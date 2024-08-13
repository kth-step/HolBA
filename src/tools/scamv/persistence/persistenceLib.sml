structure persistenceLib :> persistenceLib =
struct

  open HolKernel Parse boolLib bossLib;

  open bir_randLib;
  open holba_miscLib;

  open holba_entryLib;

  open experimentsLib;
  open embexp_logsLib;

  (* error handling *)
  val libname = "persistenceLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  (* disable this for less outputs to the database *)
  val enable_log_outputs = true;


  (* creation of a holba run with metadata and containers for programs and experiments *)
  (* ========================================================================================= *)
  datatype holba_run_refs = RunReferences of (run_handle * string * prog_list_handle * exp_list_handle);
  fun get_dotfree_time () =
    let
      val now      = Time.now ();
      val now_ms   = LargeInt.mod (Time.toMilliseconds now, LargeInt.fromInt 1000)
      val now_ms_str = StringCvt.padLeft #"0" 3 (LargeInt.fmt StringCvt.DEC now_ms);
      val now_date = Date.fromTimeLocal now;
      val now_str  = (Date.fmt "%Y-%m-%d_%H-%M-%S" now_date) ^ "_" ^ now_ms_str;

     (* assert no dots in name *)
      val _ = if not (List.exists (fn x => x = #".") (String.explode now_str)) then () else
              raise ERR "get_dotfree_time" "should never happen, found a dot in the generated name";
    in
     (* time = time without dot *)
      now_str
    end;
  fun holba_run_create descr_o =
    let
      val name      = get_dotfree_time ();

      val list_descr = Option.getOpt(Option.map (fn s => SOME ("HolBA run: " ^ s)) descr_o, SOME "auto-generated");

      val list_v  = LogsList ("HOLBA." ^ name, list_descr);
      val prog_l_id = create_prog_list list_v;
      val exp_l_id  = create_exp_list  list_v;

      val run_v     = LogsRun (name, prog_l_id, exp_l_id);
      val run_id    = create_run run_v;

      (* prepare metadata for run *)
         (* write out git commit and git diff of current directory. *)
         (*    so this code needs to be executed with the working directory in the holbarepo! *)
      open holba_exec_wrapLib;
      val run_datestr     = get_datestring();
      val holba_diff      = get_exec_output "git diff";
      val holba_commit    = get_exec_output "git rev-parse HEAD";
      val holba_args      = get_script_args ();
      val rand_seed       = rand_seed_get ();
      val holba_randseed  = Real.toString rand_seed;
      val holba_run_descr =
        if isSome descr_o then
          ("SOME (" ^ (valOf descr_o) ^ ")")
        else
          "NONE";

      val run_metadata =
        [("time",      run_datestr),
         ("diff",      holba_diff),
         ("commit",    holba_commit),
         ("args",      holba_args),
         ("randseed",  holba_randseed),
         ("run_descr", holba_run_descr)];

      (* add metadata *)
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_run_meta_handle (run_id, SOME m_n, "")) (SOME m_v)) run_metadata;
    in
      RunReferences (run_id, name, prog_l_id, exp_l_id)
    end;

  (* logging of holba run data and run context management *)
  (* ========================================================================================= *)
  val holbarun_log = ref (NONE:meta_handle option);
  val prog_log     = ref (NONE:meta_handle option);
  val exp_log      = ref (NONE:meta_handle option);
  fun get_log_out (log, fun_name, err_msg) =
    case !log of
        NONE => raise ERR fun_name err_msg
      | SOME log_out => log_out;

  fun close_log log         = log := NONE;
  fun create_log log_id =
    if not enable_log_outputs then NONE else
    let
      val _ = init_meta log_id (SOME "");
    in SOME log_id end;

  fun set_log log log_id_o = log := log_id_o;

  fun write_log_line log_t line =
    if not enable_log_outputs then () else
    let
      val log_id = get_log_out log_t;
      val _ = append_meta log_id (line ^ "\n");
    in () end;

  fun run_log_prog message =
    let
      val line = message;
    in
      write_log_line (prog_log, "run_log_prog", "no program log registered currently") line
    end;

  fun run_log_exp message =
    let
      val line = message;
    in
      write_log_line (exp_log, "run_log_exp", "no experiment log registered currently") line
    end;

  fun run_log_raw message =
    let
      val line = message;
    in
      write_log_line (holbarun_log, "run_log", "no holbarun log registered currently (this should never happen)") line
    end;

  (* embexp run references (database handles and special name string) *)
  val holba_run_id_ref     = ref (NONE:holba_run_refs option);
  val holba_run_timer_ref  = ref (NONE:Time.time option);
  val holba_run_prog_l_idx = ref 0;
  val holba_run_exp_l_idx  = ref 0;
  val holba_run_prog_map   = ref (Redblackmap.mkDict prog_handle_compare);
  val holba_run_exp_map    = ref (Redblackmap.mkDict exp_handle_compare );
  fun holba_run_id_create descr_o =
    let
      val run_refs = holba_run_create descr_o;
      val RunReferences (run_id, run_name, _, _) = run_refs;

      val _ = set_log holbarun_log (create_log (mk_run_meta_handle (run_id, SOME "log", "")));
      val _ = write_log_line (holbarun_log, "holba_run_id", "no no no") ("Starting log for: " ^ run_name);

      val _ = holba_run_timer_ref := timer_start 1;
      val _ = holba_run_id_ref := SOME run_refs;

      val _ = holba_run_prog_l_idx := 0;
      val _ = holba_run_exp_l_idx  := 0;
      val _ = holba_run_prog_map   := Redblackmap.mkDict prog_handle_compare;
      val _ = holba_run_exp_map    := Redblackmap.mkDict exp_handle_compare;
    in
      run_refs
    end;

  fun holba_run_id () =
    case !holba_run_id_ref of
        NONE => holba_run_id_create NONE
      | SOME p => p;

  fun run_log message =
    let
      val _ = holba_run_id ();
      val _ = run_log_raw message;
      val _ = print message;
    in
      ()
    end;

  fun run_finalize () =
    let
      val _ = holba_run_id ();
      val gen_run_final_msg = ref "";
      val _ = timer_stop (fn d_time =>
               gen_run_final_msg := (
                "\n\n======================================\n" ^
                "HolBA run persistence context finalized. Duration: " ^ d_time)
              ) (!holba_run_timer_ref);
      val _ = print ((!gen_run_final_msg) ^ "\n");
      val _ = run_log_raw (!gen_run_final_msg);

      val _ = holba_run_id_ref := NONE;
      val _ = holba_run_timer_ref := NONE;
    in
      close_log holbarun_log
    end;

  local
    open Redblackmap;
  in
    fun refdict_ld_gen_upd refd k genf i =
      let
        val d = !refd;
        val v =
          case peek(d, k) of
             SOME x => x
           | NONE => (let val v_ = genf i in (refd := insert(d, k, v_)); v_ end);
      in v end;

    fun gen_progexp_st (idx_ref, log_id) =
      (((idx_ref := !idx_ref + 1); !idx_ref),
       (create_log log_id));
  end;

  fun run_init descr_o =
    ((if isSome (!holba_run_id_ref) then run_finalize () else ());
     holba_run_id_create descr_o;
     ());

  fun timer_stop_gen f NONE = raise ERR "timer_stop_gen" "this should not happen"
    | timer_stop_gen f (SOME tm) = let
       val d_time = Time.- (Time.now(), tm);
       in f ((Time.toString d_time) ^ "s") end;
  fun time_since_run_str () = timer_stop_gen (fn x => x) (!holba_run_timer_ref);

  (* storing to logs *)
  (* ========================================================================================= *)
  fun run_create_prog arch prog run_metadata =
    let
      val arch_id = exp_arch_to_string arch;

      val RunReferences (_, run_name, prog_l_id, _) = holba_run_id();

      val asm_code = prog_to_asm_code prog;
      val prog_v   = LogsProg (arch_id, asm_code);
      val prog_id  = create_prog prog_v;

      val meta_name_log = "gen." ^ run_name;
      val (list_index, log) =
        refdict_ld_gen_upd
          holba_run_prog_map
          prog_id
          gen_progexp_st
          (holba_run_prog_l_idx, mk_prog_meta_handle (prog_id, SOME "log", meta_name_log));

      (* add entry to prog list *)
      val _ = add_to_prog_list (prog_l_id, prog_id, list_index);
      (* set prog log *)
      val _ = set_log prog_log log;

      (* add metadata *)
      val meta_name = meta_name_log ^ "." ^ (get_dotfree_time ());
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_prog_meta_handle (prog_id, SOME m_n, meta_name)) (SOME m_v)) run_metadata;

    in
      prog_id
    end;

  fun run_create_exp prog_id exp_type exp_params state_list run_metadata =
    let
      val exp_type_s = exp_type_to_string exp_type;

      val RunReferences (_, run_name, _, exp_l_id) = holba_run_id();
      val run_metadata_ = ("creationtime", time_since_run_str ())::run_metadata;

      val input_data = Json.OBJECT (List.map (fn (n, s) => ("input_" ^ n, machstate_to_Json s)) state_list);
      val exp_v      = LogsExp (prog_id, exp_type_s, exp_params, input_data);
      val exp_id     = create_exp exp_v;

      val meta_name_log = "gen." ^ run_name;
      val (list_index, log) =
        refdict_ld_gen_upd
          holba_run_exp_map
          exp_id
          gen_progexp_st
          (holba_run_exp_l_idx, mk_exp_meta_handle (exp_id, SOME "log", meta_name_log));

      (* add entry to exp list *)
      val _ = add_to_exp_list (exp_l_id, exp_id, !holba_run_exp_l_idx);
      (* set exp log *)
      val _ = set_log exp_log log;

      (* add metadata *)
      val meta_name = meta_name_log ^ "." ^ (get_dotfree_time ());
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_exp_meta_handle (exp_id, SOME m_n, meta_name)) (SOME m_v)) run_metadata_;
    in
      exp_id
    end;


  (* retrieving from logs *)
  (* ========================================================================================= *)
  fun runlogs_load_progs listname =
    let
      val prog_l_ids = query_all_prog_lists ();
      val prog_ls = get_prog_lists prog_l_ids;

      val (_, prog_ls_) = List.foldl (fn (x, (i, l)) => (i+1, ((i, x))::l)) (0, []) prog_ls;
      val prog_ls_filt = List.filter (fn (_, LogsList (n, _)) => n = listname) prog_ls_;
      val (i, _) = if List.length prog_ls_filt = 1 then hd prog_ls_filt else
                    raise ERR "runlogs_load_progs" ("didn't find exactly one match for prog list " ^ listname);
      val prog_l_id = List.nth (prog_l_ids, i);

      val progs_i = List.map snd (get_prog_list_entries_full prog_l_id);

      val progs = List.map (fn (LogsProg (_,code)) => prog_from_asm_code code) progs_i;
    in
      progs
    end;

end

