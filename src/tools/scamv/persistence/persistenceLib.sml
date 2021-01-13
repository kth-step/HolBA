structure persistenceLib :> persistenceLib =
struct

  open HolKernel Parse boolLib bossLib;

  open bir_randLib;
  open bir_miscLib;

  open holba_entryLib;

  open experimentsLib;
  open embexp_logsLib;

  (* error handling *)
  val libname = "persistenceLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

(*
TODO: remove this

logfile_basedir
get_progs_basedir
get_experiment_basedir
*)

  (* creation of a holba run with metadata and containers for programs and experiments *)
  (* ========================================================================================= *)
  datatype holba_run_refs = RunReferences of (run_handle * string * prog_list_handle * exp_list_handle);
  fun holba_run_create () =
    let
      val name      = get_datestring(); (* TODO: this should be changed and fixed *)

      val list_v  = LogsList ("HOLBA." ^ name, SOME "auto-generated");
      val prog_l_id = create_prog_list list_v;
      val exp_l_id  = create_exp_list  list_v;

      val run_v     = LogsRun (name, prog_l_id, exp_l_id);
      val run_id    = create_run run_v;

      (* TODO: add more metadata *)
      (*
            (* write out git commit and git diff of current directory. *)
            (*    so this script needs to be executed from within the holbarepo! *)
            val run_datestr    = get_datestring();
	    val holba_diff     = get_exec_output "git diff";
	    val holba_commit   = get_exec_output "git rev-parse HEAD";
            val holba_args     = get_script_args ();
            val rand_seed      = rand_seed_get ();
            val holba_randseed = Real.toString rand_seed;

	    val run_datestr_file    = runitpath ^ "/holba.time";
	    val holba_diff_file     = runitpath ^ "/holba.diff";
	    val holba_commit_file   = runitpath ^ "/holba.commit";
	    val holba_args_file     = runitpath ^ "/holba.args";
	    val holba_randseed_file = runitpath ^ "/holba.randseed";

	    val _ = write_to_file_or_compare_clash "holba_run_id" run_datestr_file    run_datestr;
	    val _ = write_to_file_or_compare_clash "holba_run_id" holba_diff_file     holba_diff;
	    val _ = write_to_file_or_compare_clash "holba_run_id" holba_commit_file   holba_commit;
	    val _ = write_to_file_or_compare_clash "holba_run_id" holba_args_file     holba_args;
	    val _ = write_to_file_or_compare_clash "holba_run_id" holba_randseed_file holba_randseed;
      *)
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
  fun create_log log log_id =
    let
      val _ = init_meta log_id (SOME "");
      val _ = log := SOME log_id;
    in () end;

  fun write_log_line log_t line =
    let
      val log_id = get_log_out log_t;
      val _ = append_meta log_id (line ^ "\n");
    in () end;

  fun run_log_prog_close () =
    close_log prog_log;

  fun run_log_exp_close () =
    close_log exp_log;

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

  (* embexp run references (database handles and special string) *)
  val holba_run_id_ref    = ref (NONE:holba_run_refs option);
  val holba_run_timer_ref = ref (NONE:Time.time option);
  fun holba_run_id () =
    case !holba_run_id_ref of
        NONE =>
          let
            val run_refs = holba_run_create ();
            val RunReferences (run_id, run_name, _, _) = run_refs;

            val _ = create_log holbarun_log (mk_run_meta_handle (run_id, SOME "", "log"));
            val _ = write_log_line (holbarun_log, "holba_run_id", "no no no") ("Starting log for: " ^ run_name);

            val _ = holba_run_timer_ref := timer_start 1;
            val _ = holba_run_id_ref := SOME run_refs;
          in
            run_refs
          end
      | SOME p => p;

  fun run_log message =
    let
      val _ = holba_run_id ();
      val _ = run_log_raw message;
    in
      ()
    end;

  fun run_finalize () =
    let
      val _ = holba_run_id ();
      val _ = timer_stop (fn d_time =>
               run_log_raw ("\n\n======================================\n" ^
                                   "Experiment generation duration: " ^ d_time)
              ) (!holba_run_timer_ref);

      val _ = holba_run_id_ref := NONE;
      val _ = holba_run_timer_ref := NONE;
    in
      close_log holbarun_log
    end;


  (* storing to logs *)
  (* ========================================================================================= *)

  (* TODO change architecture directly to function in experimentsLib *)
  fun run_create_prog (ArchARM8, prog_gen_id) code_asm =
    let
      val arch_id = "arm8";

      val RunReferences (_, run_name, prog_l_id, _) = holba_run_id();

      val code_asm = code_asm; (* TODO: this should be a program value type, something new in experimentsLib *)
      val prog_v   = LogsProg (arch_id, code_asm);
      val prog_id  = create_prog prog_v;
      val _        = add_to_prog_list (prog_l_id, prog_id);

(* TODO: solve problem if program with same code already exists! same for experiment!! prog is already in the list and a gen log already exists, probably same for metadata! *)
(*
   TODO: add metadata

      (* write out code *)
      val codehash = hashstring code_asm;
      val codepath = progs_basedir ^ "/" ^ codehash;
      (* this directory possibly already exists *)
      val _ = makedir true codepath;
      (* but the code should not differ if it exists already *)
      val _ = write_to_file_or_compare_clash "run_prog_create" (codepath ^ "/code.asm") code_asm;
*)

      (* create prog log *)
      val log_id = "gen." ^ run_name ^ "." ^ (get_datestring ()); (* TODO: does this name format look good and stay separable? *)
      val _ = create_log prog_log (mk_prog_meta_handle (prog_id, SOME log_id, "log"));
      (* log generator info *)
      val _ = write_log_line (prog_log, "run_prog_create", "no no no") prog_gen_id;
    in
      prog_id
    end;

  fun run_create_states2 (exp_type_id, state_gen_id) prog_id (s1,s2,straino) =
    let
      val RunReferences (_, run_name, _, exp_l_id) = holba_run_id();

  (* TODO: generalize inputs somehow, for the whole function, so that it's not fixed to 2.5 states *)
      val input_data = Json.OBJECT (
        [("input_1", machstate_to_Json s1),
         ("input_2", machstate_to_Json s2)]@(
            if isSome straino then
              [("input_train", machstate_to_Json (valOf straino))]
            else
              []));
      val exp_v      = LogsExp (prog_id, "exps2", exp_type_id, input_data);
      val exp_id     = create_exp exp_v;
      val _          = add_to_exp_list (exp_l_id, exp_id);

(* TODO: solve problem if exp with same code already exists! same for prog!! prog is already in the list and a gen log already exists, probably same for metadata! *)
(*
   TODO: add metadata

      (* write out data *)
      val input1 = gen_json_state s1;
      val input2 = gen_json_state s2;
      val traino = Option.map gen_json_state straino;

      val exp_datahash = hashstring (prog_id ^ input1 ^ input2);
      val exp_id = "exps2/" ^ exp_type_id ^ "/" ^ exp_datahash;
      val exp_datapath = exp_basedir ^ "/" ^ exp_id;
      (* btw, it can also happen that the same test is produced multiple times *)
      (* create directory if it didn't exist yet *)
      val _ = makedir true exp_datapath;

      (* write out reference to the code (hash of the code) *)
      val prog_id_file = exp_datapath ^ "/code.hash";
      val _ = write_to_file_or_compare_clash "run_states2_create" prog_id_file prog_id;

      (* write the json files after reference to code per convention *)
      (* - to indicate that experiment writing is complete *)
      val input1_file = exp_datapath ^ "/input1.json";
      val input2_file = exp_datapath ^ "/input2.json";
      val train_file  = exp_datapath ^ "/train.json";

      val _ = write_to_file_or_compare_clash "run_states2_create" input1_file input1;
      val _ = write_to_file_or_compare_clash "run_states2_create" input2_file input2;
      val _ = if not (isSome traino) then () else
               write_to_file_or_compare_clash "run_states2_create" train_file (valOf traino);
*)

      (* create exp log *)
      val log_id = "gen." ^ run_name ^ "." ^ (get_datestring ()); (* TODO: does this name format look good and stay separable? *)
      val _ = create_log exp_log (mk_exp_meta_handle (exp_id, SOME log_id, "log"));

      (* log generator info *)
      val _ = write_log_line (exp_log, "run_states2_create", "no no no") state_gen_id;
    in
      exp_id
    end;


  (* retrieving from logs *)
  (* ========================================================================================= *)
(*
  fun run_load_list listtype listname =
    let
      val logs_dir = logfile_basedir();
      val contents = read_from_file (logs_dir ^ "/lists/" ^ listtype ^ "_" ^ listname ^ ".txt");
      val list_lines = String.tokens (fn c => c = #"\n") contents;
      val nonempty = List.filter (fn x => x <> "") list_lines;
      val actual_entries = List.filter (not o (String.isPrefix "#")) nonempty;
    in
      actual_entries
    end;
*)

(* TODO: implement *)

  fun run_load_progs listname =
    let
(*
      val logs_dir = logfile_basedir();
      val archprog_ids = run_load_list "progs" listname;
      val progs = List.map (fn apid =>
            (run_code_to_prog_raw run_prog_std_preproc)
               (read_from_file (logs_dir ^ "/" ^ apid ^ "/code.asm"))
          ) archprog_ids;
*)
    in
      (*progs*)[]
    end;

(*
  (* misc *)
  (* ========================================================================================= *)
  (* generate state from json file *)
  fun parse_back_json_state filename =
    let
      val content = read_from_file filename;
      val json_obj =
        case Json.parse content of
           Json.ERROR e => raise ERR "parse_back_json_state" ("error parsing the json string: " ^ e)
         | Json.OK json => json;
    in
      Json_to_machstate json_obj
    end;
*)

end

