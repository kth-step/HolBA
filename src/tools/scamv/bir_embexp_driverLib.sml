structure bir_embexp_driverLib :> bir_embexp_driverLib =
struct

  open HolKernel Parse boolLib bossLib;

  open bir_scamv_helpersLib;

(* error handling *)
  val libname = "bir_embexp_driverLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname



(* directory variables handling *)
  fun embexp_basedir_read () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv ("HOLBA_EMBEXP_DIR")) of
          NONE => raise ERR "embexp_basedir" "the environment variable HOLBA_EMBEXP_DIR is not set"
        | SOME p => p;

  val embexp_basedir_ref = ref (NONE:string option);
  fun embexp_basedir () =
    case !embexp_basedir_ref of
        NONE =>
          let
            val dir_path = embexp_basedir_read();
            val _ = embexp_basedir_ref := SOME dir_path;
          in
            dir_path
          end
      | SOME p => p;

  fun logfile_basedir_read () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv ("HOLBA_EMBEXP_LOGS")) of
          NONE => raise ERR "logfile_basedir" "the environment variable HOLBA_EMBEXP_LOGS is not set"
        | SOME p => p;

  val logfile_basedir_ref = ref (NONE:string option);
  fun logfile_basedir () =
    case !logfile_basedir_ref of
        NONE =>
          let
            val dir_path = logfile_basedir_read();
            val _ = if not (OS.FileSys.isDir dir_path) then
                      raise ERR "logfile_basedir" ("not a directory: " ^ dir_path)
                    else
                      ();
            val _ = logfile_basedir_ref := SOME dir_path;
          in
            dir_path
          end
      | SOME p => p;

(* log dir helper functions *)
  fun get_progs_basedir arch_name =
    let
      val logfile_basedir_p = logfile_basedir()
      val progs_basedir = logfile_basedir_p ^ "/" ^ arch_name ^ "/progs";
      val _ = makedir true progs_basedir;
    in
      progs_basedir
    end;

  fun get_experiment_basedir arch_name =
    let
      val logfile_basedir_p = logfile_basedir()
      val exp_basedir = logfile_basedir_p ^ "/" ^ arch_name;
      val _ = makedir true exp_basedir;
    in
      exp_basedir
    end;

(* logging *)
  val holbarun_log = ref (NONE:TextIO.outstream option);
  val prog_log = ref (NONE:TextIO.outstream option);
  val exp_log = ref (NONE:TextIO.outstream option);
  fun get_log_out (log, fun_name, err_msg) =
    case !log of
        NONE => raise ERR fun_name err_msg
      | SOME log_out => log_out;

  fun close_log log =
    case !log of
        NONE => ()
      | SOME log_out => TextIO.closeOut log_out;

  fun create_log log filename = (
    (close_log log);
    let val log_out = TextIO.openOut filename
    in log := SOME log_out
    end);

  fun write_log_line log_t line =
    let
      val log_out = get_log_out log_t;
      val _ = TextIO.output (log_out, line);
      val _ = TextIO.output (log_out, "\n");
    in
      TextIO.flushOut log_out
    end;

  fun bir_embexp_log_prog_close () =
    close_log prog_log;

  fun bir_embexp_log_exp_close () =
    close_log exp_log;

  fun bir_embexp_log_prog message =
    let
      val line = message;
    in
      write_log_line (prog_log, "bir_embexp_log_prog", "no program log registered currently") line
    end;

  fun bir_embexp_log_exp message =
    let
      val line = message;
    in
      write_log_line (exp_log, "bir_embexp_log_exp", "no experiment log registered currently") line
    end;

  fun bir_embexp_log_raw message =
    let
      val line = message;
    in
      write_log_line (holbarun_log, "bir_embexp_log", "no holbarun log registered currently (this should never happen)") line
    end;


(* embexp run identification *)
  val embexp_run_id_ref = ref (NONE:string option);
  val embexp_run_timer_ref = ref (NONE:Time.time option);
  fun embexp_run_id () =
    case !embexp_run_id_ref of
        NONE =>
          let
            val logfile_basedir_p = logfile_basedir()
	    val holbaruns_basedir = logfile_basedir_p ^ "/holbaruns";
	    val _ = makedir true holbaruns_basedir;

            (* write out git commit and git diff of current directory. *)
            (*    so this script needs to be executed from within the holbarepo! *)
            val run_datestr    = get_datestring();
	    val holba_diff     = get_exec_output "git diff";
	    val holba_commit   = get_exec_output "git rev-parse HEAD";
            val holba_args     = get_script_args ();
            val rand_seed      = rand_seed_get ();
            val holba_randseed = Real.toString rand_seed;

	    val holba_hash = hashstring (run_datestr ^
                                         holba_diff ^
                                         holba_commit ^
                                         holba_args ^
                                         holba_randseed);
	    val runitpath = holbaruns_basedir ^ "/" ^ holba_hash;
	    (* this directory should not exist, but possibly already exists *)
	    val _ = makedir true runitpath;

	    val run_datestr_file    = runitpath ^ "/holba.time";
	    val holba_diff_file     = runitpath ^ "/holba.diff";
	    val holba_commit_file   = runitpath ^ "/holba.commit";
	    val holba_args_file     = runitpath ^ "/holba.args";
	    val holba_randseed_file = runitpath ^ "/holba.randseed";

	    val _ = write_to_file_or_compare_clash "embexp_run_id" run_datestr_file    run_datestr;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_diff_file     holba_diff;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_commit_file   holba_commit;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_args_file     holba_args;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_randseed_file holba_randseed;

	    val holba_logfile = runitpath ^ "/holba.log";
            val _ = create_log holbarun_log holba_logfile;
            val _ = write_log_line (holbarun_log, "embexp_run_id", "no no no") ("Starting log for: " ^ holba_hash);

            val _ = embexp_run_timer_ref := timer_start 1;
            val _ = embexp_run_id_ref := SOME holba_hash;
          in
            holba_hash
          end
      | SOME p => p;

  fun bir_embexp_log message =
    let
      val _ = embexp_run_id ();
      val _ = bir_embexp_log_raw message;
    in
      ()
    end;

  fun bir_embexp_finalize () =
    let
      val _ = embexp_run_id ();
      val _ = timer_stop (fn d_time =>
               bir_embexp_log_raw ("\n\n======================================\n" ^
                                   "Experiment generation duration: " ^ d_time)
              ) (!embexp_run_timer_ref);

      val _ = embexp_run_id_ref := NONE;
      val _ = embexp_run_timer_ref := NONE;
    in
      close_log holbarun_log
    end;

  (* machine state definition from the signature *)
  datatype machineState = MACHSTATE of (((string, num) Redblackmap.dict) * (int * ((num, num) Redblackmap.dict)));
  val machstate_empty = MACHSTATE ((Redblackmap.mkDict String.compare), (8, Redblackmap.mkDict Arbnum.compare));

  fun machstate_print (MACHSTATE (regmap, (wsz, memmap))) =
      let
	  val _ = print ("State is =  ");
	  val _ = print ("(mem, ");
	  val _ = List.map (fn x =>  print ("("^(Arbnum.toString(#1 x))^","^(Arbnum.toString(#2 x))^")"))
                           (Redblackmap.listItems memmap);
	  val _ = print "), ";
	  val _ = List.map (fn (n,v) => print ("(" ^ n ^ ", " ^(Arbnum.toString( v))^ ")"))
                           (Redblackmap.listItems regmap);
	  val _ = print "\n";
      in () end;

  fun machstate_add_reg (rn, rv) (MACHSTATE (rm, m)) =
    (MACHSTATE (Redblackmap.insert (rm, rn, rv), m));
  fun machstate_replace_mem newm (MACHSTATE (rm, m)) =
    (MACHSTATE (rm, newm));

  (* create json state *)
  fun gen_json_state (MACHSTATE (regmap, (wsz, memmap))) =
    let
      val _ = if wsz = 8 then () else
              raise ERR "gen_json_state" "word size has to be one byte";

      fun rkv_to_json (k,v) =
        let
          (* TODO: Stack pointer needs to be handled *)
          (* TODO: maybe want to check that we indeed get R0-R29 or whatever *) 
          val _ = if String.isPrefix "R" k then () else
                    raise ERR "gen_json_state" "input not as exptected";

          val regname = "x" ^ (String.extract(k, 1, NONE));
        in
          "\n\t\"" ^ regname ^ "\": \"0x" ^ (Arbnumcore.toHexString v) ^ "\""
        end;

      fun mkv_to_json m =
        let
          fun memConcat l = if List.null l then "" else
                            foldr (fn (a,b) => a^",\n"^b) (hd l) (tl l);

          val mname = "mem";
          fun mentry_to_json entr =
                "\t\t" ^
                "\"0x"^(Arbnumcore.toHexString (fst entr)) ^ "\"" ^
		" : \"0x" ^ (Arbnumcore.toHexString (snd entr)) ^ "\"";
	  val mappings = List.map mentry_to_json (Redblackmap.listItems m);

          val m_tm = memConcat mappings;
        in
          "\n\t\"" ^ mname ^ "\": " ^ "{\n" ^ m_tm ^ "\n\t}"
        end;

      val s_jsonmappings_reg = List.map rkv_to_json (Redblackmap.listItems regmap);
      val s_jsonmappings_mem = mkv_to_json memmap
      val s_jsonmappings = s_jsonmappings_reg@[s_jsonmappings_mem]

      val str = List.foldr (fn (m, str) => m ^ "," ^ str) "" s_jsonmappings
    in
      "{" ^ (String.extract(str, 0, SOME((String.size str) - 1))) ^ "\n}"
    end;

(* generate state from json file *)
local
  open wordsSyntax;
in
  fun parse_back_json_state filename =
    let
      fun unpackOne c1 c2 s =
        let
          val s_ = strip_ws_off false s;

          val s_l = String.explode s_;
          val _ = if length s_l > 1 then () else
                  raise ERR "parse_back_json_state::unpackOne" "string is too short";

          val c_fst = hd   s_l;
          val c_snd = last s_l;

          val _ = if c1 = c_fst andalso c2 = c_snd then () else
                  raise ERR "parse_back_json_state::unpackOne" "chars not matching";
(*
          val l = String.tokens (fn c => c = c1 orelse c = c2) s_;
          val _ = if length l = 1 then () else
                  raise ERR "parse_back_json_state::unpackOne" "cannot unpack simply";
*)
        in
          String.implode (List.take (tl s_l, (length s_l) - 2))
        end;

      (* TODO: did I place the unpacking op for quotes correctly? *)
      fun parseReg name vs =
        let
          val _ = if List.hd (String.explode name) = #"x" then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error, expect register name";
          val regnum_s = (String.implode o List.tl o String.explode) name;
          val regnum = case Int.fromString regnum_s of
                          SOME x => x
                        | _ => raise ERR "parse_back_json_state" "cannot parse register number";
          val v = Arbnum.fromHexString (unpackOne #"\"" #"\"" vs);
          val reg_s = "R" ^ (Int.toString regnum);
        in
          (reg_s, v)
        end;

      (* TODO: did I place the unpacking op for quotes correctly? *)
      fun parseMem name vs =
        let
          val _ = if name = "mem" then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error, expect memory name";

          val mapping_raw = String.tokens (fn c => c = #",") (unpackOne #"{" #"}" vs);
          fun map_s_to_kv s =
            let
              val kvl = String.tokens (fn c => c = #":") s;
              val _ = if length kvl = 2 then () else
                      raise ERR "parse_back_json_state" "error parsing memory mapping";
              val ks = unpackOne #"\"" #"\"" (strip_ws_off false (hd kvl));
              val vs = unpackOne #"\"" #"\"" (strip_ws_off false (hd (tl kvl)));
            in
              (Arbnum.fromHexString ks, Arbnum.fromHexString vs)
            end;
          val kvmap = Redblackmap.fromList Arbnum.compare (List.map map_s_to_kv mapping_raw);
        in
          (8, kvmap)
        end;

      fun splitandparse ((ks,vs), (st_regmap, st_memmap_o)) =
        let
          val _ = if length (String.explode ks) > 2 andalso
                     List.hd (String.explode ks) = #"\"" andalso
                     List.last (String.explode ks) = #"\"" then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error string quote";
          val name = unpackOne #"\"" #"\"" ks;
        in
          if name = "mem" then
            if not (isSome st_memmap_o) then
              (st_regmap, SOME (parseMem name vs))
            else
              raise ERR "parse_back_json_state" "splitandparse:: can only handle one memory"
          else
            ((parseReg name vs)::st_regmap, st_memmap_o)
        end;

      val content = read_from_file filename;

      val toplevel = strip_ws_off false (unpackOne #"{" #"}" content);

      val (p_s,p_acc,p_l) = List.foldl (fn (c, (s, acc, l)) =>
        case s of
           0 => (case c of
                    #"," => (s, [], acc::l)
                  | #"{" => (1, c::acc, l)
                  | #"}" => raise ERR "parse_back_json_state::parseentries" "aaa 1"
                  | _    => (s, c::acc, l))
         | 1 => (case c of
                    #"{" => raise ERR "parse_back_json_state::parseentries" "aaa 2"
                  | #"}" => (0, c::acc, l)
                  | _    => (s, c::acc, l))
         | _ => raise ERR "parse_back_json_state::parseentries" "impossible state")
       (0, [], [])
       (String.explode toplevel);

      val mapslist_ = if p_s = 0 andalso List.null p_acc then p_l else
                      if p_s = 0 then p_acc::p_l else
                      raise ERR "parse_back_json_state" "parser state is unexpected";

      fun splitfirstchar c s =
        let
          val l = String.explode (strip_ws_off false s);
          fun firstchar [] _ = raise ERR "parse_back_json_state" "mapsplit error"
            | firstchar (c_::l_) acc =
                if c_ = c then (List.rev acc, l_)
                else firstchar l_ (c_::acc);

          val (l1,l2) = firstchar l [];
        in
          ((strip_ws_off false o String.implode) l1, (strip_ws_off false o String.implode) l2)
        end;

      val mapslist = List.map ((splitfirstchar #":") o String.implode o List.rev)  mapslist_;

(*
      val (ks,vs) = hd mapslist;
      val (ks,vs) = hd (tl mapslist);
*)
      val (st_regmap, st_memmap_o) = List.foldl splitandparse ([], NONE) mapslist

      val regmap = Redblackmap.fromList String.compare (List.rev st_regmap);
      val mem = if isSome st_memmap_o then
                  valOf st_memmap_o
                else
                  (8, Redblackmap.mkDict Arbnum.compare);
    in
      MACHSTATE (regmap, mem)
    end;
end;

(* interface functions *)
(* ========================================================================================= *)
  (* platform parameters *)
  val bir_embexp_params_code   = Arbnum.fromHexString    "0x2000";
  val bir_embexp_params_memory = (Arbnum.fromHexString "0x100000",
                                  Arbnum.fromHexString  "0x40000");

  fun bir_embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);

  fun bir_embexp_prog_to_code asm_lines =
    let
      fun is_colon x = x = #":";
      fun is_ws x = x = #" " orelse x = #"\t" orelse x = #"\n";
      fun is_asm_line l = let val ls = String.explode l in
                            if List.exists is_colon ls then false else
                            if length ls < 1 then false else
                            not (is_ws (hd ls)) andalso not (is_ws (last ls))
                          end;
      val _ = if List.all is_asm_line asm_lines then () else
                raise ERR "bir_embexp_prog_to_code" "some lines are not valid asm lines"
    in
      List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines
    end;

  fun bir_embexp_prog_std_preproc asm_lines =
    let
(*
      val asm_lines = if List.last asm_lines = "\n" then
                        List.take (asm_lines, (length asm_lines) - 1)
                      else
                        raise ERR "bir_embexp_prog_std_preproc" "no final newline";
*)
      val asm_lines = List.map (fn line =>
         let val fixedline = strip_ws_off true line; in
           if line = "\t" ^ fixedline then
             fixedline
           else
             raise ERR "bir_embexp_prog_std_preproc" "lines are not as expected"
         end
       ) asm_lines;
    in
      asm_lines
    end;

  fun bir_embexp_prog_cleanup asm_lines =
    let
      val asm_lines = List.map (strip_ws_off true) asm_lines;
      val asm_lines = List.filter (fn x => not (x = "")) asm_lines;
    in
      asm_lines
    end;

  fun bir_embexp_code_to_prog_raw preproc_fun code_asm =
    let
      val asm_lines = String.tokens (fn c => c = #"\n") code_asm;
      val asm_lines = preproc_fun asm_lines;

      val asm_lines_p = List.exists (fn x =>
            x <> (strip_ws_off true x) orelse
            x = ""
        ) asm_lines;
      val _ = if not asm_lines_p then () else
              raise ERR "bir_embexp_code_to_prog_raw" "unexpected asm formatting";
    in
      asm_lines
    end;
  
  fun bir_embexp_code_to_prog code_asm =
    bir_embexp_code_to_prog_raw bir_embexp_prog_cleanup code_asm;

  fun bir_embexp_prog_create (arch_id, prog_gen_id) code_asm =
    let
      val progs_basedir = get_progs_basedir arch_id;

      (* write out code *)
      val codehash = hashstring code_asm;
      val codepath = progs_basedir ^ "/" ^ codehash;
      (* this directory possibly already exists *)
      val _ = makedir true codepath;
      (* but the code should not differ if it exists already *)
      val _ = write_to_file_or_compare_clash "bir_embexp_prog_create" (codepath ^ "/code.asm") code_asm;

      (* create prog log *)
      val embexp_gen_file = codepath ^ "/gen." ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = create_log prog_log embexp_gen_file;
      (* log generator info *)
      val _ = write_log_line (prog_log, "bir_embexp_prog_create", "no no no") prog_gen_id;
    in
      codehash
    end;

  fun bir_embexp_states2_create (arch_id, exp_type_id, state_gen_id) prog_id (s1,s2,straino) =
    let
      val exp_basedir = get_experiment_basedir arch_id;

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
      val _ = write_to_file_or_compare_clash "bir_embexp_states2_create" prog_id_file prog_id;

      (* write the json files after reference to code per convention *)
      (* - to indicate that experiment writing is complete *)
      val input1_file = exp_datapath ^ "/input1.json";
      val input2_file = exp_datapath ^ "/input2.json";
      val train_file  = exp_datapath ^ "/train.json";

      val _ = write_to_file_or_compare_clash "bir_embexp_states2_create" input1_file input1;
      val _ = write_to_file_or_compare_clash "bir_embexp_states2_create" input2_file input2;
      val _ = if not (isSome traino) then () else
               write_to_file_or_compare_clash "bir_embexp_states2_create" train_file (valOf traino);

      (* create exp log, if there was no clash before! *)
      val embexp_gen_file = exp_datapath ^ "/gen." ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = create_log exp_log embexp_gen_file;
      (* log generator info *)
      val _ = write_log_line (exp_log, "bir_embexp_states2_create", "no no no") state_gen_id;
    in
      arch_id ^ "/" ^ exp_id
    end;

  fun bir_embexp_run exp_id with_reset =
    let
      val cmdline = ("\"" ^ (logfile_basedir()) ^ "/scripts/run_experiment.py\" " ^
                     (if with_reset then "--conn_mode reset " else "--conn_mode try ") ^
                     exp_id);
      val _ = print ("===>>> RUNNING EXPERIMENT: " ^ exp_id ^ "\n")
      val lines = get_exec_output_list cmdline;
      val lastline = List.nth(lines, (List.length lines) - 1);
      val result = if lastline = "result = true\n" then
                     (SOME true, "the result is based on the python experiment runner script output")
                   else if lastline = "result = false\n" then
                     (SOME false, "the result is based on the python experiment runner script output")
                   else if String.isPrefix "result = " lastline then
                     (NONE, "BOARD EXCEPTION /\\/\\/\\/\\/\\/ " ^ (strip_ws_off true lastline))
                   else
                     raise ERR "bir_embexp_run" ("the last line of the python experiment runner is unexpected: " ^ lastline)
    in
      result
    end;


  fun bir_embexp_load_prog_file code_file =
    bir_embexp_code_to_prog (read_from_file code_file);


  fun bir_embexp_load_prog arch_id prog_id =
    let
      val logs_dir = logfile_basedir();
      val code_file = (logs_dir ^ "/" ^ arch_id ^ "/progs/" ^ prog_id ^ "/code.asm");
    in
      bir_embexp_load_prog_file code_file
    end;


  fun bir_embexp_load_exp exp_id =
    let
      val logs_dir = logfile_basedir();

      val prog_id = read_from_file (logs_dir ^ "/" ^ exp_id ^ "/code.hash");
      val code_file = (logs_dir ^ "/" ^ exp_id ^ "/../../../progs/" ^ prog_id ^ "/code.asm");
      val asm_lines = bir_embexp_load_prog_file code_file;

      val input1_file = (logs_dir ^ "/" ^ exp_id ^ "/input1.json");
      val input2_file = (logs_dir ^ "/" ^ exp_id ^ "/input2.json");

      val train_file = (logs_dir ^ "/" ^ exp_id ^ "/train.json");
      val train_filename = (read_from_file train_file; SOME train_file)
                           handle _ => NONE;

      val s1 = parse_back_json_state input1_file;
      val s2 = parse_back_json_state input2_file;

      val traino = Option.map (fn filename => parse_back_json_state filename) train_filename;
    in
      (asm_lines, (s1, s2, traino))
    end;

  fun bir_embexp_load_list listtype listname =
    let
      val logs_dir = logfile_basedir();
      val contents = read_from_file (logs_dir ^ "/lists/" ^ listtype ^ "_" ^ listname ^ ".txt");
      val list_lines = String.tokens (fn c => c = #"\n") contents;
      val nonempty = List.filter (fn x => x <> "") list_lines;
      val actual_entries = List.filter (not o (String.isPrefix "#")) nonempty;
    in
      actual_entries
    end;

  fun bir_embexp_create_list_open listtype listname =
    let
      val logs_dir = logfile_basedir();
      val filename = logs_dir ^ "/lists/" ^ listtype ^ "_" ^ listname ^ ".txt";
    in
      TextIO.openOut filename
    end;

  fun bir_embexp_load_progs listname =
    let
      val logs_dir = logfile_basedir();
      val archprog_ids = bir_embexp_load_list "progs" listname;
      val progs = List.map (fn apid =>
            (bir_embexp_code_to_prog_raw bir_embexp_prog_std_preproc)
               (read_from_file (logs_dir ^ "/" ^ apid ^ "/code.asm"))
          ) archprog_ids;
    in
      progs
    end;

  fun bir_embexp_load_exp_ids listname =
    bir_embexp_load_list "exps" listname;

end

