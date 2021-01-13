structure persistenceLib :> persistenceLib =
struct

  open HolKernel Parse boolLib bossLib;

  open bir_randLib;
  open bir_miscLib;
  open bir_fileLib;
  open bir_exec_wrapLib;

  open holba_entryLib;

  open experimentsLib;

  (* error handling *)
  val libname = "persistenceLib"
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

  (* create json state *)
  fun gen_json_state mach =
      Json.serialise (machstate_to_Json mach);

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

(* interface functions *)
(* ========================================================================================= *)

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

end

