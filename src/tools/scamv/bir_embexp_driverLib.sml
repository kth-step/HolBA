structure bir_embexp_driverLib :> bir_embexp_driverLib =
struct

  open HolKernel Parse boolLib bossLib;


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


(* datestring helper *)
  fun get_datestring () =
    let
      val date = Date.fromTimeLocal (Time.now ());
      val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
    in
      datestr
    end;

(* directory creation helper *)
  fun makedir makepath path =
    let
      val r = OS.Process.system ("mkdir " ^ (if makepath then "-p " else "") ^ path);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "makedir" ("couldn't create the following directory: " ^ path)
              else
                ();
    in
      ()
    end;

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

(* file read/write helpers *)
  fun read_from_file filename =
    let
      val file = TextIO.openIn filename;
      val s    = TextIO.inputAll file before TextIO.closeIn file;
    in
      s
    end;

  fun read_from_file_lines filename =
    let
      val file = TextIO.openIn filename;
      fun allLinesRevFun acc = case TextIO.inputLine file of
			    NONE => acc
			  | SOME l => allLinesRevFun (l::acc);
      val lines = List.rev (allLinesRevFun []) before TextIO.closeIn file;
    in
      lines
    end;

  fun write_to_file filename str =
    let
      val file = TextIO.openOut (filename);
      val _    = TextIO.output (file, str);
      val _    = TextIO.closeOut file;
    in
      ()
    end;
  fun write_to_file_or_compare filename str =
    let
      val _ = OS.FileSys.isDir filename
                handle SysErr _ => (write_to_file filename str; false);
      val s = read_from_file filename;
    in
      str = s
    end;
  fun write_to_file_or_compare_clash clash_id filename str =
    let
      val eq = write_to_file_or_compare filename str;
      val _ = if eq then () else
                raise ERR ("write_to_file_or_compare_clash___" ^ clash_id) ("there has been a clash with: " ^ filename);
    in
      ()
    end;

(* helper functions *)
  val tempdir = "./tempdir";
  fun get_tempfile prefix suffix =
    let
      val _ = makedir true tempdir;
      val datestr = get_datestring();
      val tempfile = tempdir ^ "/" ^ prefix ^ "_" ^ datestr ^ "_" ^ suffix;
    in
      tempfile
    end;

  fun get_exec_output_gen do_print exec_cmd =
    let
      val outputfile = get_tempfile "exec_output" ".txt";

      val r = OS.Process.system (exec_cmd ^ " > " ^ outputfile);
      val _ = if not do_print then () else
                print (read_from_file outputfile);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "get_exec_output" ("the following command did not execute successfully: " ^ exec_cmd)
              else
                ();

      val s = read_from_file outputfile;

      val _ = OS.Process.system ("rm " ^ outputfile);
    in
      s
    end;

  fun get_exec_output exec_cmd = get_exec_output_gen false exec_cmd;

  fun get_exec_output_list exec_cmd =
    let
      val outputfile = get_tempfile "exec_output_list" ".txt";

      val output = get_exec_output exec_cmd;
      val _ = write_to_file outputfile output;

      val lines = read_from_file_lines outputfile;

      val _ = OS.Process.system ("rm " ^ outputfile);
    in
      lines
    end;

  fun get_exec_python3 script argstring =
    let
      val scriptfile = get_tempfile "exec_script" ".py";
      val _ = write_to_file scriptfile script;

      val s = get_exec_output ("python3 " ^ scriptfile ^ " " ^ argstring);

      val _ = OS.Process.system ("rm " ^ scriptfile);
    in
      s
    end;

  fun get_exec_python3_argvar script arg =
    let
      val argfile = get_tempfile "exec_script_arg" ".txt";
      val _ = write_to_file argfile arg;

      val script_argread = "import sys\nwith open(sys.argv[1],'r') as f:\n\targvar = f.read()\n" ^ "\n" ^ script;
      val s = get_exec_python3 script_argread argfile;

      val _ = OS.Process.system ("rm " ^ argfile);
    in
      s
    end;

  fun hashstring str =
    let
      val pyhashprep = "import hashlib\nsha = hashlib.sha1()\nsha.update(argvar.encode('utf-8'))\n";
      val pyprint = "print(sha.hexdigest(), end='')";
    in
      get_exec_python3_argvar (pyhashprep ^ pyprint) str
    end;

(* embexp run identification *)
  val embexp_run_id_ref = ref (NONE:string option);
  fun embexp_run_id () =
    case !embexp_run_id_ref of
        NONE =>
          let
            val logfile_basedir_p = logfile_basedir()
	    val holbaruns_basedir = logfile_basedir_p ^ "/holbaruns";
	    val _ = makedir true holbaruns_basedir;

            (* write out git commit and git diff of current directory. *)
            (*    so this script needs to be executed from within the holbarepo! *)
            val run_datestr = get_datestring();
	    val holba_diff = get_exec_output "git diff";
	    val holba_commit = get_exec_output "git rev-parse HEAD";

	    val holba_hash = hashstring (run_datestr ^ holba_diff ^ holba_commit);
	    val runitpath = holbaruns_basedir ^ "/" ^ holba_hash;
	    (* this directory should not exist, but possibly already exists *)
	    val _ = makedir true runitpath;

	    val run_datestr_file = runitpath ^ "/holba.time";
	    val holba_diff_file = runitpath ^ "/holba.diff";
	    val holba_commit_file = runitpath ^ "/holba.commit";

	    val _ = write_to_file_or_compare_clash "embexp_run_id" run_datestr_file run_datestr;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_diff_file holba_diff;
	    val _ = write_to_file_or_compare_clash "embexp_run_id" holba_commit_file holba_commit;

            val _ = embexp_run_id_ref := SOME holba_hash;
          in
            holba_hash
          end
      | SOME p => p;


(* create json state *)
  fun gen_json_state isSecond s =
    let
      fun kv_to_json (k,v) =
        let
          val _ = if String.isPrefix "R" k then () else
                    raise ERR "gen_json_state" "input not as exptected";
          val _ = if isSecond = String.isSuffix "_" k then () else
                    raise ERR "gen_json_state" "input not as exptected _";
          val k = if isSecond then
                    (String.extract(k, 0, SOME((String.size k) - 1)))
                  else k;

          val regname = "x" ^ (String.extract(k, 1, NONE));
        in
          "\n\t\"" ^ regname ^ "\": " ^ (Arbnumcore.toString v)
        end;
      val s_jsonmappings = List.map kv_to_json s;

      val str = List.foldr (fn (m, str) => m ^ "," ^ str) "" s_jsonmappings;
    in
      "{" ^ (String.extract(str, 0, SOME((String.size str) - 1))) ^ "\n}"
    end;

(* interface functions *)
(* ========================================================================================= *)
  fun bir_embexp_prog_to_code asm_lines =
    List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines;

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

      (* write out gen info *)
      val embexp_run_file = codepath ^ "/" ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = write_to_file_or_compare_clash "bir_embexp_prog_create" embexp_run_file prog_gen_id;
    in
      codehash
    end;

  fun bir_embexp_sates2_create (arch_id, exp_type_id, state_gen_id) prog_id (s1,s2) =
    let
      val exp_basedir = get_experiment_basedir arch_id;

      (* write out data *)
      val input1 = gen_json_state false s1;
      val input2 = gen_json_state true  s2;
      val exp_datahash = hashstring (prog_id ^ input1 ^ input2);
      val exp_id = "exps2/" ^ exp_type_id ^ "/" ^ exp_datahash;
      val exp_datapath = exp_basedir ^ "/" ^ exp_id;
      (* it can also happen that the same test is produced multiple times *)
      val _ = makedir true exp_datapath;
      val _ = write_to_file_or_compare_clash "bir_embexp_sates2_create" (exp_datapath ^ "/input1.json") input1;
      val _ = write_to_file_or_compare_clash "bir_embexp_sates2_create" (exp_datapath ^ "/input2.json") input2;

      (* write out reference to the code (hash of the code) *)
      val prog_id_file = exp_datapath ^ "/code.hash";
      val _ = write_to_file_or_compare_clash "bir_embexp_sates2_create" prog_id_file prog_id;

      (* write out gen info *)
      val embexp_run_file = exp_datapath ^ "/" ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = write_to_file_or_compare_clash "bir_embexp_prog_create" embexp_run_file state_gen_id;
    in
      arch_id ^ "/" ^ exp_id
    end;


  fun bir_embexp_run exp_id with_reset =
    if with_reset then (NONE, "not implemented yet") else
    let
      val cmdline = ("\"" ^ (logfile_basedir()) ^ "/scripts/run_experiment.py\" " ^
                     "\"" ^ (embexp_basedir()) ^ "\" " ^
                     exp_id);
      val lines = get_exec_output_list cmdline;
      val lastline = List.nth(lines, (List.length lines) - 1);
      val result = if lastline = "result = true\n" then
                     (SOME true, "the result is based on the python experiment runner script output")
                   else if lastline = "result = false\n" then
                     (SOME false, "the result is based on the python experiment runner script output")
                   else
                     raise ERR "bir_embexp_run" ("the last line of the python experiment runner is unexpected: " ^ lastline)
    in
      result
    end;

end

