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
            val _ = logfile_basedir_ref := SOME dir_path;
          in
            dir_path
          end
      | SOME p => p;


(* datestring helper *)
  fun get_datestring () =
    let
      val date = Date.fromTimeLocal (Time.now ());
      val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S_" date;
    in
      datestr
    end;


(* embexp run identification *)
  val embexp_run_id_ref = ref (NONE:string option);
  fun embexp_run_id () =
    case !embexp_run_id_ref of
        NONE =>
          let
            val datestr = get_datestring();
            val _ = embexp_run_id_ref := SOME datestr;
          in
            datestr
          end
      | SOME p => p;

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

(* helper functions *)
  fun get_experiment_basedir (arch_name, exp_name) =
    let
      val logfile_basedir_p = logfile_basedir()
      val _ = if not (OS.FileSys.isDir logfile_basedir_p) then
                raise ERR "logfile_basedir" ("not a directory: " ^ logfile_basedir_p)
              else
                ();
      val exp_basedir = logfile_basedir_p ^ "/" ^ arch_name ^ "/" ^ exp_name;
      val _ = makedir true exp_basedir;
    in
      exp_basedir
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
      val file = TextIO.openIn filename;
      val s    = TextIO.inputAll file before TextIO.closeIn file;
    in
      str = s
    end;

  val tempdir = "./tempdir";
  fun get_exec_output exec_cmd =
    let
      val _ = makedir true tempdir;
      val datestr = get_datestring();
      val outputfile = tempdir ^ "/exec_output_" ^ datestr ^ ".txt";

      val r = OS.Process.system (exec_cmd ^ " > " ^ outputfile);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "get_exec_output" ("the following command did not execute successfully: " ^ exec_cmd)
              else
                ();

      val file = TextIO.openIn outputfile;
      val s    = TextIO.inputAll file before TextIO.closeIn file;

      val _ = OS.Process.system ("rm " ^ outputfile);
    in
      s
    end;

  fun get_exec_python3 script argstring =
    let
      val _ = makedir true tempdir;
      val datestr = get_datestring();
      val scriptfile = tempdir ^ "/exec_script_" ^ datestr ^ ".py";
      val _ = write_to_file scriptfile script;

      val s = get_exec_output ("python3 " ^ scriptfile ^ " " ^ argstring);

      val _ = OS.Process.system ("rm " ^ scriptfile);
    in
      s
    end;

  fun get_exec_python3_argvar script arg =
    let
      val _ = makedir true tempdir;
      val datestr = get_datestring();
      val argfile = tempdir ^ "/exec_script_arg_" ^ datestr ^ ".txt";
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
  fun bir_embexp_create exp_id exp_code_asm obs_model_name (s1,s2) =
    let
      val exp_basedir = get_experiment_basedir exp_id;

      (* write out code *)
      val exp_codehash = hashstring exp_code_asm;
      val exp_codepath = exp_basedir ^ "/" ^ exp_codehash;
      (* this directory possibly already exists *)
      val _ = makedir true exp_codepath;
      (* but the code should not differ if it exists already *)
      val code_eq = write_to_file_or_compare (exp_codepath ^ "/code.asm") exp_code_asm;
      val _ = if code_eq then () else
                raise ERR "bir_embexp_create" ("there has been a hash clash with: " ^ exp_codepath);

      (* write out data *)
      val input1 = gen_json_state false s1;
      val input2 = gen_json_state true  s2;
      val exp_datahash = hashstring (input1 ^ input2);
      val exp_datapath = exp_codepath ^ "/" ^ exp_datahash;
      (* it can also happen that the same test is produced multiple times *)
      val _ = makedir true exp_datapath;
      val input1_eq = write_to_file_or_compare (exp_datapath ^ "/input1.json") input1;
      val input2_eq = write_to_file_or_compare (exp_datapath ^ "/input2.json") input2;
      val _ = if input1_eq andalso input2_eq then () else
                raise ERR "bir_embexp_create" ("there has been a hash clash with: " ^ exp_datapath);

      (* write out git commit and git diff of current directory. so this script needs to be executed from within the holbarepo! *)
      val embexp_run_id = embexp_run_id();
      val holba_diff = get_exec_output "git diff";
      val holba_commit = get_exec_output "git rev-parse HEAD";
      val holba_diff_file = exp_datapath ^ "/holba_" ^ embexp_run_id ^ ".diff";
      val holba_commit_file = exp_datapath ^ "/holba_" ^ embexp_run_id ^ ".commit";
      val holba_obsmodel_file = exp_datapath ^ "/holba_" ^ embexp_run_id ^ ".obsmodel";

      val holba_diff_eq = write_to_file_or_compare holba_diff_file holba_diff;
      val _ = if holba_diff_eq then () else
                raise ERR "bir_embexp_create" ("there has been a clash with: " ^ holba_diff_file);

      val holba_commit_eq = write_to_file_or_compare holba_commit_file holba_commit;
      val _ = if holba_commit_eq then () else
                raise ERR "bir_embexp_create" ("there has been a clash with: " ^  holba_commit_file);

      val holba_obsmodel_eq = write_to_file_or_compare holba_obsmodel_file obs_model_name;
      val _ = if holba_obsmodel_eq then () else
                raise ERR "bir_embexp_create" ("there has been a clash with: " ^ holba_obsmodel_file);
    in
      exp_datapath
    end;


  fun bir_embexp_run exp_path with_reset =
    if with_reset then (NONE, "not implemented yet") else
    let
      val r = OS.Process.system ("\"" ^ (logfile_basedir()) ^ "/scripts/run_experiment.py\" " ^
                                 "\"" ^ (embexp_basedir()) ^ "\" " ^
                                 "\"" ^ exp_path ^ "\" ");
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "bir_embexp_run" ("running the following experiment was unsuccessful: " ^ exp_path)
              else
                ();
    in
      (NONE, "no result forwarding yet")
    end;

end

