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
            val run_datestr    = get_datestring();
	    val holba_diff     = get_exec_output "git diff";
	    val holba_commit   = get_exec_output "git rev-parse HEAD";
            val holba_args     = get_script_args ();
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

(* generate state from json file *)
local
  open wordsSyntax;
in
  fun parse_back_json_state isSecond filename =
    let
      fun splitandstrip f l =
            List.foldr (op@) [] (List.map ((List.map (strip_ws_off false)) o f) l);

      fun splitandparse isSecond kv =
        let
          val kvl = splitandstrip (String.tokens (fn c => c = #":")) [kv];
          val _ = if length kvl = 2 then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error kvl";
          val ks = List.nth(kvl,0);
          val vs = List.nth(kvl,1);
          val _ = if length (String.explode ks) > 2 andalso
                     List.hd (String.explode ks) = #"\"" andalso
                     List.last (String.explode ks) = #"\"" then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error ks1";
          val ks = splitandstrip (String.tokens (fn c => c = #"\"")) [ks];
          val _ = if length ks = 1 then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error ks2";
          val ks = List.hd ks;
          val _ = if List.hd (String.explode ks) = #"x" then () else
                  raise ERR "parse_back_json_state" "splitandparse:: format error ks3";
          val regnum_s = (String.implode o List.tl o String.explode) ks;
          val regnum = case Int.fromString regnum_s of
                          SOME x => x
                        | _ => raise ERR "parse_back_json_state" "cannot parse register number";
          val v = mk_wordi (Arbnum.fromString vs, 64);
          val reg_s = "R" ^ (Int.toString regnum) ^ (if isSecond then "_" else "");
        in
          (reg_s, v)
        end;

      val content = read_from_file filename;
      val content = strip_ws_off false content;
      val l = [content];

      val l = splitandstrip (String.tokens (fn c => c = #"{" orelse c = #"}")) l;
      val l = splitandstrip (String.tokens (fn c => c = #"[" orelse c = #"]")) l;
      val _ = if length l = 1 then () else
              raise ERR "parse_back_json_state" "file not formatted as expected";

      val kvs = splitandstrip (String.tokens (fn c => c = #",")) l;
    in
      List.map (splitandparse isSecond) kvs
    end;
end

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
                            if length ls < 4 then false else
                            not (is_ws (hd ls)) andalso not (is_ws (last ls))
                          end;
      val _ = if List.all is_asm_line asm_lines then () else
                raise ERR "bir_embexp_prog_to_code" "some lines are not valid asm lines"
    in
      List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines
    end;

  fun bir_embexp_code_to_prog code_asm =
    let
      val asm_lines = String.tokens (fn c => c = #"\n") code_asm;
      val asm_lines = List.map (strip_ws_off true) asm_lines;
      val asm_lines = List.filter (fn x => not (x = "")) asm_lines;
    in
      asm_lines
    end;

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
      val embexp_run_file = codepath ^ "/gen." ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = write_to_file_or_compare_clash "bir_embexp_prog_create" embexp_run_file prog_gen_id;
    in
      codehash
    end;

  fun bir_embexp_sates2_create (arch_id, exp_type_id, state_gen_id) prog_id (s1,s2) =
    let
      val exp_basedir = get_experiment_basedir arch_id;

      (* write out data *)
      val input1 = gen_json_state false s1;
      val input2 = gen_json_state false s2;
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
      val embexp_run_file = exp_datapath ^ "/gen." ^ (embexp_run_id()) ^ "." ^ (get_datestring ());
      val _ = write_to_file_or_compare_clash "bir_embexp_prog_create" embexp_run_file state_gen_id;
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

      val s = (parse_back_json_state false input1_file,
               parse_back_json_state false input2_file);
    in
      (asm_lines, s)
    end;

end

