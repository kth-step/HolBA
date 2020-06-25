structure bir_exec_wrapLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "bir_exec_wrapLib"
  val wrap_exn = Feedback.wrap_exn "bir_exec_wrapLib"

  open bir_fileLib;

in

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

end (* local *)
end (* struct *)
