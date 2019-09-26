structure bir_scamv_helpersLib =
struct

local

  open HolKernel boolLib liteLib simpLib Parse bossLib;

(* error handling *)
  val libname = "bir_scamv_helpersLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in


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
  fun get_simple_tempfile filename =
    let
      val _ = makedir true tempdir;
      val tempfile = tempdir ^ "/" ^ filename;
    in
      tempfile
    end;

  fun get_tempfile prefix suffix =
    let
      val datestr = get_datestring();
    in
      get_simple_tempfile (prefix ^ "_" ^ datestr ^ "_" ^ suffix)
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


(*
val s = ""
*)
  fun strip_ws_off accept_empty_string s =
    let
      fun is_ws x = x = #" " orelse x = #"\t" orelse x = #"\n";
      fun find_first_idx p l = List.foldl (fn ((idx,x),r) => if r >= 0 then r else if p x then idx else r)
                                          (~1)
                                          (snd (List.foldr (fn (x,(i,l)) => (i-1,(i,x)::l)) ((List.length l) - 1, []) l));

      val l = String.explode s;
      val first_c = find_first_idx (not o is_ws) l;
      val last_c = (List.length l) - 1 - (find_first_idx (not o is_ws) (List.rev l));
    in
      if first_c < 0 then
        if accept_empty_string then "" else raise ERR "strip_ws_off" "here we don't accept empty assembly lines"
      else
        String.extract (String.substring (s, 0, last_c + 1), first_c, NONE)
    end;

end (* local *)

end
