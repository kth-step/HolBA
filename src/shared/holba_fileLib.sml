structure holba_fileLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "holba_fileLib"
  val wrap_exn = Feedback.wrap_exn "holba_fileLib"

  open holba_miscLib;

in

  fun read_file_lines file_name = let
    val instream = TextIO.openIn file_name
    fun read_it acc =
      case TextIO.inputLine instream of
          NONE => List.rev acc
        | SOME s => read_it (s::acc);
    val input = read_it [] before TextIO.closeIn instream
  in input end;

(* file read/write helpers *)
  fun read_from_file_bytes filename bytes =
    let
      val file = TextIO.openIn filename;
      val s    = TextIO.inputN (file, bytes);
    in
      s
    end;

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
      val _    = TextIO.output (file, str) before TextIO.closeOut file;
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
  val tempdir = "./tempdir";
  fun get_simple_tempfile filename =
    let
      val _ = makedir true tempdir;
      val tempfile = tempdir ^ "/" ^ filename;
    in
      tempfile
    end;

  fun seedgen_linux_random () =
    let
      val randpath = "/dev/random";
      val s = read_from_file_bytes randpath 5;
      val cs = String.explode s;
      val li_256 = LargeInt.fromInt 256;
      (* val c = hd cs;
         val x = LargeInt.fromInt 2 *)
      fun add_char (c, x) = LargeInt.+ (LargeInt.* (x, li_256), LargeInt.fromInt (Char.ord c));
      val largeint = List.foldl add_char (LargeInt.fromInt 0) cs;
    in
      Real.fromLargeInt largeint
    end;

  val tempfile_randgen = Random.newgenseed (seedgen_linux_random ()); (*Random.newgen ();*)
  fun get_tempfile_randstr () =
    Int.toString (Random.range (100000,999999) tempfile_randgen);

  fun get_tempfile prefix suffix =
    let
      val datestr = get_datestring();
      val randstr = get_tempfile_randstr();
    in
      get_simple_tempfile (prefix ^ "_" ^ datestr ^ "_" ^ randstr ^ "_" ^ suffix)
    end;

end (* local *)
end (* struct *)
