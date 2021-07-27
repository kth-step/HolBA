structure bir_angrLib =
struct
local

  (* error handling *)
  val libname = "bir_angrLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in
  fun get_pythondir () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_DIR")) of
          NONE => raise ERR "get_pythondir" "the environment variable HOLBA_DIR is not set"
        | SOME p => (p ^ "/src/tools/angr/python");

(*
  val bprog_t = bprog;
*)
  fun do_symb_exec bprog_t =
    let
      val pythonscript = (get_pythondir()) ^ "/symbolic_execution.py";
      val magicinputfilename = (get_pythondir()) ^ "/magicinput.bir";

      val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog_t;
      val _ = bir_fileLib.write_to_file magicinputfilename bprog_json_str;

      val output = bir_exec_wrapLib.get_exec_output ("python3 \"" ^ pythonscript ^ "\" \"" ^ magicinputfilename ^ "\"");
      val _ = print output;
    in
      ()
    end;



end (* local *)

end (* struct *)
