structure bir_gccLib :> bir_gccLib =
struct

local
  open bir_fileLib;

  val libname = "bir_gccLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname
in

  fun gcc_prefix () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_GCC_ARM8_CROSS")) of
          NONE => raise ERR "scamv_gcc_prefix" "the environment variable HOLBA_GCC_ARM8_CROSS is not set"
        | SOME p => p;


(*
val lines = "";
*)
  fun bir_gcc_assembe_disassemble input_code =
    let
      val gcc_prefix = gcc_prefix ();

      val path_asm_s  = get_simple_tempfile "asm.s";
      val path_asm_o  = get_simple_tempfile "asm.o";
      val path_asm_bin = get_simple_tempfile "asm";
      val path_asm_da = get_simple_tempfile "asm.da";

      val _ = write_to_file path_asm_s input_code;

      val commandline = (gcc_prefix ^ "gcc -o " ^ path_asm_o ^ " -c " ^ path_asm_s ^
                         " && " ^
			 gcc_prefix ^ "gcc -Wl,--entry=0x400000 -nostartfiles " ^ path_asm_o ^ " -o " ^ path_asm_bin ^
                         " && " ^
                         gcc_prefix ^ "objdump -d " ^ path_asm_bin ^ " > " ^ path_asm_da);
      val _ = if OS.Process.isSuccess (OS.Process.system commandline) then ()
              else raise ERR "bir_gcc_assembe_disassemble" "compilation failed somehow";
    in
      path_asm_da
    end;

end (* local *)

end (* struct *)
