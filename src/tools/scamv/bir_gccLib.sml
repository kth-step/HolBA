structure bir_gccLib :> bir_gccLib =
struct

local
  val libname = "bir_gccLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname
in

  fun gcc_prefix () =
      case OS.Process.getEnv("HOLBA_GCC_ARM8_CROSS") of
          NONE => raise ERR "scamv_gcc_prefix" "the environment variable HOLBA_GCC_ARM8_CROSS is not set"
        | SOME p => p;


  fun writeToFile str file_name =
    let
      val outstream = TextIO.openOut file_name;
      val _ = TextIO.output (outstream, str) before TextIO.closeOut outstream;
    in
      () 
    end;

(*
val lines = ["ldr x2, [x1]"];
val tempdir = "./tempdir";
*)
  fun bir_gcc_assembe_disassemble lines tempdir =
    let
      val gcc_prefix = gcc_prefix ();

      (* if tempdir does not exist, create it *)
      val _ = (if OS.FileSys.isDir tempdir then ()
               else raise ERR "bir_gcc_assembe_disassemble" "tempdir has to be a directory"
              ) handle SysErr(_) => (OS.FileSys.mkDir tempdir);

      val path_asm_s  = tempdir ^ "/asm.s";
      val path_asm_o  = tempdir ^ "/asm.o";
      val path_asm_da = tempdir ^ "/asm.da";

      val input_code = List.foldl (fn (l,s) => s ^ "\t" ^ l ^ "\n") "\n__scamv_entry__:\n" lines;
      val _ = writeToFile input_code path_asm_s;

      val commandline = (gcc_prefix ^ "gcc -o " ^ path_asm_o ^ " -c " ^ path_asm_s ^
                         " && " ^
                         gcc_prefix ^ "objdump -d " ^ path_asm_o ^ " > " ^ path_asm_da);
      val _ = if OS.Process.isSuccess (OS.Process.system commandline) then ()
              else raise ERR "bir_gcc_assembe_disassemble" "compilation failed somehow";
    in
      path_asm_da
    end;

end (* local *)

end (* struct *)
