structure bir_angrLib =
struct

open HolKernel Parse Abbrev;

(* error handling *)
val libname  = "bir_angrLib"
val ERR      = Feedback.mk_HOL_ERR libname
val wrap_exn = Feedback.wrap_exn libname

(* path to fence_insertion repo
   intended usage by default is to have a symlink in the fs
*)
val fence_insertion_repo_path = "angr_platforms/bir";


val bir_program = ``BirProgram
                    [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
                     bb_statements :=
                     [BStmt_Assert
                          (BExp_Const (Imm1 abc));
                      BStmt_Assign (BVar "R3" (BType_Imm Bit64))
                                   (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                                              (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                                              Bit64);
                      BStmt_Observe 0 (BExp_Const (Imm1 1w))
                                    [BExp_BinExp BIExp_And
                                                  (BExp_Const (Imm64 0x1FC0w))
                                                  (BExp_Den (BVar "R1" (BType_Imm Bit64)))]
                                    HD];
                     bb_last_statement := BStmt_Halt (BExp_Const (Imm64 4w))|>]``;

(* some arguments ignored for now:
   maxdepth, precondition, pd, envupdate_o
*)
fun symb_exec_program maxdepth precondition program pd envupdate_o =
    let open bir_fileLib bir_exec_wrapLib;
        val bir_program_filename = get_tempfile "program" ".bir";
        val _ = write_to_file bir_program_filename (term_to_string program);
        val python_script_filename = fence_insertion_repo_path ^ "/symbolic_execution.py";
        val output = get_exec_output_list ("python3 " ^ python_script_filename ^ " " ^ bir_program_filename);
    in
      output
    end;

end
