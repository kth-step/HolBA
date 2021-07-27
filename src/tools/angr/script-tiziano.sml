

val bprog = “BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 (0w :word64)) "D10043FF (sub sp, sp, #0x10)";
         bb_statements :=
           [(BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (16w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>]”;


(*
val _ = bir_angrLib.do_symb_exec bprog;
*)


val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog;
val _ = print bprog_json_str;

