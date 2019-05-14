open HolKernel Parse boolLib bossLib;
open tutorial_liftTheory;
open tutorialWPLib;

val _ = new_theory "tutorial_wp";

(* Test: Finding SQRT function: *)
val sqrt_prog_def = Define `sqrt_prog = BirProgram ([ <|bb_label :=
           BL_Address_HC (Imm64 3548w) "F9401FF8 (ldr x24, [sp, #56])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R24" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 56w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 3552w)))|>])`;


(* add that the SP is higher that program code and smaller than max stack. Both to precondition and invariant *)
``bir_sqrt_entry_contract =
bir_triple sqrt_prog (BL_Address (Imm64 0x854w))
 {(BL_Address (Imm64 0x890w))}
 (BExp_Const (Imm1 1w))
 b_sqrt_I
 ``;

``bir_sqrt_loop_inv_contract =
bir_triple sqrt_prog (BL_Address (Imm64 0x890w))
 {(BL_Address (Imm64 0x890w))}
 (BExp_BinExp BIExp_And (b_sqrt_I)
  (BExp_Den (BVar "ProcState_C" BType_Bool))
 )
 b_sqrt_I
 ``;

``bir_sqrt_loop_exit_contract =
bir_triple sqrt_prog (BL_Address (Imm64 0x890w))
 {(BL_Address (Imm64 0x894w))}
 (BExp_BinExp BIExp_And (b_sqrt_I)
  (BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ProcState_C" BType_Bool))
 ))
 (BExp_BinExp BIExp_And (b_sqrt_I)
  (BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ProcState_C" BType_Bool))
 ))
 ``;

val _ = export_theory();
