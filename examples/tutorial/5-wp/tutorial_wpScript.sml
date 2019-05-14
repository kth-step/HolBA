open HolKernel Parse boolLib bossLib;
open tutorial_liftTheory;
open examplesBinaryLib;

val _ = new_theory "tutorial_wp";

val sqrt_prog_def =
  Define `sqrt_prog = ^sqrt_prog_tm`;

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
