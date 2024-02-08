open HolKernel boolLib Parse bossLib;

open BasicProvers simpLib metisLib;

open logrootTheory arithmeticTheory pairTheory combinTheory wordsTheory;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open isqrtTheory;

val _ = new_theory "isqrt_prop";

val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_isqrt_prog``;

(el 1)blocks;
(el 2)blocks;

bir_isqrt_riscv_lift_THM;

Definition SQRT_def:
 SQRT x = ROOT 2 x
End

val arith_ss = srw_ss() ++ numSimps.old_ARITH_ss;

Theorem sqrt_thm:
!x p. SQRT x = let q = p * p in
      if (q <= x /\ x < q + 2 * p + 1) then p else SQRT x
Proof
RW_TAC (arith_ss ++ boolSimps.LET_ss) [SQRT_def] THEN
  MATCH_MP_TAC ROOT_UNIQUE THEN
  RW_TAC bool_ss [ADD1,EXP_ADD,EXP_1,DECIDE ``2 = SUC 1``,
    LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
  DECIDE_TAC
QED

Definition wSQRT_def:
 wSQRT w = n2w (SQRT (w2n w))
End

Definition isqrt_spec_def:
 isqrt_spec_def ms = 
 let input = ms.c_gpr ms.procID 0w in
 ms with c_gpr := 
  (\x y. if x = ms.procID /\ y = 0w then (wSQRT input) else ms.c_gpr x y)
End

(* run symbolic execution of BIR to get two symbolic states  *)
(* connect this back to the riscv state via the lifting theorem *)

val _ = export_theory ();
