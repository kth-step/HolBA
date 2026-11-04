open HolKernel boolLib Parse bossLib;

open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_bool_expTheory bir_programTheory;
open bir_exp_liftingTheory;
open bir_lifting_machinesTheory;
open bir_riscv_extrasTheory;
open bir_riscv_backlifterTheory;

(* Bridge lemmas for riscv_bir_condLib: from a lifting theorem for an
   RISC-V state condition to the relations bir_pre_riscv_to_bir and
   bir_post_bir_to_riscv used by get_riscv_contract_thm *)

val _ = new_theory "riscv_bir_cond";

Theorem bir_pre_riscv_to_bir_lifted:
 !P Q e.
  bir_is_bool_exp e ==>
  (!bs ms. bmr_rel riscv_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. P ms ==> Q ms) ==>
  bir_pre_riscv_to_bir P e
Proof
 rw [bir_pre_riscv_to_bir_def, bir_is_lifted_imm_exp_def] >>
 res_tac >>
 fs [bir_val_true_def, bool2b_def, bool2w_def]
QED

Theorem bir_post_bir_to_riscv_lifted:
 !P Q e ls.
  (!bs ms. bmr_rel riscv_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. Q ms ==> P ms) ==>
  bir_post_bir_to_riscv P (\l. e) ls
Proof
 rw [bir_post_bir_to_riscv_def, bir_is_lifted_imm_exp_def] >>
 res_tac >>
 Cases_on `Q ms` >>
 fs [bir_val_true_def, bool2b_def, bool2w_def]
QED

Theorem bir_post_bir_to_riscv_lifted_PC:
 !P Q A e ls.
  (!bs ms. bmr_rel riscv_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. ms.c_PC ms.procID = A /\ Q ms ==> P ms) ==>
  bir_post_bir_to_riscv P
   (\l. if l = BL_Address (Imm64 A) then e else bir_exp_false) ls
Proof
 rw [bir_post_bir_to_riscv_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 A)` >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def] >>
 `ms.c_PC ms.procID = A` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
 res_tac >>
 fs [bir_is_lifted_imm_exp_def] >>
 Cases_on `Q ms` >>
 fs [bool2b_def, bool2w_def]
QED

(* Postconditions by cases on the PC,
     if ms.c_PC ms.procID = A1 then Q1 ms
     else ... if ms.c_PC ms.procID = An then Qn ms else F,
   built from the last case to the first *)

Theorem bir_post_bir_to_riscv_cases_nil:
 !ls. bir_post_bir_to_riscv (\ms. F) (\l. bir_exp_false) ls
Proof
 rw [bir_post_bir_to_riscv_def, bir_exp_false_def, bir_eval_exp_def,
     bir_val_true_def]
QED

Theorem bir_post_bir_to_riscv_cases_cons:
 !P Q R A e f ls.
  (!bs ms. bmr_rel riscv_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  bir_post_bir_to_riscv R f ls ==>
  (!ms. (if ms.c_PC ms.procID = A then Q ms else R ms) ==> P ms) ==>
  bir_post_bir_to_riscv P
   (\l. if l = BL_Address (Imm64 A) then e else f l) ls
Proof
 rw [bir_post_bir_to_riscv_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 A)` >> fs [] >| [
  `ms.c_PC ms.procID = A` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
  res_tac >>
  fs [bir_is_lifted_imm_exp_def] >>
  Cases_on `Q ms` >>
  fs [bir_val_true_def, bool2b_def, bool2w_def] >>
  METIS_TAC [],

  `ms.c_PC ms.procID <> A` by METIS_TAC [riscv_bmr_bpc_label_c_PC_equiv] >>
  Q.PAT_X_ASSUM `!ms bs. _`
   (MP_TAC o Q.SPECL [`ms`, `bir_state_t b (BEnv f') b1`]) >>
  fs [] >>
  METIS_TAC []
 ]
QED

val _ = export_theory ();
