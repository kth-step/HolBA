open HolKernel boolLib Parse bossLib;

open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_bool_expTheory bir_programTheory;
open bir_exp_liftingTheory;
open bir_lifting_machinesTheory;
open bir_arm8_extrasTheory;
open bir_arm8_backlifterTheory;

(* Bridge lemmas for arm8_bir_condLib: from a lifting theorem for an
   ARMv8 state condition to the relations bir_pre_arm8_to_bir and
   bir_post_bir_to_arm8 used by get_arm8_contract_thm *)

val _ = new_theory "arm8_bir_cond";

Theorem bir_pre_arm8_to_bir_lifted:
 !P Q e.
  bir_is_bool_exp e ==>
  (!bs ms. bmr_rel arm8_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. P ms ==> Q ms) ==>
  bir_pre_arm8_to_bir P e
Proof
 rw [bir_pre_arm8_to_bir_def, bir_is_lifted_imm_exp_def] >>
 res_tac >>
 fs [bir_val_true_def, bool2b_def, bool2w_def]
QED

Theorem bir_post_bir_to_arm8_lifted:
 !P Q e ls.
  (!bs ms. bmr_rel arm8_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. Q ms ==> P ms) ==>
  bir_post_bir_to_arm8 P (\l. e) ls
Proof
 rw [bir_post_bir_to_arm8_def, bir_is_lifted_imm_exp_def] >>
 res_tac >>
 Cases_on `Q ms` >>
 fs [bir_val_true_def, bool2b_def, bool2w_def]
QED

Theorem bir_post_bir_to_arm8_lifted_PC:
 !P Q A e ls.
  (!bs ms. bmr_rel arm8_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  (!ms. ms.PC = A /\ Q ms ==> P ms) ==>
  bir_post_bir_to_arm8 P
   (\l. if l = BL_Address (Imm64 A) then e else bir_exp_false) ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 A)` >>
 fs [bir_exp_false_def, bir_eval_exp_def, bir_val_true_def] >>
 `ms.PC = A` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
 res_tac >>
 fs [bir_is_lifted_imm_exp_def] >>
 Cases_on `Q ms` >>
 fs [bool2b_def, bool2w_def]
QED

(* Postconditions by cases on the PC,
     if ms.PC = A1 then Q1 ms else ... if ms.PC = An then Qn ms else F,
   built from the last case to the first *)

Theorem bir_post_bir_to_arm8_cases_nil:
 !ls. bir_post_bir_to_arm8 (\ms. F) (\l. bir_exp_false) ls
Proof
 rw [bir_post_bir_to_arm8_def, bir_exp_false_def, bir_eval_exp_def,
     bir_val_true_def]
QED

Theorem bir_post_bir_to_arm8_cases_cons:
 !P Q R A e f ls.
  (!bs ms. bmr_rel arm8_bmr bs ms ==>
    bir_is_lifted_imm_exp bs.bst_environ e (bool2b (Q ms))) ==>
  bir_post_bir_to_arm8 R f ls ==>
  (!ms. (if ms.PC = A then Q ms else R ms) ==> P ms) ==>
  bir_post_bir_to_arm8 P
   (\l. if l = BL_Address (Imm64 A) then e else f l) ls
Proof
 rw [bir_post_bir_to_arm8_def] >>
 Cases_on `bs` >> Cases_on `b0` >> fs [] >>
 Cases_on `b.bpc_label = BL_Address (Imm64 A)` >> fs [] >| [
  `ms.PC = A` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  res_tac >>
  fs [bir_is_lifted_imm_exp_def] >>
  Cases_on `Q ms` >>
  fs [bir_val_true_def, bool2b_def, bool2w_def] >>
  METIS_TAC [],

  `ms.PC <> A` by METIS_TAC [arm8_bmr_bpc_label_PC_equiv] >>
  Q.PAT_X_ASSUM `!ms bs. _`
   (MP_TAC o Q.SPECL [`ms`, `bir_state_t b (BEnv f') b1`]) >>
  fs [] >>
  METIS_TAC []
 ]
QED

val _ = export_theory ();
