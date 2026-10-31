open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open wordsTheory;

open holba_auxiliaryLib;

open add_regTheory;
open add_reg_spec_arm8Theory;
open add_reg_spec_birTheory;
open add_reg_symb_transfTheory;

val _ = new_theory "add_reg_prop";

(* -------------------------------- *)
(* Backlifting BIR contract to ARMv8 *)
(* -------------------------------- *)

(* contracts 1 and 3 also list the loop exit as ending label,
   which is never reached first, for composition *)

val arm8_cont_add_reg_1_thm =
 get_arm8_contract_thm
  bspec_cont_add_reg_1 add_reg_init_addr_1_def [add_reg_end_addr_1_def, add_reg_end_addr_def]
  bir_add_reg_progbin_def
  arm8_add_reg_pre_1_def arm8_add_reg_post_1_def
  bir_add_reg_prog_def
  [bspec_add_reg_pre_1_def]
  bspec_add_reg_pre_1_def add_reg_arm8_pre_1_imp_bspec_pre_1_thm
  [bspec_add_reg_post_1_def] add_reg_arm8_post_1_imp_bspec_post_1_thm
  bir_add_reg_arm8_lift_THM;

Theorem arm8_cont_add_reg_1:
 arm8_cont bir_add_reg_progbin add_reg_init_addr_1 {add_reg_end_addr_1; add_reg_end_addr}
  (arm8_add_reg_pre_1 pre_x2 pre_x3)
  (arm8_add_reg_post_1 pre_x2 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_add_reg_1_thm
QED

val arm8_cont_add_reg_2_thm =
 get_arm8_contract_thm
  bspec_cont_add_reg_2 add_reg_init_addr_2_def [add_reg_end_addr_2_loop_def, add_reg_end_addr_2_ret_def]
  bir_add_reg_progbin_def
  arm8_add_reg_pre_2_def arm8_add_reg_post_2_def
  bir_add_reg_prog_def
  [bspec_add_reg_pre_2_def]
  bspec_add_reg_pre_2_def add_reg_arm8_pre_2_imp_bspec_pre_2_thm
  [bspec_add_reg_post_2_loop_def,bspec_add_reg_post_2_ret_def] add_reg_arm8_post_2_imp_bspec_post_2_thm
  bir_add_reg_arm8_lift_THM;

Theorem arm8_cont_add_reg_2:
 arm8_cont bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr_2_loop; add_reg_end_addr_2_ret}
  (arm8_add_reg_pre_2 pre_x2 pre_x3)
  (arm8_add_reg_post_2 pre_x2 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_add_reg_2_thm
QED

val arm8_cont_add_reg_3_thm =
 get_arm8_contract_thm
  bspec_cont_add_reg_3 add_reg_init_addr_3_def [add_reg_end_addr_3_def, add_reg_end_addr_def]
  bir_add_reg_progbin_def
  arm8_add_reg_pre_3_def arm8_add_reg_post_3_def
  bir_add_reg_prog_def
  [bspec_add_reg_pre_3_def]
  bspec_add_reg_pre_3_def add_reg_arm8_pre_3_imp_bspec_pre_3_thm
  [bspec_add_reg_post_3_def] add_reg_arm8_post_3_imp_bspec_post_3_thm
  bir_add_reg_arm8_lift_THM;

Theorem arm8_cont_add_reg_3:
 arm8_cont bir_add_reg_progbin add_reg_init_addr_3 {add_reg_end_addr_3; add_reg_end_addr}
  (arm8_add_reg_pre_3 pre_x2 pre_x3)
  (arm8_add_reg_post_3 pre_x2 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_add_reg_3_thm
QED

(* ------------------------------ *)
(* Whole program contract          *)
(* ------------------------------ *)

(* The loop head is add_reg_init_addr_2 and the loop exit
   add_reg_end_addr. Since the piece contracts cannot state that
   execution does not return to their own start label, iterations are
   expressed as avoidance contracts (arm8_cont_avoid), which only
   require that the loop exit is not encountered on the way back to
   the loop head. *)

val addr_defs = [
 add_reg_init_addr_def,
 add_reg_init_addr_1_def, add_reg_end_addr_1_def,
 add_reg_init_addr_2_def, add_reg_end_addr_2_loop_def, add_reg_end_addr_2_ret_def,
 add_reg_init_addr_3_def, add_reg_end_addr_3_def,
 add_reg_end_addr_def];

(* Some addresses have several names, e.g., add_reg_end_addr_1 and
   add_reg_init_addr_2. To use a theorem whose address names differ
   from those of the goal, unfold both. *)
fun addr_irule thm =
 REWRITE_TAC addr_defs >> irule (REWRITE_RULE addr_defs thm);

(* signed decrement of a positive value stays nonnegative
   and decreases the unsigned value (a - 1w, as normalised by rw) *)
Theorem add_reg_dec[local]:
 !a:word64. 0w < a ==> 0w <= a + -1w /\ w2n (a + -1w) < w2n a
Proof
 rw [GSYM WORD_LO] >> blastLib.FULL_BBLAST_TAC
QED

Theorem add_reg_zero[local]:
 !a:word64. 0w <= a ==> ~(0w < a) ==> a = 0w
Proof
 blastLib.BBLAST_TAC
QED

Theorem arm8_cont_add_reg_1_avoid:
 arm8_cont_avoid bir_add_reg_progbin add_reg_init_addr_1 {add_reg_end_addr}
  (arm8_add_reg_pre_1 pre_x2 pre_x3)
  (arm8_add_reg_post_1 pre_x2 pre_x3)
Proof
 QINST_IRULE [("ls", `{add_reg_end_addr_1}`)] arm8_cont_avoid_intro >>
 conj_tac >- rw (arm8_add_reg_post_1_def :: addr_defs) >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 ACCEPT_TAC arm8_cont_add_reg_1
QED

Theorem arm8_cont_add_reg_3_avoid:
 arm8_cont_avoid bir_add_reg_progbin add_reg_init_addr_3 {add_reg_end_addr}
  (arm8_add_reg_pre_3 pre_x2 pre_x3)
  (arm8_add_reg_post_3 pre_x2 pre_x3)
Proof
 QINST_IRULE [("ls", `{add_reg_end_addr_3}`)] arm8_cont_avoid_intro >>
 conj_tac >- rw (arm8_add_reg_post_3_def :: addr_defs) >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 ACCEPT_TAC arm8_cont_add_reg_3
QED

(* loop branch when the loop condition holds *)
Theorem arm8_cont_add_reg_2_loop_avoid:
 0w < pre_x2 ==>
 arm8_cont_avoid bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr_2_ret}
  (arm8_add_reg_pre_2 pre_x2 pre_x3)
  (\ms. ms.PC = add_reg_end_addr_2_loop /\ arm8_add_reg_post_2_loop pre_x2 pre_x3 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls", `{add_reg_end_addr_2_loop}`)] arm8_cont_avoid_intro >>
 conj_tac >- simp addr_defs >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 QINST_IRULE [("pre1", `arm8_add_reg_pre_2 pre_x2 pre_x3`),
  ("post1", `arm8_add_reg_post_2 pre_x2 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.PC = add_reg_end_addr_2_loop` >>
  fs ([arm8_add_reg_post_2_def, arm8_add_reg_post_2_ret_def] @ addr_defs) >>
  METIS_TAC [WORD_NOT_LESS]
 ) >>
 ACCEPT_TAC arm8_cont_add_reg_2
QED

(* loop branch when the loop condition does not hold *)
Theorem arm8_cont_add_reg_2_exit:
 pre_x2 <= 0w ==>
 arm8_cont bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr_2_ret}
  (arm8_add_reg_pre_2 pre_x2 pre_x3)
  (\ms. ms.PC = add_reg_end_addr_2_ret /\ arm8_add_reg_post_2_ret pre_x2 pre_x3 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls2", `{add_reg_end_addr_2_loop}`)] arm8_cont_subset_rule >>
 conj_tac >- simp addr_defs >>
 `{add_reg_end_addr_2_ret} UNION {add_reg_end_addr_2_loop} =
  {add_reg_end_addr_2_loop; add_reg_end_addr_2_ret}`
  by (rw [EXTENSION] >> METIS_TAC []) >>
 pop_assum (fn thm => REWRITE_TAC [thm]) >>
 QINST_IRULE [("pre1", `arm8_add_reg_pre_2 pre_x2 pre_x3`),
  ("post1", `arm8_add_reg_post_2 pre_x2 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.PC = add_reg_end_addr_2_loop` >>
  fs ([arm8_add_reg_post_2_def, arm8_add_reg_post_2_loop_def] @ addr_defs) >>
  METIS_TAC [WORD_NOT_LESS]
 ) >>
 ACCEPT_TAC arm8_cont_add_reg_2
QED

(* before loop: establish the loop invariant *)
Theorem arm8_cont_add_reg_before_loop:
 arm8_cont_avoid bir_add_reg_progbin add_reg_init_addr {add_reg_end_addr}
  (arm8_add_reg_pre pre_x pre_y)
  (\ms. ms.PC = add_reg_init_addr_2 /\ arm8_add_reg_inv pre_x pre_y ms)
Proof
 Cases_on `0w <= pre_x` >- (
  QINST_IRULE [("pre1", `arm8_add_reg_pre_1 pre_x pre_y`),
  ("post1", `arm8_add_reg_post_1 pre_x pre_y`)] arm8_cont_avoid_conseq_rule >>
  rpt conj_tac >- rw [arm8_add_reg_pre_def, arm8_add_reg_pre_1_def] >- (
   rw ([arm8_add_reg_post_1_def, arm8_add_reg_inv_def] @ addr_defs)
  ) >>
  addr_irule arm8_cont_add_reg_1_avoid
 ) >>
 rw [arm8_cont_avoid_def, arm8_add_reg_pre_def, WORD_GREATER_EQ]
QED

(* one loop iteration: loop branch followed by loop body back to the head *)
Theorem arm8_cont_add_reg_iter:
 !x. arm8_cont_avoid bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr}
  (\ms. arm8_add_reg_inv pre_x pre_y ms /\ arm8_add_reg_cond ms /\
        arm8_add_reg_variant ms = x)
  (\ms. ms.PC = add_reg_init_addr_2 /\ arm8_add_reg_inv pre_x pre_y ms /\
        arm8_add_reg_variant ms < x)
Proof
 gen_tac >>
 QINST_IRULE [("pre1", `\ms. ?a b. ms.REG 2w = a /\ ms.REG 3w = b /\
     a + b = pre_x + pre_y /\ 0w < a /\ w2n a = x`),
  ("post1", `\ms. ms.PC = add_reg_init_addr_2 /\ arm8_add_reg_inv pre_x pre_y ms /\
     arm8_add_reg_variant ms < x`)] arm8_cont_avoid_conseq_rule >>
 rpt conj_tac >- (
  rw [arm8_add_reg_inv_def, arm8_add_reg_cond_def, arm8_add_reg_variant_def]
 ) >- simp [] >>
 ho_match_mp_tac arm8_cont_avoid_exists_rule >>
 gen_tac >>
 ho_match_mp_tac arm8_cont_avoid_exists_rule >>
 gen_tac >>
 BETA_TAC >>
 Cases_on `a + b = pre_x + pre_y /\ 0w < a /\ w2n a = x` >- (
  QINST_IRULE [("l2", `add_reg_init_addr_3`),
  ("post1", `\ms. ms.PC = add_reg_end_addr_2_loop /\ arm8_add_reg_post_2_loop a b ms`),
  ("pre2", `arm8_add_reg_pre_3 a b`)] arm8_cont_avoid_seq_rule >>
  rpt conj_tac >- (
   QINST_IRULE [("pre1", `arm8_add_reg_pre_2 a b`),
  ("post1", `\ms. ms.PC = add_reg_end_addr_2_loop /\ arm8_add_reg_post_2_loop a b ms`)] arm8_cont_avoid_conseq_rule >>
   rpt conj_tac >- rw [arm8_add_reg_pre_2_def] >- simp [] >>
   addr_irule arm8_cont_add_reg_2_loop_avoid >>
   fs []
  ) >- rw ([arm8_add_reg_post_2_loop_def, arm8_add_reg_pre_3_def] @ addr_defs) >>
  QINST_IRULE [("pre1", `arm8_add_reg_pre_3 a b`),
  ("post1", `arm8_add_reg_post_3 a b`)] arm8_cont_avoid_conseq_rule >>
  rpt conj_tac >- simp [] >- (
   rw ([arm8_add_reg_post_3_def, arm8_add_reg_inv_def,
        arm8_add_reg_variant_def] @ addr_defs) >>
   METIS_TAC [add_reg_dec]
  ) >>
  MATCH_ACCEPT_TAC arm8_cont_add_reg_3_avoid
 ) >>
 rw [arm8_cont_avoid_def] >>
 METIS_TAC []
QED

(* loop exit: loop branch to the exit *)
Theorem arm8_cont_add_reg_exit:
 arm8_cont bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr}
  (\ms. arm8_add_reg_inv pre_x pre_y ms /\ ~arm8_add_reg_cond ms)
  (arm8_add_reg_post pre_x pre_y)
Proof
 QINST_IRULE [("pre1", `arm8_add_reg_pre_2 0w (pre_x + pre_y)`),
  ("post1", `\ms. ms.PC = add_reg_end_addr_2_ret /\
     arm8_add_reg_post_2_ret 0w (pre_x + pre_y) ms`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- (
  rw [arm8_add_reg_inv_def, arm8_add_reg_cond_def, arm8_add_reg_pre_2_def] >>
  `ms.REG 2w = 0w` by METIS_TAC [add_reg_zero] >>
  fs []
 ) >- rw [arm8_add_reg_post_2_ret_def, arm8_add_reg_post_def] >>
 addr_irule arm8_cont_add_reg_2_exit >>
 simp []
QED

Theorem arm8_cont_add_reg_loop:
 arm8_cont bir_add_reg_progbin add_reg_init_addr_2 {add_reg_end_addr}
  (arm8_add_reg_inv pre_x pre_y)
  (arm8_add_reg_post pre_x pre_y)
Proof
 QINST_IRULE [("C", `arm8_add_reg_cond`),
  ("var", `arm8_add_reg_variant`)] arm8_cont_loop_rule >>
 simp [arm8_cont_add_reg_iter, arm8_cont_add_reg_exit]
QED

Theorem arm8_cont_add_reg:
 arm8_cont bir_add_reg_progbin add_reg_init_addr {add_reg_end_addr}
  (arm8_add_reg_pre pre_x pre_y)
  (arm8_add_reg_post pre_x pre_y)
Proof
 QINST_IRULE [("l2", `add_reg_init_addr_2`),
  ("post1", `\ms. ms.PC = add_reg_init_addr_2 /\ arm8_add_reg_inv pre_x pre_y ms`),
  ("pre2", `arm8_add_reg_inv pre_x pre_y`)] arm8_cont_avoid_cont_seq_rule >>
 rpt conj_tac >- MATCH_ACCEPT_TAC arm8_cont_add_reg_before_loop >- simp [] >>
 MATCH_ACCEPT_TAC arm8_cont_add_reg_loop
QED

val _ = export_theory ();
