open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
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

open isqrtTheory;
open isqrt_auxTheory;
open isqrt_spec_riscvTheory;
open isqrt_spec_birTheory;
open isqrt_symb_transfTheory;

val _ = new_theory "isqrt_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

(* contracts 1 and 2 also list the loop exit as ending label,
   which is never reached first, for composition *)

val riscv_cont_isqrt_1_thm =
 get_riscv_contract_thm
  bspec_cont_isqrt_1 isqrt_init_addr_1_def [isqrt_end_addr_1_def, isqrt_end_addr_def]
  bir_isqrt_progbin_def
  riscv_isqrt_pre_1_def riscv_isqrt_post_1_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_1_def]
  bspec_isqrt_pre_1_def isqrt_riscv_pre_1_imp_bspec_pre_1_thm
  [bspec_isqrt_post_1_def, isqrt_end_addr_1_def, isqrt_end_addr_def]
  isqrt_riscv_post_1_imp_bspec_post_1_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_1:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1; isqrt_end_addr}
  (riscv_isqrt_pre_1 pre_x10)
  (riscv_isqrt_post_1 pre_x10)
Proof
 ACCEPT_TAC riscv_cont_isqrt_1_thm
QED

val riscv_cont_isqrt_2_thm =
 get_riscv_contract_thm
  bspec_cont_isqrt_2 isqrt_init_addr_2_def [isqrt_end_addr_2_def, isqrt_end_addr_def]
  bir_isqrt_progbin_def
  riscv_isqrt_pre_2_def riscv_isqrt_post_2_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_2_def]
  bspec_isqrt_pre_2_def isqrt_riscv_pre_2_imp_bspec_pre_2_thm
  [bspec_isqrt_post_2_def, isqrt_end_addr_2_def, isqrt_end_addr_def]
  isqrt_riscv_post_2_imp_bspec_post_2_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_2:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2; isqrt_end_addr}
  (riscv_isqrt_pre_2 pre_x13 pre_x15)
  (riscv_isqrt_post_2 pre_x13 pre_x15)
Proof
 ACCEPT_TAC riscv_cont_isqrt_2_thm
QED

val riscv_cont_isqrt_3_thm =
 get_riscv_contract_thm
  bspec_cont_isqrt_3 isqrt_init_addr_3_def [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def]
  bir_isqrt_progbin_def
  riscv_isqrt_pre_3_def riscv_isqrt_post_3_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_3_def]
  bspec_isqrt_pre_3_def isqrt_riscv_pre_3_imp_bspec_pre_3_thm
  [bspec_isqrt_post_3_loop_def, bspec_isqrt_post_3_ret_def,
   isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def]
  isqrt_riscv_post_3_imp_bspec_post_3_thm
  bir_isqrt_riscv_lift_THM;

Theorem riscv_cont_isqrt_3:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15)
  (riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14 pre_x15)
Proof
 ACCEPT_TAC riscv_cont_isqrt_3_thm
QED

(* ------------------------------ *)
(* Whole program contract          *)
(* ------------------------------ *)

(* The loop head is isqrt_init_addr_2 and the loop exit
   isqrt_end_addr. Since the piece contracts cannot state that
   execution does not return to their own start label, iterations are
   expressed as avoidance contracts (riscv_cont_avoid), which only
   require that the loop exit is not encountered on the way back to
   the loop head. *)

(* Some addresses have several names, e.g., isqrt_end_addr_1 and
   isqrt_init_addr_2. A theorem whose address names differ from
   those of the goal is used with UNFOLD_IRULE addr_defs. *)
val addr_defs = [
 isqrt_init_addr_def,
 isqrt_init_addr_1_def, isqrt_end_addr_1_def,
 isqrt_init_addr_2_def, isqrt_end_addr_2_def,
 isqrt_init_addr_3_def, isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def,
 isqrt_end_addr_def];

Theorem riscv_cont_isqrt_1_avoid:
 riscv_cont_avoid bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr}
  (riscv_isqrt_pre_1 pre_x10)
  (riscv_isqrt_post_1 pre_x10)
Proof
 QINST_IRULE [("ls", `{isqrt_end_addr_1}`)] riscv_cont_avoid_intro >>
 conj_tac >- rw (riscv_isqrt_post_1_def :: addr_defs) >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 ACCEPT_TAC riscv_cont_isqrt_1
QED

Theorem riscv_cont_isqrt_2_avoid:
 riscv_cont_avoid bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr}
  (riscv_isqrt_pre_2 pre_x13 pre_x15)
  (riscv_isqrt_post_2 pre_x13 pre_x15)
Proof
 QINST_IRULE [("ls", `{isqrt_end_addr_2}`)] riscv_cont_avoid_intro >>
 conj_tac >- rw (riscv_isqrt_post_2_def :: addr_defs) >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 ACCEPT_TAC riscv_cont_isqrt_2
QED

(* loop branch when the loop condition holds *)
Theorem riscv_cont_isqrt_3_loop_avoid:
 pre_x14 <=+ pre_x13 ==>
 riscv_cont_avoid bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_ret}
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15)
  (\ms. ms.c_PC ms.procID = isqrt_end_addr_3_loop /\ riscv_isqrt_post_3_loop pre_x10 pre_x13 pre_x14 pre_x15 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls", `{isqrt_end_addr_3_loop}`)] riscv_cont_avoid_intro >>
 conj_tac >- simp addr_defs >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 QINST_IRULE [("pre1", `riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15`),
  ("post1", `riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14 pre_x15`)] riscv_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.c_PC ms.procID = isqrt_end_addr_3_loop` >>
  fs ([riscv_isqrt_post_3_def, riscv_isqrt_post_3_ret_def] @ addr_defs) >>
  METIS_TAC [WORD_NOT_LOWER]
 ) >>
 ACCEPT_TAC riscv_cont_isqrt_3
QED

(* loop branch when the loop condition does not hold *)
Theorem riscv_cont_isqrt_3_exit:
 pre_x13 <+ pre_x14 ==>
 riscv_cont bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_ret}
  (riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15)
  (\ms. ms.c_PC ms.procID = isqrt_end_addr_3_ret /\ riscv_isqrt_post_3_ret pre_x10 pre_x13 pre_x14 pre_x15 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls2", `{isqrt_end_addr_3_loop}`)] riscv_cont_subset_rule >>
 conj_tac >- simp addr_defs >>
 `{isqrt_end_addr_3_ret} UNION {isqrt_end_addr_3_loop} =
  {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}`
  by (rw [EXTENSION] >> METIS_TAC []) >>
 pop_assum (fn thm => REWRITE_TAC [thm]) >>
 QINST_IRULE [("pre1", `riscv_isqrt_pre_3 pre_x10 pre_x13 pre_x14 pre_x15`),
  ("post1", `riscv_isqrt_post_3 pre_x10 pre_x13 pre_x14 pre_x15`)] riscv_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.c_PC ms.procID = isqrt_end_addr_3_loop` >>
  fs ([riscv_isqrt_post_3_def, riscv_isqrt_post_3_loop_def] @ addr_defs) >>
  METIS_TAC [WORD_NOT_LOWER]
 ) >>
 ACCEPT_TAC riscv_cont_isqrt_3
QED

(* before loop: establish the loop invariant *)
Theorem riscv_cont_isqrt_before_loop:
 riscv_cont_avoid bir_isqrt_progbin isqrt_init_addr {isqrt_end_addr}
  (riscv_isqrt_pre pre_x10)
  (\ms. ms.c_PC ms.procID = isqrt_init_addr_2 /\ riscv_isqrt_inv pre_x10 ms)
Proof
 Cases_on `pre_x10 <+ 0xFFFFFFFE00000001w` >- (
  QINST_IRULE [("pre1", `riscv_isqrt_pre_1 pre_x10`),
  ("post1", `riscv_isqrt_post_1 pre_x10`)] riscv_cont_avoid_conseq_rule >>
  rpt conj_tac >- rw [riscv_isqrt_pre_def, riscv_isqrt_pre_1_def] >- (
   rw ([riscv_isqrt_post_1_def, riscv_isqrt_inv_def] @ addr_defs) >>
   EVAL_TAC
  ) >>
  UNFOLD_IRULE addr_defs riscv_cont_isqrt_1_avoid
 ) >>
 rw [riscv_cont_avoid_def, riscv_isqrt_pre_def]
QED

(* one loop iteration: loop body followed by loop branch back to the head *)
Theorem riscv_cont_isqrt_iter:
 !x. riscv_cont_avoid bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr}
  (\ms. riscv_isqrt_inv pre_x10 ms /\ riscv_isqrt_cond ms /\ riscv_isqrt_variant ms = x)
  (\ms. ms.c_PC ms.procID = isqrt_init_addr_2 /\ riscv_isqrt_inv pre_x10 ms /\ riscv_isqrt_variant ms < x)
Proof
 gen_tac >>
 QINST_IRULE [("pre1", `\ms. ?y. ms.c_gpr ms.procID 15w = y /\ ms.c_gpr ms.procID 13w = pre_x10 /\
     pre_x10 <+ 0xFFFFFFFE00000001w /\ y <+ 0xFFFFFFFFw /\
     (y + 1w) * (y + 1w) <=+ pre_x10 /\ w2n pre_x10 - w2n y = x`),
  ("post1", `\ms. ms.c_PC ms.procID = isqrt_init_addr_2 /\ riscv_isqrt_inv pre_x10 ms /\
     riscv_isqrt_variant ms < x`)] riscv_cont_avoid_conseq_rule >>
 rpt conj_tac >- (
  rw [riscv_isqrt_inv_def, riscv_isqrt_cond_def, riscv_isqrt_variant_def] >>
  METIS_TAC []
 ) >- simp [] >>
 ho_match_mp_tac riscv_cont_avoid_exists_rule >>
 gen_tac >>
 BETA_TAC >>
 Cases_on `pre_x10 <+ 0xFFFFFFFE00000001w /\ y <+ 0xFFFFFFFFw /\
   (y + 1w) * (y + 1w) <=+ pre_x10 /\ w2n pre_x10 - w2n y = x` >- (
  QINST_IRULE [("l2", `isqrt_init_addr_3`),
  ("post1", `riscv_isqrt_post_2 pre_x10 y`),
  ("pre2", `riscv_isqrt_pre_3 y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w)`)] riscv_cont_avoid_seq_rule >>
  rpt conj_tac >- (
   QINST_IRULE [("pre1", `riscv_isqrt_pre_2 pre_x10 y`),
  ("post1", `riscv_isqrt_post_2 pre_x10 y`)] riscv_cont_avoid_conseq_rule >>
   rpt conj_tac >- rw [riscv_isqrt_pre_2_def] >- simp [] >>
   MATCH_ACCEPT_TAC riscv_cont_isqrt_2_avoid
  ) >- rw ([riscv_isqrt_post_2_def, riscv_isqrt_pre_3_def] @ addr_defs) >>
  QINST_IRULE [("pre1", `riscv_isqrt_pre_3 y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w)`),
  ("post1", `\ms. ms.c_PC ms.procID = isqrt_end_addr_3_loop /\
     riscv_isqrt_post_3_loop y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w) ms`)] riscv_cont_avoid_conseq_rule >>
  rpt conj_tac >- simp [] >- (
   rw ([riscv_isqrt_post_3_loop_def, riscv_isqrt_inv_def, riscv_isqrt_variant_def] @ addr_defs) >>
   qspecl_then [`ms.c_gpr ms.procID 10w`, `ms.c_gpr ms.procID 13w`] mp_tac isqrt_step >>
   simp []
  ) >>
  UNFOLD_IRULE addr_defs riscv_cont_isqrt_3_loop_avoid >>
  fs []
 ) >>
 rw [riscv_cont_avoid_def] >>
 METIS_TAC []
QED

(* loop exit: loop body followed by loop branch to the exit *)
Theorem riscv_cont_isqrt_exit:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr}
  (\ms. riscv_isqrt_inv pre_x10 ms /\ ~riscv_isqrt_cond ms)
  (riscv_isqrt_post pre_x10)
Proof
 QINST_IRULE [("pre1", `\ms. ?y. ms.c_gpr ms.procID 15w = y /\ ms.c_gpr ms.procID 13w = pre_x10 /\
     y <+ 0xFFFFFFFFw /\ y * y <=+ pre_x10 /\ pre_x10 <+ (y + 1w) * (y + 1w)`),
  ("post1", `riscv_isqrt_post pre_x10`)] riscv_cont_conseq_rule >>
 rpt conj_tac >- (
  rw [riscv_isqrt_inv_def, riscv_isqrt_cond_def, WORD_NOT_LOWER_EQUAL] >>
  METIS_TAC []
 ) >- simp [] >>
 ho_match_mp_tac riscv_cont_exists_rule >>
 gen_tac >>
 BETA_TAC >>
 Cases_on `y <+ 0xFFFFFFFFw /\ y * y <=+ pre_x10 /\ pre_x10 <+ (y + 1w) * (y + 1w)` >- (
  QINST_IRULE [("l2", `isqrt_init_addr_3`),
  ("post1", `riscv_isqrt_post_2 pre_x10 y`),
  ("pre2", `riscv_isqrt_pre_3 y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w)`)] riscv_cont_avoid_cont_seq_rule >>
  rpt conj_tac >- (
   QINST_IRULE [("pre1", `riscv_isqrt_pre_2 pre_x10 y`),
  ("post1", `riscv_isqrt_post_2 pre_x10 y`)] riscv_cont_avoid_conseq_rule >>
   rpt conj_tac >- rw [riscv_isqrt_pre_2_def] >- simp [] >>
   MATCH_ACCEPT_TAC riscv_cont_isqrt_2_avoid
  ) >- rw ([riscv_isqrt_post_2_def, riscv_isqrt_pre_3_def] @ addr_defs) >>
  QINST_IRULE [("pre1", `riscv_isqrt_pre_3 y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w)`),
  ("post1", `\ms. ms.c_PC ms.procID = isqrt_end_addr_3_ret /\
     riscv_isqrt_post_3_ret y pre_x10 ((y + 1w) * (y + 1w)) (y + 1w) ms`)] riscv_cont_conseq_rule >>
  rpt conj_tac >- simp [] >- rw [riscv_isqrt_post_3_ret_def, riscv_isqrt_post_def] >>
  UNFOLD_IRULE addr_defs riscv_cont_isqrt_3_exit >>
  fs []
 ) >>
 rw [riscv_cont_def, total_program_logicTheory.t_jgmt_def] >>
 METIS_TAC []
QED

Theorem riscv_cont_isqrt_loop:
 riscv_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr}
  (riscv_isqrt_inv pre_x10)
  (riscv_isqrt_post pre_x10)
Proof
 QINST_IRULE [("C", `riscv_isqrt_cond`),
  ("var", `riscv_isqrt_variant`)] riscv_cont_loop_rule >>
 simp [riscv_cont_isqrt_iter, riscv_cont_isqrt_exit]
QED

Theorem riscv_cont_isqrt:
 riscv_cont bir_isqrt_progbin isqrt_init_addr {isqrt_end_addr}
  (riscv_isqrt_pre pre_x10)
  (riscv_isqrt_post pre_x10)
Proof
 QINST_IRULE [("l2", `isqrt_init_addr_2`),
  ("post1", `\ms. ms.c_PC ms.procID = isqrt_init_addr_2 /\ riscv_isqrt_inv pre_x10 ms`),
  ("pre2", `riscv_isqrt_inv pre_x10`)] riscv_cont_avoid_cont_seq_rule >>
 rpt conj_tac >- MATCH_ACCEPT_TAC riscv_cont_isqrt_before_loop >- simp [] >>
 MATCH_ACCEPT_TAC riscv_cont_isqrt_loop
QED

val _ = export_theory ();
