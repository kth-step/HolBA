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

open isqrtTheory;
open isqrt_auxTheory;
open isqrt_spec_arm8Theory;
open isqrt_spec_birTheory;
open isqrt_symb_transfTheory;

val _ = new_theory "isqrt_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

(* contracts 1 and 2 also exclude the loop exit, for composition *)

val arm8_cont_isqrt_1_excl_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_1 isqrt_init_addr_1_def [isqrt_end_addr_1_def, isqrt_end_addr_def]
  bir_isqrt_progbin_def
  arm8_isqrt_pre_1_def arm8_isqrt_post_1_excl_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_1_def]
  bspec_isqrt_pre_1_def isqrt_arm8_pre_1_imp_bspec_pre_1_thm
  [bspec_isqrt_post_1_def] isqrt_arm8_post_1_excl_imp_bspec_post_1_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_1_excl:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1; isqrt_end_addr}
  (arm8_isqrt_pre_1 pre_x0)
  (arm8_isqrt_post_1_excl pre_x0)
Proof
 ACCEPT_TAC arm8_cont_isqrt_1_excl_thm
QED

Theorem arm8_cont_isqrt_1:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_1 {isqrt_end_addr_1}
  (arm8_isqrt_pre_1 pre_x0)
  (arm8_isqrt_post_1 pre_x0)
Proof
 QINST_IRULE [("pre1", `arm8_isqrt_pre_1 pre_x0`),
  ("post1", `arm8_isqrt_post_1_excl pre_x0`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- rw [arm8_isqrt_post_1_excl_def] >>
 QINST_IRULE [("ls2", `{isqrt_end_addr}`)] arm8_cont_subset_rule >>
 conj_tac >- rw [arm8_isqrt_post_1_excl_def, isqrt_end_addr_def, isqrt_end_addr_1_def] >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 MATCH_ACCEPT_TAC arm8_cont_isqrt_1_excl
QED

val arm8_cont_isqrt_2_excl_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_2 isqrt_init_addr_2_def [isqrt_end_addr_2_def, isqrt_end_addr_def]
  bir_isqrt_progbin_def
  arm8_isqrt_pre_2_def arm8_isqrt_post_2_excl_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_2_def]
  bspec_isqrt_pre_2_def isqrt_arm8_pre_2_imp_bspec_pre_2_thm
  [bspec_isqrt_post_2_def] isqrt_arm8_post_2_excl_imp_bspec_post_2_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_2_excl:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2; isqrt_end_addr}
  (arm8_isqrt_pre_2 pre_x1 pre_x3)
  (arm8_isqrt_post_2_excl pre_x1 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_isqrt_2_excl_thm
QED

Theorem arm8_cont_isqrt_2:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_2 {isqrt_end_addr_2}
  (arm8_isqrt_pre_2 pre_x1 pre_x3)
  (arm8_isqrt_post_2 pre_x1 pre_x3)
Proof
 QINST_IRULE [("pre1", `arm8_isqrt_pre_2 pre_x1 pre_x3`),
  ("post1", `arm8_isqrt_post_2_excl pre_x1 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- rw [arm8_isqrt_post_2_excl_def] >>
 QINST_IRULE [("ls2", `{isqrt_end_addr}`)] arm8_cont_subset_rule >>
 conj_tac >- rw [arm8_isqrt_post_2_excl_def, isqrt_end_addr_def, isqrt_end_addr_2_def] >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 MATCH_ACCEPT_TAC arm8_cont_isqrt_2_excl
QED

val arm8_cont_isqrt_3_thm =
 get_arm8_contract_thm
  bspec_cont_isqrt_3 isqrt_init_addr_3_def [isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def]
  bir_isqrt_progbin_def
  arm8_isqrt_pre_3_def arm8_isqrt_post_3_def
  bir_isqrt_prog_def
  [bspec_isqrt_pre_3_def]
  bspec_isqrt_pre_3_def isqrt_arm8_pre_3_imp_bspec_pre_3_thm
  [bspec_isqrt_post_3_loop_def,bspec_isqrt_post_3_ret_def] isqrt_arm8_post_3_imp_bspec_post_3_thm
  bir_isqrt_arm8_lift_THM;

Theorem arm8_cont_isqrt_3:
 arm8_cont bir_isqrt_progbin isqrt_init_addr_3 {isqrt_end_addr_3_loop; isqrt_end_addr_3_ret}
  (arm8_isqrt_pre_3 pre_x0 pre_x1 pre_x2 pre_x3)
  (arm8_isqrt_post_3 pre_x0 pre_x1 pre_x2 pre_x3)
Proof
 ACCEPT_TAC arm8_cont_isqrt_3_thm
QED

(* ------------------------------ *)
(* Whole program contract          *)
(* ------------------------------ *)

(* The loop head is 0x720 and the loop exit 0x734. Since the piece
   contracts cannot state that execution does not return to their own
   start label, iterations are expressed as avoidance contracts
   (arm8_cont_avoid), which only require that the loop exit is not
   encountered on the way back to the loop head. *)

val addr_defs = [
 isqrt_init_addr_1_def, isqrt_end_addr_1_def,
 isqrt_init_addr_2_def, isqrt_end_addr_2_def,
 isqrt_init_addr_3_def, isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def,
 isqrt_end_addr_def];

Theorem arm8_cont_isqrt_1_avoid:
 arm8_cont_avoid bir_isqrt_progbin 0x718w {0x734w}
  (arm8_isqrt_pre_1 pre_x0)
  (\ms. ms.PC = 0x720w /\ arm8_isqrt_post_1 pre_x0 ms)
Proof
 QINST_IRULE [("ls", `{0x720w}`)] arm8_cont_avoid_intro >>
 conj_tac >- simp [] >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 QINST_IRULE [("pre1", `arm8_isqrt_pre_1 pre_x0`),
  ("post1", `arm8_isqrt_post_1_excl pre_x0`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- rw [arm8_isqrt_post_1_excl_def, isqrt_end_addr_1_def] >>
 ACCEPT_TAC (REWRITE_RULE addr_defs arm8_cont_isqrt_1_excl)
QED

Theorem arm8_cont_isqrt_2_avoid:
 arm8_cont_avoid bir_isqrt_progbin 0x720w {0x734w}
  (arm8_isqrt_pre_2 pre_x1 pre_x3)
  (\ms. ms.PC = 0x72cw /\ arm8_isqrt_post_2 pre_x1 pre_x3 ms)
Proof
 QINST_IRULE [("ls", `{0x72cw}`)] arm8_cont_avoid_intro >>
 conj_tac >- simp [] >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 QINST_IRULE [("pre1", `arm8_isqrt_pre_2 pre_x1 pre_x3`),
  ("post1", `arm8_isqrt_post_2_excl pre_x1 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- rw [arm8_isqrt_post_2_excl_def, isqrt_end_addr_2_def] >>
 ACCEPT_TAC (REWRITE_RULE addr_defs arm8_cont_isqrt_2_excl)
QED

(* loop branch when the loop condition holds *)
Theorem arm8_cont_isqrt_3_loop_avoid:
 pre_x2 <=+ pre_x3 ==>
 arm8_cont_avoid bir_isqrt_progbin 0x72cw {0x734w}
  (arm8_isqrt_pre_3 pre_x0 pre_x1 pre_x2 pre_x3)
  (\ms. ms.PC = 0x720w /\ arm8_isqrt_post_3_loop pre_x0 pre_x1 pre_x2 pre_x3 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls", `{0x720w}`)] arm8_cont_avoid_intro >>
 conj_tac >- simp [] >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 QINST_IRULE [("pre1", `arm8_isqrt_pre_3 pre_x0 pre_x1 pre_x2 pre_x3`),
  ("post1", `arm8_isqrt_post_3 pre_x0 pre_x1 pre_x2 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.PC = 0x720w` >>
  fs [arm8_isqrt_post_3_def, arm8_isqrt_post_3_ret_def,
      isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def] >>
  METIS_TAC [WORD_NOT_LOWER]
 ) >>
 ACCEPT_TAC (REWRITE_RULE addr_defs arm8_cont_isqrt_3)
QED

(* loop branch when the loop condition does not hold *)
Theorem arm8_cont_isqrt_3_exit:
 pre_x3 <+ pre_x2 ==>
 arm8_cont bir_isqrt_progbin 0x72cw {0x734w}
  (arm8_isqrt_pre_3 pre_x0 pre_x1 pre_x2 pre_x3)
  (\ms. ms.PC = 0x734w /\ arm8_isqrt_post_3_ret pre_x0 pre_x1 pre_x2 pre_x3 ms)
Proof
 strip_tac >>
 QINST_IRULE [("ls2", `{0x720w}`)] arm8_cont_subset_rule >>
 conj_tac >- simp [] >>
 `{0x734w} UNION {0x720w} = {0x720w; 0x734w:word64}`
  by (rw [EXTENSION] >> METIS_TAC []) >>
 pop_assum (fn thm => REWRITE_TAC [thm]) >>
 QINST_IRULE [("pre1", `arm8_isqrt_pre_3 pre_x0 pre_x1 pre_x2 pre_x3`),
  ("post1", `arm8_isqrt_post_3 pre_x0 pre_x1 pre_x2 pre_x3`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- simp [] >- (
  rpt strip_tac >>
  Cases_on `ms.PC = 0x720w` >>
  fs [arm8_isqrt_post_3_def, arm8_isqrt_post_3_loop_def,
      isqrt_end_addr_3_loop_def, isqrt_end_addr_3_ret_def] >>
  METIS_TAC [WORD_NOT_LOWER]
 ) >>
 ACCEPT_TAC (REWRITE_RULE addr_defs arm8_cont_isqrt_3)
QED

(* before loop: establish the loop invariant *)
Theorem arm8_cont_isqrt_before_loop:
 arm8_cont_avoid bir_isqrt_progbin 0x718w {0x734w}
  (arm8_isqrt_pre pre_x0)
  (\ms. ms.PC = 0x720w /\ arm8_isqrt_inv pre_x0 ms)
Proof
 Cases_on `pre_x0 <+ 0xFFFFFFFE00000001w` >- (
  QINST_IRULE [("pre1", `arm8_isqrt_pre_1 pre_x0`),
  ("post1", `\ms. ms.PC = 0x720w /\ arm8_isqrt_post_1 pre_x0 ms`)] arm8_cont_avoid_conseq_rule >>
  rpt conj_tac >- rw [arm8_isqrt_pre_def, arm8_isqrt_pre_1_def] >- (
   rw [arm8_isqrt_post_1_def, arm8_isqrt_inv_def] >>
   EVAL_TAC
  ) >>
  MATCH_ACCEPT_TAC arm8_cont_isqrt_1_avoid
 ) >>
 rw [arm8_cont_avoid_def, arm8_isqrt_pre_def]
QED

(* one loop iteration: loop body followed by loop branch back to the head *)
Theorem arm8_cont_isqrt_iter:
 !x. arm8_cont_avoid bir_isqrt_progbin 0x720w {0x734w}
  (\ms. arm8_isqrt_inv pre_x0 ms /\ arm8_isqrt_cond ms /\ arm8_isqrt_variant ms = x)
  (\ms. ms.PC = 0x720w /\ arm8_isqrt_inv pre_x0 ms /\ arm8_isqrt_variant ms < x)
Proof
 gen_tac >>
 QINST_IRULE [("pre1", `\ms. ?y. ms.REG 1w = y /\ ms.REG 3w = pre_x0 /\
     pre_x0 <+ 0xFFFFFFFE00000001w /\ y <+ 0xFFFFFFFFw /\
     (y + 1w) * (y + 1w) <=+ pre_x0 /\ w2n pre_x0 - w2n y = x`),
  ("post1", `\ms. ms.PC = 0x720w /\ arm8_isqrt_inv pre_x0 ms /\ arm8_isqrt_variant ms < x`)] arm8_cont_avoid_conseq_rule >>
 rpt conj_tac >- (
  rw [arm8_isqrt_inv_def, arm8_isqrt_cond_def, arm8_isqrt_variant_def] >>
  METIS_TAC []
 ) >- simp [] >>
 ho_match_mp_tac arm8_cont_avoid_exists_rule >>
 gen_tac >>
 BETA_TAC >>
 Cases_on `pre_x0 <+ 0xFFFFFFFE00000001w /\ y <+ 0xFFFFFFFFw /\
   (y + 1w) * (y + 1w) <=+ pre_x0 /\ w2n pre_x0 - w2n y = x` >- (
  QINST_IRULE [("l2", `0x72cw`),
  ("post1", `\ms. ms.PC = 0x72cw /\ arm8_isqrt_post_2 y pre_x0 ms`),
  ("pre2", `arm8_isqrt_pre_3 y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0`)] arm8_cont_avoid_seq_rule >>
  rpt conj_tac >- (
   QINST_IRULE [("pre1", `arm8_isqrt_pre_2 y pre_x0`),
  ("post1", `\ms. ms.PC = 0x72cw /\ arm8_isqrt_post_2 y pre_x0 ms`)] arm8_cont_avoid_conseq_rule >>
   rpt conj_tac >- rw [arm8_isqrt_pre_2_def] >- simp [] >>
   MATCH_ACCEPT_TAC arm8_cont_isqrt_2_avoid
  ) >- rw [arm8_isqrt_post_2_def, arm8_isqrt_pre_3_def] >>
  QINST_IRULE [("pre1", `arm8_isqrt_pre_3 y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0`),
  ("post1", `\ms. ms.PC = 0x720w /\
     arm8_isqrt_post_3_loop y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0 ms`)] arm8_cont_avoid_conseq_rule >>
  rpt conj_tac >- simp [] >- (
   rw [arm8_isqrt_post_3_loop_def, arm8_isqrt_inv_def, arm8_isqrt_variant_def] >>
   qspecl_then [`ms.REG 0w`, `ms.REG 3w`] mp_tac isqrt_step >>
   simp []
  ) >>
  irule arm8_cont_isqrt_3_loop_avoid >>
  fs []
 ) >>
 rw [arm8_cont_avoid_def] >>
 METIS_TAC []
QED

(* loop exit: loop body followed by loop branch to the exit *)
Theorem arm8_cont_isqrt_exit:
 arm8_cont bir_isqrt_progbin 0x720w {0x734w}
  (\ms. arm8_isqrt_inv pre_x0 ms /\ ~arm8_isqrt_cond ms)
  (arm8_isqrt_post pre_x0)
Proof
 QINST_IRULE [("pre1", `\ms. ?y. ms.REG 1w = y /\ ms.REG 3w = pre_x0 /\
     y <+ 0xFFFFFFFFw /\ y * y <=+ pre_x0 /\ pre_x0 <+ (y + 1w) * (y + 1w)`),
  ("post1", `arm8_isqrt_post pre_x0`)] arm8_cont_conseq_rule >>
 rpt conj_tac >- (
  rw [arm8_isqrt_inv_def, arm8_isqrt_cond_def, WORD_NOT_LOWER_EQUAL] >>
  METIS_TAC []
 ) >- simp [] >>
 ho_match_mp_tac arm8_cont_exists_rule >>
 gen_tac >>
 BETA_TAC >>
 Cases_on `y <+ 0xFFFFFFFFw /\ y * y <=+ pre_x0 /\ pre_x0 <+ (y + 1w) * (y + 1w)` >- (
  QINST_IRULE [("l2", `0x72cw`),
  ("post1", `\ms. ms.PC = 0x72cw /\ arm8_isqrt_post_2 y pre_x0 ms`),
  ("pre2", `arm8_isqrt_pre_3 y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0`)] arm8_cont_avoid_cont_seq_rule >>
  rpt conj_tac >- (
   QINST_IRULE [("pre1", `arm8_isqrt_pre_2 y pre_x0`),
  ("post1", `\ms. ms.PC = 0x72cw /\ arm8_isqrt_post_2 y pre_x0 ms`)] arm8_cont_avoid_conseq_rule >>
   rpt conj_tac >- rw [arm8_isqrt_pre_2_def] >- simp [] >>
   MATCH_ACCEPT_TAC arm8_cont_isqrt_2_avoid
  ) >- rw [arm8_isqrt_post_2_def, arm8_isqrt_pre_3_def] >>
  QINST_IRULE [("pre1", `arm8_isqrt_pre_3 y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0`),
  ("post1", `\ms. ms.PC = 0x734w /\
     arm8_isqrt_post_3_ret y (y + 1w) ((y + 1w) * (y + 1w)) pre_x0 ms`)] arm8_cont_conseq_rule >>
  rpt conj_tac >- simp [] >- rw [arm8_isqrt_post_3_ret_def, arm8_isqrt_post_def] >>
  irule arm8_cont_isqrt_3_exit >>
  fs []
 ) >>
 rw [arm8_cont_def, total_program_logicTheory.t_jgmt_def] >>
 METIS_TAC []
QED

Theorem arm8_cont_isqrt_loop:
 arm8_cont bir_isqrt_progbin 0x720w {0x734w}
  (arm8_isqrt_inv pre_x0)
  (arm8_isqrt_post pre_x0)
Proof
 QINST_IRULE [("C", `arm8_isqrt_cond`),
  ("var", `arm8_isqrt_variant`)] arm8_cont_loop_rule >>
 simp [arm8_cont_isqrt_iter, arm8_cont_isqrt_exit]
QED

Theorem arm8_cont_isqrt:
 arm8_cont bir_isqrt_progbin isqrt_init_addr {isqrt_end_addr}
  (arm8_isqrt_pre pre_x0)
  (arm8_isqrt_post pre_x0)
Proof
 REWRITE_TAC [isqrt_init_addr_def, isqrt_end_addr_def] >>
 QINST_IRULE [("l2", `0x720w`),
  ("post1", `\ms. ms.PC = 0x720w /\ arm8_isqrt_inv pre_x0 ms`),
  ("pre2", `arm8_isqrt_inv pre_x0`)] arm8_cont_avoid_cont_seq_rule >>
 rpt conj_tac >- MATCH_ACCEPT_TAC arm8_cont_isqrt_before_loop >- simp [] >>
 MATCH_ACCEPT_TAC arm8_cont_isqrt_loop
QED

val _ = export_theory ();
