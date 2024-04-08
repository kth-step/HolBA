open HolKernel boolLib Parse bossLib;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open tutorial_smtSupportLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open birs_stepLib;

open incrTheory;

open incr_symb_execTheory;

val _ = new_theory "incr_prop";

(* ------ *)

Definition riscv_incr_pre_def:
 riscv_incr_pre (m : riscv_state) = T (* FIXME *)
End

Definition riscv_incr_post_def:
 riscv_incr_post (m : riscv_state) = T (* FIXME *)
End

Definition bir_incr_pre_def:
  bir_incr_pre : bir_exp_t = bir_exp_true (* FIXME *)
End

Definition bir_incr_post_def:
 bir_incr_post : bir_exp_t = bir_exp_true (* FIXME *)
End

(* ------ *)

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) incr_symb_analysis_thm;

Definition incr_analysis_L_def:
 incr_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 8w))``;

Definition bprecond_def:
  bprecond = bir_exp_true
End

val bprecond = (fst o dest_eq o concl) bprecond_def;

Definition bsysprecond_def:
  bsysprecond = FST (THE (birs_eval_exp ^bprecond (bir_senv_GEN_list birenvtyl_riscv)))
End

Theorem bprecond_birs_eval_exp_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC
   birs_stepLib.birs_eval_exp_CONV)
     ``birs_eval_exp bprecond (bir_senv_GEN_list birenvtyl_riscv)``

Theorem bsysprecond_thm =
 (REWRITE_CONV [bsysprecond_def, birs_eval_exp_ALT_thm, bprecond_birs_eval_exp_thm] THENC EVAL) ``bsysprecond``

Theorem bprecond_birs_eval_exp_thm2 = REWRITE_CONV [bprecond_birs_eval_exp_thm, GSYM bsysprecond_thm] ``birs_eval_exp bprecond (bir_senv_GEN_list birenvtyl_riscv)``

val bsysprecond = (fst o dest_eq o concl) bsysprecond_def;

val birs_state_init_pre = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl_riscv;
  bsst_status   := BST_Running;
  bsst_pcond    := ^bsysprecond
|>``;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
val birs_state_init_pre_EQ_thm =
 REWRITE_RULE [] ((REWRITE_CONV [bsysprecond_thm] THENC
  SIMP_CONV (std_ss++birs_state_ss++holBACore_ss) [] THENC
  EVAL)
  ``^((snd o dest_comb) sys_i) = ^birs_state_init_pre``);

val incr_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm] incr_symb_analysis_thm;

Theorem birenvtyl_riscv_EVAL_thm =
 (REWRITE_CONV [birenvtyl_riscv_def, riscv_vars_def,
   bir_lifting_machinesTheory.riscv_bmr_vars_EVAL,
   bir_lifting_machinesTheory.riscv_bmr_temp_vars_EVAL] THENC EVAL) ``birenvtyl_riscv``

val birs_state_thm = REWRITE_CONV [birenvtyl_riscv_EVAL_thm] birs_state_init_pre;

(* ------ *)

(* now the transfer *)

val bprog_tm = (fst o dest_eq o concl) bir_incr_prog_def;

val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'observation_type` |-> Type.alpha] bprog_tm) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);

Definition bprog_P_def:
  bprog_P ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       pc.bpc_index = 0 /\
       bir_envty_list birenvtyl_riscv st /\
       bir_eval_exp ^bprecond (BEnv st) = SOME bir_val_true)
End

(* translate the property to BIR state property *)
Theorem bprog_P_thm:
  !bs.
  bprog_P (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bs.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl_riscv bs.bst_environ /\
       bir_eval_exp ^bprecond bs.bst_environ = SOME bir_val_true)
Proof
 REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_P_def, bir_envty_list_b_thm, bir_BEnv_lookup_EQ_thm]
QED

Definition bprog_Q_def:
  bprog_Q
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (
       (pc2 = ^birs_state_end_lbl)
       /\
       (status2 = BST_Running)
     )
End

Theorem bprog_Q_thm:
  !bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (
      (bs2.bst_pc = ^birs_state_end_lbl)
      /\
      (bs2.bst_status = BST_Running)
    )
Proof
FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
QED

Theorem abstract_jgmt_rel_incr[local]:
 abstract_jgmt_rel (bir_ts bir_incr_prog) (BL_Address (Imm64 0w)) {BL_Address (Imm64 8w)}
  (\st. bir_exec_to_labels_triple_precond st bir_incr_pre bir_incr_prog)
  (\st st'. bir_exec_to_labels_triple_postcond st' (\l. if l = BL_Address (Imm64 8w) then bir_incr_post else bir_exp_false) bir_incr_prog)
Proof
 (* reasoning via symb_prop_transfer_thm goes here *)
 cheat
QED

Theorem bir_cont_incr[local]:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 8w)} {} bir_incr_pre
  (\l. if l = BL_Address (Imm64 8w) then bir_incr_post else bir_exp_false)
Proof
 `{BL_Address (Imm64 8w)} <> {}` by fs [] >>
 MP_TAC (Q.SPECL [`bir_incr_prog`,
  `BL_Address (Imm64 0w)`,
  `{BL_Address (Imm64 8w)}`,
  `bir_incr_pre`,
  `\l. if l = BL_Address (Imm64 8w) then bir_incr_post else bir_exp_false`
 ] abstract_jgmt_rel_bir_cont) >>
 rw [] >>
 METIS_TAC [abstract_jgmt_rel_incr]
QED

(* TODO: RISC-V backlifting *)

val _ = export_theory ();
