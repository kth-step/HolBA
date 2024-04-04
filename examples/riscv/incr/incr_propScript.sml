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

open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open birs_stepLib;

open incrTheory;

open incr_symb_execTheory;

val _ = new_theory "incr_prop";

Definition riscv_incr_pre_def:
 riscv_incr_pre (m : riscv_state) = F
End

Definition riscv_incr_post_def:
 riscv_incr_post (m : riscv_state) = T
End

Definition bir_incr_pre_def:
  bir_incr_pre : bir_exp_t = bir_exp_false
End

Definition bir_incr_post_def:
 bir_incr_post : bir_exp_t = bir_exp_true
End

Theorem bir_cont_incr[local]:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 20w)} {} bir_incr_pre
  (\l. if l = BL_Address (Imm64 20w) then bir_incr_post else bir_exp_false)
Proof
 cheat
QED

val _ = export_theory ();
