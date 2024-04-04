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

(*
Theorem abstract_jgmt_rel_incr[local]:
 abstract_jgmt_rel (bir_ts bprog) (BL_Address (Imm64 0w)) {BL_Address (Imm64 8w)}
  (\st. bir_exec_to_labels_triple_precond st pre bir_incr_prog)
  (\st st'. bir_exec_to_labels_triple_postcond st' post bprog)
Proof
 (* reasoning using symbolic execution goes here *)
 cheat
QED
*)

Theorem bir_cont_incr[local]:
 bir_cont bir_incr_prog bir_exp_true (BL_Address (Imm64 0w))
  {BL_Address (Imm64 8w)} {} bir_incr_pre
  (\l. if l = BL_Address (Imm64 8w) then bir_incr_post else bir_exp_false)
Proof
 cheat
QED

(* TODO: RISC-V backlifting *)

val _ = export_theory ();
