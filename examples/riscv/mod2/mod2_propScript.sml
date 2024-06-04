open HolKernel boolLib Parse bossLib;

open markerTheory;

open numTheory arithmeticTheory int_bitwiseTheory;
open pairTheory combinTheory wordsTheory;

open distribute_generic_stuffLib;

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

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open distribute_generic_stuffTheory;

open mod2Theory;
open mod2_specTheory;
open mod2_symb_transfTheory;

val _ = new_theory "mod2_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_mod2_thm =
 get_riscv_contract_sing
  bir_cont_mod2
  ``bir_mod2_progbin``
  ``riscv_mod2_pre pre_x10`` ``riscv_mod2_post pre_x10`` bir_mod2_prog_def
  [bir_mod2_pre_def]
  bir_mod2_pre_def mod2_riscv_pre_imp_bir_pre_thm
  [bir_mod2_post_def] mod2_riscv_post_imp_bir_post_thm
  bir_mod2_riscv_lift_THM;

Theorem riscv_cont_mod2:
 riscv_cont bir_mod2_progbin 0w {4w} (riscv_mod2_pre pre_x10) (riscv_mod2_post pre_x10)
Proof
 ACCEPT_TAC riscv_cont_mod2_thm
QED

(* unfolded theorem *)
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
val tm = concl riscv_cont_mod2;
val sset = std_ss++bir_wm_SS++bir_lifting_machinesLib.bmr_ss;
val thms = [riscv_cont_def, t_jgmt_def, riscv_ts_def, riscv_weak_trs_def, riscv_mod2_pre_def, riscv_mod2_post_def, riscv_bmr_def, riscv_state_is_OK_def];
(*
EVAL tm;
SIMP_CONV sset thms tm
REWRITE_CONV  tm;
*)
val readable_thm = computeLib.RESTR_EVAL_CONV [``riscv_weak_trs``] tm;

Theorem riscv_cont_mod2_full:
  !pre_x10. ^((snd o dest_eq o concl) readable_thm)
Proof
  METIS_TAC [riscv_cont_mod2, readable_thm]
QED

val _ = export_theory ();
