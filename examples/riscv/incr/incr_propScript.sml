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

open tutorial_smtSupportLib;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open incrTheory;
open incr_specTheory;
open incr_symb_transfTheory;

val _ = new_theory "incr_prop";

(* --------------- *)
(* BIR HL contract *)
(* --------------- *)

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_incr_thm =
 get_riscv_contract_sing
  bir_cont_incr
  ``bir_incr_progbin``
  ``riscv_incr_pre pre_x10`` ``riscv_incr_post pre_x10`` bir_incr_prog_def
  [bir_incr_pre_def]
  bir_incr_pre_def incr_riscv_pre_imp_bir_pre_thm
  [bir_incr_post_def] incr_riscv_post_imp_bir_post_thm
  bir_incr_riscv_lift_THM;

Theorem riscv_cont_incr:
 riscv_cont bir_incr_progbin 0w {4w} (riscv_incr_pre pre_x10) (riscv_incr_post pre_x10)
Proof
 ACCEPT_TAC riscv_cont_incr_thm
QED

(* unfolded theorem *)
val tm = concl riscv_cont_incr;
val sset = std_ss++bir_wm_SS++bir_lifting_machinesLib.bmr_ss;
val thms = [riscv_cont_def, t_jgmt_def, riscv_ts_def, riscv_weak_trs_def, riscv_incr_pre_def, riscv_incr_post_def, riscv_bmr_def, riscv_state_is_OK_def];
(*
EVAL tm;
SIMP_CONV sset thms tm
REWRITE_CONV  tm;
*)
val readable_thm = computeLib.RESTR_EVAL_CONV [``riscv_weak_trs``] tm;

Theorem riscv_cont_incr_full:
  !pre_x10. ^((snd o dest_eq o concl) readable_thm)
Proof
  METIS_TAC [riscv_cont_incr, readable_thm]
QED

val _ = export_theory ();
