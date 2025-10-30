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

open incrTheory;
open incr_spec_arm8Theory;
open incr_spec_birTheory;
open incr_symb_transfTheory;

val _ = new_theory "incr_prop";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_incr_progbin_def;
val arm8_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) arm8_incr_pre_def;
val arm8_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) arm8_incr_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val arm8_cont_incr_thm =
 get_arm8_contract
  bspec_cont_incr
  progbin_tm
  arm8_pre_tm arm8_post_tm bir_incr_prog_def
  [bspec_incr_pre_def]
  bspec_incr_pre_def incr_arm8_pre_imp_bspec_pre_thm
  [bspec_incr_post_def] incr_arm8_post_imp_bspec_post_thm
  bir_incr_arm8_lift_THM;

Theorem arm8_cont_incr:
 arm8_cont bir_incr_progbin incr_init_addr {incr_end_addr}
  (arm8_incr_pre pre_x0)
  (arm8_incr_post pre_x0)
Proof
 rw [incr_init_addr_def,incr_end_addr_def] >>
 ACCEPT_TAC arm8_cont_incr_thm
QED

(* ------------------------ *)
(* Unfolded ARMv8 contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``arm8_weak_trs``] arm8_cont_incr;
Theorem arm8_cont_incr_full = GEN_ALL readable_thm;

val _ = export_theory ();
