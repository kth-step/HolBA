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

open isqrtTheory;
open isqrt_specTheory;
open isqrt_symb_transfTheory;

val _ = new_theory "isqrt_prop";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_isqrt_progbin_def;

val riscv_pre_1_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_1_def;
val riscv_post_1_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_1_def;

val riscv_pre_2_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_2_def;
val riscv_post_2_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_2_def;

val riscv_pre_3_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_pre_3_def;
val riscv_post_3_loop_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_3_loop_def;
val riscv_post_3_ret_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_isqrt_post_3_ret_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_isqrt_1_thm =
 get_riscv_contract_sing
  bspec_cont_isqrt_1
  progbin_tm riscv_pre_1_tm riscv_post_1_tm
  bir_isqrt_prog_def
  [bspec_isqrt_pre_1_def]
  bspec_isqrt_pre_1_def isqrt_riscv_pre_1_imp_bspec_pre_1_thm
  [bspec_isqrt_post_1_def] isqrt_riscv_post_1_imp_bspec_post_1_thm
  bir_isqrt_riscv_lift_THM;

val riscv_cont_isqrt_2_thm =
 get_riscv_contract_sing
  bspec_cont_isqrt_2
  progbin_tm riscv_pre_2_tm riscv_post_2_tm
  bir_isqrt_prog_def
  [bspec_isqrt_pre_2_def]
  bspec_isqrt_pre_2_def isqrt_riscv_pre_2_imp_bspec_pre_2_thm
  [bspec_isqrt_post_2_def] isqrt_riscv_post_2_imp_bspec_post_2_thm
  bir_isqrt_riscv_lift_THM;

val _ = export_theory ();
