open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;
open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

val _ = new_theory "ifelse_spec";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

Definition ifelse_init_addr_def:
 ifelse_init_addr : word64 = 0x10488w
End

Definition ifelse_end_addr_def:
 ifelse_end_addr : word64 = 0x104bcw
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

val bspec_ifelse_keysetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_ifelse_pre_def:
 bspec_ifelse_pre : bir_exp_t =
  ^bspec_ifelse_keysetup_pre_tm
End

val _ = export_theory ();
