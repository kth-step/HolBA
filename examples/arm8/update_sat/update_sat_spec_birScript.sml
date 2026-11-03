open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_arm8_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

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

open update_sat_spec_arm8Theory;

open arm8_bir_condLib;

val _ = new_theory "update_sat_spec_bir";

(* ------------------------------------------------- *)
(* BSPEC contract, translated from the ARMv8 contract *)
(* ------------------------------------------------- *)

(* Defines bspec_update_sat_pre and bspec_update_sat_post *)

val (_, update_sat_arm8_pre_imp_bspec_pre) =
 arm8_pre_to_bir arm8_update_sat_pre_def;

val (_, update_sat_arm8_post_imp_bspec_post) =
 arm8_post_to_bir arm8_update_sat_post_def;

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem update_sat_arm8_pre_imp_bspec_pre_thm = update_sat_arm8_pre_imp_bspec_pre

Theorem update_sat_arm8_post_imp_bspec_post_thm = update_sat_arm8_post_imp_bspec_post

val _ = export_theory ();
