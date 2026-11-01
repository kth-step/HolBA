open HolKernel boolLib Parse bossLib;

open markerTheory;

open holba_auxiliaryTheory;

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

open bslSyntax;

val _ = new_theory "update_sat_spec_bir";

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_update_sat_pre_tm = bandl [
  bslt (bminus (bchsign (bconst64 2147483647), bconst64 1), bconstvar64 "pre_x2"),

  bslt (bconstvar64 "pre_x2", bconstvar64 "pre_x3"),

  bsle (bconstvar64 "pre_x2", bconstvar64 "pre_x1"),

  bsle (bconstvar64 "pre_x1", bconstvar64 "pre_x3"),

  bslt (bden (bvarimm64 "R3"), bconst64 2147483647),

  beq (bden (bvarimm64 "R3"), bconstvar64 "pre_x3"),

  beq (bden (bvarimm64 "R2"), bconstvar64 "pre_x2"),

  beq (bden (bvarimm64 "R1"), bconstvar64 "pre_x1"),

  beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x0")
];

Definition bspec_update_sat_pre_def:
 bspec_update_sat_pre (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_update_sat_pre_tm
End

val bspec_update_sat_post_or_1_tm = borl [
  bnot (band (beq (bconstvar64 "pre_x0", bconst64 0),
   bslt (bminus (bconstvar64 "pre_x1", bconst64 1), bconstvar64 "pre_x2"))),

  beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x2")
];

val bspec_update_sat_post_or_2_tm = borl [
  bnot (band (beq (bconstvar64 "pre_x0", bconst64 0),
   bsle (bconstvar64 "pre_x2", bminus (bconstvar64 "pre_x1", bconst64 1)))),

  beq (bden (bvarimm64 "R0"),
   bminus (bconstvar64 "pre_x1", bconst64 1))
];

val bspec_update_sat_post_or_3_tm = borl [
  bnot (band (bnot (beq (bconstvar64 "pre_x0", bconst64 0)),
   bslt (bconstvar64 "pre_x3", bplus (bconstvar64 "pre_x1", bconst64 1)))),

   beq (bden (bvarimm64 "R0"), bconstvar64 "pre_x3")
];

val bspec_update_sat_post_or_4_tm = borl [
  bnot (band (bnot (beq (bconstvar64 "pre_x0", bconst64 0)),
   bsle (bplus (bconstvar64 "pre_x1", bconst64 1), bconstvar64 "pre_x3"))),

   beq (bden (bvarimm64 "R0"),
    bplus (bconstvar64 "pre_x1", bconst64 1))
];

val bspec_update_sat_post_tm = bandl [
  bspec_update_sat_post_or_1_tm,
  bspec_update_sat_post_or_2_tm,
  bspec_update_sat_post_or_3_tm,
  bspec_update_sat_post_or_4_tm
];

Definition bspec_update_sat_post_def:
 bspec_update_sat_post (pre_x0:word64) (pre_x1:word64) (pre_x2:word64) (pre_x3:word64) : bir_exp_t =
  ^bspec_update_sat_post_tm
End

(* ------------------------------------ *)
(* Connecting ARMv8 and BSPEC contracts *)
(* ------------------------------------ *)

Theorem update_sat_arm8_pre_imp_bspec_pre_thm:
  bir_pre_arm8_to_bir
   (arm8_update_sat_pre pre_x0 pre_x1 pre_x2 pre_x3)
   (bspec_update_sat_pre pre_x0 pre_x1 pre_x2 pre_x3)
Proof
 rw [bir_pre_arm8_to_bir_def,arm8_update_sat_pre_def,bspec_update_sat_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   arm8_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,
   bir_envTheory.bir_env_lookup_def,
   bir_val_TF_bool2b_DEF
  ] >>

  rw []
QED

Theorem update_sat_arm8_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_arm8
  (arm8_update_sat_post pre_x0 pre_x1 pre_x2 pre_x3)
  (\l. bspec_update_sat_post pre_x0 pre_x1 pre_x2 pre_x3) ls
Proof
 once_rewrite_tac [bir_post_bir_to_arm8_def,bspec_update_sat_post_def] >>
 once_rewrite_tac [bspec_update_sat_post_def] >>
 once_rewrite_tac [bspec_update_sat_post_def] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>

 Q.ABBREV_TAC `g = ?z. f "R0" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>

 Cases_on `g` >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   fs [Abbrev_def] >>
   Cases_on `z` >> fs [type_of_bir_val_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def,bir_immTheory.bool2b_def,bir_val_true_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>
   once_rewrite_tac [arm8_update_sat_post_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [arm8_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
    bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
   rw [] >> fs [if_bool_1w]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

val _ = export_theory ();
