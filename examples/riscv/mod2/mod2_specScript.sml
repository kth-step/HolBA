open HolKernel boolLib Parse bossLib;

open markerTheory;

open distribute_generic_stuffLib;

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

open bir_env_oldTheory;
open bir_program_varsTheory;

open mod2Theory;

open distribute_generic_stuffTheory;

val _ = new_theory "mod2_spec";

(* --------------- *)
(* HLSPEC          *)
(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_mod2_pre_def:
 riscv_mod2_pre x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w x)
End

Definition riscv_mod2_post_def:
 riscv_mod2_post x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w (x MOD 2))
End

(* ------------ *)
(* HLSPEC       *)
(* ------------ *)
(* BIR contract *)
(* ------------ *)

Definition bir_mod2_pre_def:
  bir_mod2_pre x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w x)))
End

Definition bir_mod2_post_def:
 bir_mod2_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w (x MOD 2))))
End

(* ------------ *)
(* BSPEC        *)
(* ------------ *)
(* BIR contract *)
(* ------------ *)

Definition bspec_mod2_pre_def:
  bspec_mod2_pre x : bir_exp_t =
  BExp_BinPred
   BIExp_Equal
   (BExp_Den (BVar "x10" (BType_Imm Bit64)))
   (BExp_Const (Imm64 x))
End

Definition bspec_mod2_post_def:
 bspec_mod2_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_And (BExp_Const (Imm64 x)) (BExp_Const (Imm64 1w)))
End

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem mod2_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir (riscv_mod2_pre pre_x10) (bir_mod2_pre pre_x10)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_mod2_pre_def,bir_mod2_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

(* FIXME: boilerplate *)
Theorem mod2_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_mod2_post pre_x10) (\l. bir_mod2_post pre_x10) ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_mod2_post_def,bir_mod2_post_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Q.ABBREV_TAC `g = ?z. f "x10" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   fs [Abbrev_def] >>
   `bir_eval_bin_pred BIExp_Equal (SOME z)
     (SOME (BVal_Imm (Imm64 (n2w (pre_x10 MOD 2))))) = SOME bir_val_true`
    by METIS_TAC [] >>
   Cases_on `z` >> fs [type_of_bir_val_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def,bir_immTheory.bool2b_def,bir_val_true_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_def] >>
   Q.ABBREV_TAC `bb = bir_bin_pred BIExp_Equal b' (Imm64 (n2w (pre_x10 MOD 2)))` >>
   Cases_on `bb` >> fs [] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

(* ----------------------------------------- *)
(* Connecting HLSPEC BIR and BSPEC contracts *)
(* ----------------------------------------- *)

val mod2_bir_pre_imp_bspec_pre_thm =
 prove_exp_is_taut ``BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bir_mod2_pre (w2n pre_x10)))
   (bspec_mod2_pre pre_x10)``;

Theorem mod2_bir_pre_imp_bspec_pre:
 bir_exp_is_taut (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bir_mod2_pre (w2n pre_x10)))
   (bspec_mod2_pre pre_x10))
Proof
 rw [mod2_bir_pre_imp_bspec_pre_thm]
QED

(*
val mod2_bspec_post_imp_bir_post_thm =
 prove_exp_is_taut ``BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bspec_mod2_post pre_x10))
    (bir_mod2_post (w2n pre_x10))``;

Theorem mod2_bspec_post_imp_bir_post:
 bir_exp_is_taut (BExp_BinExp BIExp_Or
   (BExp_UnaryExp BIExp_Not (bspec_mod2_post pre_x10))
    (bir_mod2_post pre_x10))
Proof
 rw [mod2_bspec_post_imp_bir_post_thm]
QED
*)

val _ = export_theory ();