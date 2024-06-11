open HolKernel boolLib Parse bossLib;

open markerTheory;

open distribute_generic_stuffLib;

open bir_bool_expSyntax;
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

open incrTheory;

open distribute_generic_stuffTheory;

val _ = new_theory "incr_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition incr_init_addr_def:
 incr_init_addr : word64 = 0x00w
End

Definition incr_end_addr_def:
 incr_end_addr : word64 = 0x04w
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_incr_pre_def:
 riscv_incr_pre (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_incr_post_def:
 riscv_incr_post (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x + 1w)
End

(* --------------- *)
(* HL BIR contract *)
(* --------------- *)

Definition bir_incr_pre_def:
 bir_incr_pre (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bir_incr_post_def:
 bir_incr_post (x:word64) : bir_exp_t =
  BExp_BinPred
   BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (x + 1w)))
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

Definition bspec_incr_pre_def:
 bspec_incr_pre (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bspec_incr_post_def:
 bspec_incr_post (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 x)) (BExp_Const (Imm64 1w)))
End

(* -------------------------------------- *)
(* Connecting RISC-V and HL BIR contracts *)
(* -------------------------------------- *)

Theorem incr_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir (riscv_incr_pre pre_x10) (bir_incr_pre pre_x10)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_incr_pre_def,bir_incr_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

Theorem incr_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv (riscv_incr_post pre_x10) (\l. bir_incr_post pre_x10) ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_incr_post_def,bir_incr_post_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Q.ABBREV_TAC `g = ?z. f "x10" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def] >>
   fs [Abbrev_def] >>
   `bir_eval_bin_pred BIExp_Equal (SOME z)
     (SOME (BVal_Imm (Imm64 (pre_x10 + 1w)))) = SOME bir_val_true`
    by METIS_TAC [] >>   
   Cases_on `z` >> fs [type_of_bir_val_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_pred_def,bir_immTheory.bool2b_def,bir_val_true_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_def] >>
   Q.ABBREV_TAC `bb = bir_bin_pred BIExp_Equal b' (Imm64 (pre_x10 + 1w))` >>
   Cases_on `bb` >> fs [] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_Equal_REWR] >> 
   FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

(* ------------------------------------- *)
(* Connecting HL BIR and BSPEC contracts *)
(* ------------------------------------- *)

Theorem incr_bir_pre_imp_bspec_pre_thm[local]:
 bir_exp_is_taut
  (bir_exp_imp (bir_incr_pre pre_x10) (bspec_incr_pre pre_x10))
Proof
 rw [prove_exp_is_taut ``bir_exp_imp (bir_incr_pre pre_x10) (bspec_incr_pre pre_x10)``]
QED

val incr_bir_pre_imp_bspec_pre_eq_thm =
 computeLib.RESTR_EVAL_CONV [``bir_exp_is_taut``,``bir_incr_pre``,``bspec_incr_pre``]
  (concl incr_bir_pre_imp_bspec_pre_thm);

Theorem incr_bir_pre_imp_bspec_pre:
 ^((snd o dest_eq o concl) incr_bir_pre_imp_bspec_pre_eq_thm)
Proof
 rw [GSYM incr_bir_pre_imp_bspec_pre_eq_thm] >>
 ACCEPT_TAC incr_bir_pre_imp_bspec_pre_thm
QED

Theorem incr_bspec_post_imp_bir_post_thm[local]:
 bir_exp_is_taut
  (bir_exp_imp (bspec_incr_post pre_x10) (bir_incr_post pre_x10))
Proof
 rw [prove_exp_is_taut ``bir_exp_imp (bspec_incr_post pre_x10) (bir_incr_post pre_x10)``]
QED

val incr_bspec_post_imp_bir_post_eq_thm =
 computeLib.RESTR_EVAL_CONV [``bir_exp_is_taut``,``bspec_incr_post``,``bir_incr_post``]
 (concl incr_bspec_post_imp_bir_post_thm);

Theorem incr_bspec_post_imp_bir_post:
 ^((snd o dest_eq o concl) incr_bspec_post_imp_bir_post_eq_thm)
Proof
 rw [GSYM incr_bspec_post_imp_bir_post_eq_thm] >>
 ACCEPT_TAC incr_bspec_post_imp_bir_post_thm
QED

val _ = export_theory ();
