open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open tutorial_smtSupportLib;
open bir_symbLib;
open birs_smtLib;

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

open distribute_generic_stuffTheory;

open mod2_memTheory;

val _ = new_theory "mod2_mem_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition mod2_mem_init_addr_def:
 mod2_mem_init_addr : word64 = 0x00w
End

Definition mod2_mem_end_addr_def:
 mod2_mem_end_addr : word64 = 0x08w
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_mod2_mem_pre_def:
 riscv_mod2_mem_pre (pre_x10:word64) (pre_x10_deref:word64) (m:riscv_state) : bool =
  (^(mem_addrs_aligned_prog_disj_riscv_tm "pre_x10") /\
   m.c_gpr m.procID 10w = pre_x10 /\
   riscv_mem_load_dword m.MEM8 pre_x10 = pre_x10_deref)
End

Definition riscv_mod2_mem_post_def:
 riscv_mod2_mem_post (pre_x10:word64) (pre_x10_deref:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w ((w2n pre_x10_deref) MOD 2))
End

(* --------------- *)
(* HL BIR contract *)
(* --------------- *)

val bir_mod2_mem_pre_tm = bslSyntax.bandl [
 mem_addrs_aligned_prog_disj_bir_tm "x10",
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
 ``BExp_BinPred
      BIExp_Equal
      (BExp_Load
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "x10" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 pre_x10_deref))``
];

Definition bir_mod2_mem_pre_def:
  bir_mod2_mem_pre (pre_x10:word64) (pre_x10_deref:word64) : bir_exp_t =
   ^bir_mod2_mem_pre_tm
End

Definition bir_mod2_mem_post_def:
 bir_mod2_mem_post (pre_x10:word64) (pre_x10_deref:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w ((w2n pre_x10_deref) MOD 2))))
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

Definition bspec_mod2_mem_pre_def:
  bspec_mod2_mem_pre (pre_x10:word64) (pre_x10_deref:word64) : bir_exp_t =
   ^bir_mod2_mem_pre_tm
End

Definition bspec_mod2_mem_post_def:
 bspec_mod2_mem_post (pre_x10:word64) (pre_x10_deref:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_And (BExp_Const (Imm64 pre_x10_deref)) (BExp_Const (Imm64 1w)))
End

(* -------------------------------------- *)
(* Connecting RISC-V and HL BIR contracts *)
(* -------------------------------------- *)

Theorem mod2_mem_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_mod2_mem_pre pre_x10 pre_x10_deref)
  (bir_mod2_mem_pre pre_x10 pre_x10_deref)
Proof
 cheat
QED

Theorem mod2_mem_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv
  (riscv_mod2_mem_post pre_x10 pre_x10_deref)
  (\l. bir_mod2_mem_post pre_x10 pre_x10_deref) ls
Proof
 cheat
QED

(* ------------------------------------- *)
(* Connecting HL BIR and BSPEC contracts *)
(* ------------------------------------- *)

Theorem mod2_wand_n2w_w2n[local]:
 !x. 1w && x = n2w ((w2n x) MOD 2)
Proof
 STRIP_TAC >>
 MP_TAC (Q.SPECL [`1`, `w2n x`] WORD_AND_EXP_SUB1) >>
 rw []
QED

Theorem mod2_mem_bir_pre_imp_bspec_pre_thm[local]:
 bir_exp_is_taut
  (bir_exp_imp (bir_mod2_mem_pre pre_x10 pre_x10_deref)
    (bspec_mod2_mem_pre pre_x10 pre_x10_deref))
Proof
 rw [prove_exp_is_taut ``bir_exp_imp
  (bir_mod2_mem_pre pre_x10 pre_x10_deref) (bspec_mod2_mem_pre pre_x10 pre_x10_deref)``]
QED

val mod2_mem_bir_pre_imp_bspec_pre_eq_thm =
 computeLib.RESTR_EVAL_CONV [``bir_exp_is_taut``,``bir_mod2_mem_pre``,``bspec_mod2_mem_pre``]
  (concl mod2_mem_bir_pre_imp_bspec_pre_thm);

Theorem mod2_mem_bir_pre_imp_bspec_pre:
 ^((snd o dest_eq o concl) mod2_mem_bir_pre_imp_bspec_pre_eq_thm)
Proof
 rw [GSYM mod2_mem_bir_pre_imp_bspec_pre_eq_thm] >>
 ACCEPT_TAC mod2_mem_bir_pre_imp_bspec_pre_thm
QED

Theorem mod2_mem_bspec_post_imp_bir_post_thm[local]:
 bir_exp_is_taut
  (bir_exp_imp (bspec_mod2_mem_post pre_x10 pre_x10_deref)
   (bir_mod2_mem_post pre_x10 pre_x10_deref))
Proof
 rw [bir_exp_imp_def,bir_exp_or_def,bir_exp_not_def] >>
 rw [bspec_mod2_mem_post_def,bir_mod2_mem_post_def,bir_exp_is_taut_def,bir_is_bool_exp_REWRS] >-
  (rw [type_of_bir_exp_def,type_of_bir_imm_def,bir_type_is_Imm_def,bir_envTheory.bir_var_type_def]) >-
  (rw [type_of_bir_exp_def,type_of_bir_imm_def,bir_type_is_Imm_def,bir_envTheory.bir_var_type_def]) >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_env_oldTheory.bir_var_set_is_well_typed_INSERT] >>
   rw [bir_env_oldTheory.bir_var_set_is_well_typed_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_exp_def,bir_eval_unary_exp_def,bir_eval_bin_pred_def,
  bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_check_type_def] >>
 Cases_on `env` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_env_vars_are_initialised_def,bir_env_var_is_initialised_def] >>
 fs [bir_envTheory.bir_var_name_def] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 Cases_on `v'` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_REWRS] >>
 Cases_on `b` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>
 Cases_on `c` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def] >>
 rw [mod2_wand_n2w_w2n]
QED

val mod2_mem_bspec_post_imp_bir_post_eq_thm =
 computeLib.RESTR_EVAL_CONV [``bir_exp_is_taut``,``bspec_mod2_mem_post``,``bir_mod2_mem_post``]
 (concl mod2_mem_bspec_post_imp_bir_post_thm);

Theorem mod2_mem_bspec_post_imp_bir_post:
 ^((snd o dest_eq o concl) mod2_mem_bspec_post_imp_bir_post_eq_thm)
Proof
 rw [GSYM mod2_mem_bspec_post_imp_bir_post_eq_thm] >>
 ACCEPT_TAC mod2_mem_bspec_post_imp_bir_post_thm
QED

val _ = export_theory ();
