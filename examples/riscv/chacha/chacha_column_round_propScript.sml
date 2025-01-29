open HolKernel boolLib Parse bossLib;

open markerTheory wordsTheory wordsLib;

open addressTheory;

open holba_auxiliaryTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open birs_auxTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open HolBACoreSimps;
open bir_extra_expsTheory;

open chachaTheory;
open chacha_specTheory;
open chacha_symb_transf_column_roundTheory;

val _ = new_theory "chacha_column_round_prop";

Theorem if_bool_1w[local]:
 !b. ((if b then 1w else 0w) = 1w) = b
Proof
 rw []
QED

Theorem bir_eval_bin_pred_eq[local]:
 !f w reg.
 (bir_eval_bin_pred BIExp_Equal
  (if (∃z. f reg = SOME z ∧ BType_Imm Bit64 = type_of_bir_val z)
  then f reg else NONE) (SOME (BVal_Imm (Imm64 w))) = SOME bir_val_true) <=>
 (f reg = SOME (BVal_Imm (Imm64 w)))
Proof
 REPEAT STRIP_TAC >>
 Q.ABBREV_TAC `g = ?z. f reg' = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 fs [Abbrev_def] >-
  (Cases_on `z` >> fs [type_of_bir_val_def] >>
   Cases_on `b` >> fs [type_of_bir_imm_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def,bool2w_def] >>
   Cases_on `c = w` >> fs [bir_val_true_def]) >>
 STRIP_TAC >>
 fs [type_of_bir_val_def,type_of_bir_imm_def]
QED

Theorem bir_eval_bin_pred_lowcast_eq[local]:
!f w reg.
(bir_eval_bin_pred BIExp_Equal
 (bir_eval_cast BIExp_LowCast
   (if (?z. f reg = SOME z /\ BType_Imm Bit64 = type_of_bir_val z)
    then f reg else NONE) Bit32) (SOME (BVal_Imm (Imm32 w))) =
 SOME bir_val_true) 
 <=>
 (?(z:word64). f reg = SOME (BVal_Imm (Imm64 z)) /\ n2w (w2n z) = w)
Proof
 REPEAT STRIP_TAC >>
 Q.ABBREV_TAC `g = ?z. f reg' = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 fs [Abbrev_def] >-
  (Cases_on `z` >> fs [type_of_bir_val_def] >>
   Cases_on `b` >> fs [type_of_bir_imm_def] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def,bool2w_def,w2w_n2w_w2n_64_32] >>
   rw [if_bool_1w,bir_val_true_def]) >>
 rw [] >>
 fs [type_of_bir_val_def,type_of_bir_imm_def]
QED

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem chacha_column_round_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
  (bspec_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof 
 rw [bir_pre_riscv_to_bir_def,riscv_chacha_column_round_pre_def,bspec_chacha_column_round_pre_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF,
  bool2b_def,
  bool2w_def,
  w2w_n2w_w2n_64_32
 ] >>
 EVAL_TAC
QED

Theorem chacha_column_round_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
     pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
   (\l. (bspec_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
          pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15))
   ls
Proof
 once_rewrite_tac [bir_post_bir_to_riscv_def,bspec_chacha_column_round_post_def] >>
 once_rewrite_tac [bspec_chacha_column_round_post_def] >>
 once_rewrite_tac [bspec_chacha_column_round_post_def] >>

 fs [GSYM bir_and_equiv] >>

 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >>

 rw [bir_eval_bin_pred_lowcast_eq] >>

 rw [riscv_chacha_column_round_post_def,riscv_chacha_quarter_round_exprs_def,
  riscv_chacha_line_exp_fst_def,riscv_chacha_line_exp_snd_def,riscv_chacha_column_round_exprs_def] >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bool2b_def,bool2w_def,b2n_def,bir_val_true_def,
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >>
 
 rw [] >> fs [if_bool_1w]
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_column_round_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_column_round_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha_column_round_thm =
 get_riscv_contract
  bspec_cont_chacha_column_round
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha_prog_def
  [bspec_chacha_column_round_pre_def]
  bspec_chacha_column_round_pre_def chacha_column_round_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha_column_round_post_def] chacha_column_round_riscv_post_imp_bspec_post_thm
  bir_chacha_riscv_lift_THM;

Theorem riscv_cont_chacha_column_round:
 riscv_cont bir_chacha_progbin chacha_column_round_init_addr {chacha_column_round_end_addr}
 (riscv_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 rw [chacha_column_round_init_addr_def,chacha_column_round_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha_column_round_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha_column_round;
Theorem riscv_cont_chacha_column_round_full = GEN_ALL readable_thm;

val _ = export_theory ();
