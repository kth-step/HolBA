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
open chacha20Theory;
open chacha20_specTheory;
open chacha20_diagonal_round_symb_transfTheory;

val _ = new_theory "chacha20_diagonal_round_prop";

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem chacha20_diagonal_round_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_chacha20_diagonal_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
  (bspec_chacha20_diagonal_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof 
 rw [bir_pre_riscv_to_bir_def,riscv_chacha20_diagonal_round_pre_def,bspec_chacha20_diagonal_round_pre_def] >-
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

Theorem chacha20_diagonal_round_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_chacha20_diagonal_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
     pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
   (\l. (bspec_chacha20_diagonal_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
          pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15))
   ls
Proof
 once_rewrite_tac [bir_post_bir_to_riscv_def,bspec_chacha20_diagonal_round_post_def] >>
 once_rewrite_tac [bspec_chacha20_diagonal_round_post_def] >>
 once_rewrite_tac [bspec_chacha20_diagonal_round_post_def] >>

 fs [GSYM bir_and_equiv] >>

 Cases_on `bs` >> Cases_on `b0` >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def
 ] >>

 rw [bir_eval_bin_pred_exists_64_lowcast_32_eq] >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_chacha20_diagonal_round_post_def,
  chacha_quarter_round_exprs_def,
  chacha_line_exp_fst_def,
  chacha_line_exp_snd_def,
  chacha_diagonal_round_exprs_def,

  riscv_bmr_rel_EVAL,
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bool2b_def,bool2w_def,b2n_def,bir_val_true_def
 ] >>
 
 rw [] >> fs [if_bool_1w]
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha20_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha20_diagonal_round_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha20_diagonal_round_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha20_diagonal_round_thm =
 get_riscv_contract
  bspec_cont_chacha20_diagonal_round
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha20_prog_def
  [bspec_chacha20_diagonal_round_pre_def]
  bspec_chacha20_diagonal_round_pre_def chacha20_diagonal_round_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha20_diagonal_round_post_def] chacha20_diagonal_round_riscv_post_imp_bspec_post_thm
  bir_chacha20_riscv_lift_THM;

Theorem riscv_cont_chacha20_diagonal_round:
 riscv_cont bir_chacha20_progbin chacha20_diagonal_round_init_addr {chacha20_diagonal_round_end_addr}
 (riscv_chacha20_diagonal_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha20_diagonal_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 rw [chacha20_diagonal_round_init_addr_def,chacha20_diagonal_round_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha20_diagonal_round_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha20_diagonal_round;
Theorem riscv_cont_chacha20_diagonal_round_full = GEN_ALL readable_thm;

val _ = export_theory ();
