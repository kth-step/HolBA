open HolKernel boolLib Parse bossLib;

open markerTheory wordsTheory wordsLib;

open addressTheory;

open holba_auxiliaryTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
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

open HolBACoreSimps;

open chachaTheory;
open chacha_specTheory;
open chacha_symb_transf_quarter_roundTheory;

val _ = new_theory "chacha_quarter_round_prop";

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem chacha_line_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_chacha_line_pre pre_a pre_b pre_d)
  (bspec_chacha_line_pre pre_a pre_b pre_d)
Proof 
 rw [bir_pre_riscv_to_bir_def,riscv_chacha_line_pre_def,bspec_chacha_line_pre_def] >-
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

Theorem chacha_line_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_chacha_line_post pre_a pre_b pre_d)
   (\l. (bspec_chacha_line_post pre_a pre_b pre_d))
   ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_chacha_line_post_def,bspec_chacha_line_post_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >> 
 Q.ABBREV_TAC `g = ?z. f "x20" = SOME z /\ BType_Imm Bit64 = type_of_bir_val z` >>
 Cases_on `g` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 fs [Abbrev_def] >>
 fs [] >>
 Cases_on `z` >> fs [type_of_bir_val_def] >>

 Q.ABBREV_TAC `g = ?z. f "x10" = SOME z /\ type_of_bir_val z = BType_Imm Bit64` >>
 Cases_on `g` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
 fs [Abbrev_def] >>
 fs [] >>
 Cases_on `z` >> fs [type_of_bir_val_def] >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_cast_def,bir_cast_def,bool2b_def,bool2w_def,b2n_def] >>

 Cases_on `b'` >> fs [type_of_bir_imm_def] >>
 
 Cases_on `b''` >> fs [type_of_bir_imm_def] >>
 
 fs [bir_val_true_def,b2n_def] >>

 Cases_on `n2w (w2n c) = pre_a + pre_b` >> fs [] >>

 Cases_on `n2w (w2n c') =
           pre_a ≪ 16 + pre_b ≪ 16 ⊕ pre_d ≪ 16 ‖
           pre_d ⋙ 16 ⊕ (pre_a + pre_b) ⋙ 16` >> fs [] >>

 rw [riscv_chacha_line_exp_fst_def,riscv_chacha_line_exp_snd_def] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 rw []
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_line_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_line_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha_line_thm =
 get_riscv_contract
  bspec_cont_chacha_line
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha_prog_def
  [bspec_chacha_line_pre_def]
  bspec_chacha_line_pre_def chacha_line_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha_line_post_def] chacha_line_riscv_post_imp_bspec_post_thm
  bir_chacha_riscv_lift_THM;

Theorem riscv_cont_chacha_line:
 riscv_cont bir_chacha_progbin chacha_line_init_addr {chacha_line_end_addr}
 (riscv_chacha_line_pre pre_a pre_b pre_d)
 (riscv_chacha_line_post pre_a pre_b pre_d)
Proof
 rw [chacha_line_init_addr_def,chacha_line_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha_line_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha_line;
Theorem riscv_cont_chacha_line_full = GEN_ALL readable_thm;

val _ = export_theory ();
