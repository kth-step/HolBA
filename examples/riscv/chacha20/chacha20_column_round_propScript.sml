open HolKernel boolLib Parse bossLib;

open markerTheory wordsTheory wordsLib;

open addressTheory;

open holba_auxiliaryTheory holba_auxiliaryLib;

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
open chacha20_spec_riscvTheory;
open chacha20_spec_birTheory;
open chacha20_column_round_symb_transfTheory;

val _ = new_theory "chacha20_column_round_prop";

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha20_column_round_excl_thm =
 get_riscv_contract_thm
  bspec_cont_chacha20_column_round_excl
  chacha20_column_round_init_addr_def
  [chacha20_column_round_end_addr_def, chacha20_double_round_end_addr_def]
  bir_chacha20_progbin_def
  riscv_chacha20_column_round_pre_def riscv_chacha20_column_round_post_def
  bir_chacha20_prog_def
  [bspec_chacha20_column_round_pre_def]
  bspec_chacha20_column_round_pre_def chacha20_column_round_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha20_column_round_post_def,
   chacha20_column_round_end_addr_def, chacha20_double_round_end_addr_def]
  chacha20_column_round_riscv_post_imp_bspec_post_thm
  bir_chacha20_riscv_lift_THM;

(* column round contract that also excludes the end of the double round,
   for sequential composition with the diagonal round *)
Theorem riscv_cont_chacha20_column_round_excl:
 riscv_cont bir_chacha20_progbin chacha20_column_round_init_addr
  {chacha20_column_round_end_addr; chacha20_double_round_end_addr}
 (riscv_chacha20_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha20_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 ACCEPT_TAC riscv_cont_chacha20_column_round_excl_thm
QED

(* -------------------------------------- *)
(* Column round contract without exclusion *)
(* -------------------------------------- *)

Theorem riscv_cont_chacha20_column_round:
 riscv_cont bir_chacha20_progbin chacha20_column_round_init_addr {chacha20_column_round_end_addr}
 (riscv_chacha20_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha20_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 QINST_IRULE [("ls2", `{chacha20_double_round_end_addr}`)] riscv_cont_subset_rule >>
 conj_tac >- (
  rw [riscv_chacha20_column_round_post_def] >>
  pairarg_tac >>
  fs [chacha20_column_round_end_addr_def, chacha20_double_round_end_addr_def]
 ) >>
 REWRITE_TAC [GSYM INSERT_SING_UNION] >>
 ACCEPT_TAC riscv_cont_chacha20_column_round_excl
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha20_column_round;
Theorem riscv_cont_chacha20_column_round_full = GEN_ALL readable_thm;

val _ = export_theory ();
