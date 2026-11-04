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
open chacha20_spec_riscvTheory;
open chacha20_spec_birTheory;
open chacha20_column_round_propTheory;
open chacha20_diagonal_round_propTheory;

val _ = new_theory "chacha20_double_round_prop";

(* ---------------------------------- *)
(* Composing column and diagonal round *)
(* ---------------------------------- *)

val pre_arr_vars = List.tabulate (16, fn i => mk_var ("pre_arr_" ^ Int.toString i, ``:word32``));
fun vars_named s = List.tabulate (16, fn i => mk_var (s ^ Int.toString i, ``:word32``));

(* diagonal round contract with the column round results as inputs *)
val riscv_cont_chacha20_diagonal_round_x =
 INST (ListPair.map (fn (v, x) => v |-> x) (pre_arr_vars, vars_named "x"))
  riscv_cont_chacha20_diagonal_round;

Theorem riscv_cont_chacha20_double_round:
 riscv_cont bir_chacha20_progbin chacha20_double_round_init_addr {chacha20_double_round_end_addr}
 (riscv_chacha20_double_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha20_double_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 `?x. chacha_column_round_exprs pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15 = x` by simp [] >>
 PairCases_on `x` >>
 `?y. chacha_diagonal_round_exprs x0 x1 x2 x3 x4 x5 x6 x7
   x8 x9 x10 x11 x12 x13 x14 x15 = y` by simp [] >>
 PairCases_on `y` >>
 `riscv_chacha20_double_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15 =
  riscv_chacha20_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15`
  by rw [FUN_EQ_THM, riscv_chacha20_double_round_pre_def, riscv_chacha20_column_round_pre_def] >>
 `riscv_chacha20_double_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15 =
  riscv_chacha20_diagonal_round_post x0 x1 x2 x3 x4 x5 x6 x7
   x8 x9 x10 x11 x12 x13 x14 x15`
  by fs [FUN_EQ_THM, riscv_chacha20_double_round_post_def, riscv_chacha20_diagonal_round_post_def,
         chacha_double_round_exprs_def] >>
 `chacha20_double_round_init_addr = chacha20_column_round_init_addr`
  by rw [chacha20_double_round_init_addr_def, chacha20_column_round_init_addr_def] >>
 `chacha20_column_round_end_addr = chacha20_diagonal_round_init_addr`
  by rw [chacha20_column_round_end_addr_def, chacha20_diagonal_round_init_addr_def] >>
 `chacha20_double_round_end_addr = chacha20_diagonal_round_end_addr`
  by rw [chacha20_double_round_end_addr_def, chacha20_diagonal_round_end_addr_def] >>
 ASM_REWRITE_TAC [] >>
 MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] riscv_cont_seq_rule) >>
 qexistsl_tac [`chacha20_diagonal_round_init_addr`,
  `riscv_chacha20_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
   pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15`,
  `riscv_chacha20_diagonal_round_pre x0 x1 x2 x3 x4 x5 x6 x7
   x8 x9 x10 x11 x12 x13 x14 x15`] >>
 rpt conj_tac >- (
  (* diagonal round end label is not its start label *)
  rw [chacha20_diagonal_round_init_addr_def, chacha20_diagonal_round_end_addr_def]
 ) >- (
  (* column round contract *)
  MP_TAC riscv_cont_chacha20_column_round_excl >>
  rw [chacha20_column_round_end_addr_def, chacha20_double_round_end_addr_def,
      chacha20_diagonal_round_init_addr_def]
 ) >- (
  (* column round postcondition implies diagonal round precondition *)
  fs [riscv_chacha20_column_round_post_def,
      riscv_chacha20_diagonal_round_pre_def] >>
  rw []
 ) >>
 (* diagonal round contract *)
 ACCEPT_TAC riscv_cont_chacha20_diagonal_round_x
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha20_double_round;
Theorem riscv_cont_chacha20_double_round_full = GEN_ALL readable_thm;

val _ = export_theory ();
