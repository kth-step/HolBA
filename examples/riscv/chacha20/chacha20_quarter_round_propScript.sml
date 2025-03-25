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
open chacha20_quarter_round_symb_transfTheory;

val _ = new_theory "chacha20_quarter_round_prop";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha20_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha20_line_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha20_line_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha20_line_thm =
 get_riscv_contract
  bspec_cont_chacha20_line
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha20_prog_def
  [bspec_chacha20_line_pre_def]
  bspec_chacha20_line_pre_def chacha20_line_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha20_line_post_def] chacha20_line_riscv_post_imp_bspec_post_thm
  bir_chacha20_riscv_lift_THM;

Theorem riscv_cont_chacha20_line:
 riscv_cont bir_chacha20_progbin chacha20_line_init_addr {chacha20_line_end_addr}
 (riscv_chacha20_line_pre pre_a pre_b pre_d)
 (riscv_chacha20_line_post pre_a pre_b pre_d)
Proof
 rw [chacha20_line_init_addr_def,chacha20_line_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha20_line_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha20_line;
Theorem riscv_cont_chacha20_line_full = GEN_ALL readable_thm;

val _ = export_theory ();
