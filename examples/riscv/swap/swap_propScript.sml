open HolKernel boolLib Parse bossLib;

open markerTheory;

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

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open swapTheory;
open swap_specTheory;
open swap_symb_transfTheory;

val _ = new_theory "swap_prop";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_swap_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_swap_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_swap_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_swap_thm =
 get_riscv_contract_sing
  bspec_cont_swap
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_swap_prog_def
  [bspec_swap_pre_def]
  bspec_swap_pre_def swap_riscv_pre_imp_bspec_pre_thm
  [bspec_swap_post_def] swap_riscv_post_imp_bspec_post_thm
  bir_swap_riscv_lift_THM;

Theorem riscv_cont_swap:
 riscv_cont bir_swap_progbin swap_init_addr {swap_end_addr}
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
  (riscv_swap_post pre_x10 pre_x11 pre_x10_deref pre_x11_deref)
Proof
 rw [swap_init_addr_def,swap_end_addr_def] >>
 ACCEPT_TAC riscv_cont_swap_thm
QED

(* TODO: look at this, the assumptions are false, the composition is wrong *)
Theorem riscv_cont_swap_fixed = (EVAL o fst o dest_imp o concl o DISCH_ALL) riscv_cont_swap;

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_CONV [``riscv_weak_trs``] (concl riscv_cont_swap);

Theorem riscv_cont_swap_full:
  !pre_x10 pre_x11 pre_x10_deref pre_x11_deref. ^((snd o dest_eq o concl) readable_thm)
Proof
 METIS_TAC [GEN_ALL (REWRITE_RULE [readable_thm] riscv_cont_swap)]
QED
(* TODO: why does the Theorem/prove primitive allow assumptions like this?!?! it should just fail or run forever instead *)

val _ = export_theory ();
