open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open swapTheory;
open swap_spec_riscvTheory;
open swap_spec_birTheory;
open swap_symb_execTheory;

val _ = new_theory "swap_symb_transf";

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val bir_cont_thm =
 bir_symb_transfer_thm
  bir_swap_prog_def
  swap_init_addr_def swap_end_addr_def
  riscv_swap_pre_bir_def riscv_swap_post_bir_def
  swap_birenvtyl_def swap_prog_vars_list_def
  swap_symb_analysis_thm NONE swap_prog_vars_thm;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bir_cont_thm);

Theorem bir_cont_swap = bir_cont_thm

val _ = export_theory ();
