open HolKernel boolLib Parse bossLib;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;
open bir_tsTheory bir_bool_expTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open swapTheory;

val _ = new_theory "swap_prop";

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_dword (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_dword (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

Definition riscv_swap_pre_def:
 riscv_swap_pre (m : riscv_state) = T
End

Definition riscv_swap_post_def:
 riscv_swap_post (m : riscv_state) = T
End

Definition bir_swap_pre_def:
  bir_swap_pre : bir_exp_t = bir_exp_true
End

Definition bir_swap_post_def:
 bir_swap_post : bir_exp_t = bir_exp_true
End

Theorem swap_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir riscv_swap_pre bir_swap_pre
Proof
 EVAL_TAC >> rw []
QED

Theorem swap_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv riscv_swap_post (\l. bir_swap_post) ls
Proof
 EVAL_TAC >> rw []
QED

Theorem bir_cont_swap:
  bir_cont bir_swap_prog bir_exp_true
   (BL_Address (Imm64 0w)) {BL_Address (Imm64 20w)} {}
  bir_swap_pre
  (\l. if l = BL_Address (Imm64 20w) then bir_swap_post else bir_exp_false)
Proof
 cheat
QED

(* For debugging:

val bir_ct = bir_cont_swap;
val prog_bin = ``bir_swap_progbin``;
val riscv_pre = ``riscv_swap_pre``;
val riscv_post = ``riscv_swap_post``;
val bir_prog_def = bir_swap_prog_def;
val bir_pre_defs = [bir_swap_pre_def]
val bir_pre1_def = bir_swap_pre_def;
val riscv_pre_imp_bir_pre_thm = swap_riscv_pre_imp_bir_pre_thm;
val bir_post_defs = [bir_swap_post_def];
val riscv_post_imp_bir_post_thm = swap_riscv_post_imp_bir_post_thm;
val bir_is_lifted_prog_thm = bir_swap_riscv_lift_THM;
*)

val riscv_swap_contract_thm = save_thm("riscv_swap_contract_thm",
 get_riscv_contract_sing
  bir_cont_swap
  ``bir_swap_progbin``
  ``riscv_swap_pre`` ``riscv_swap_post`` bir_swap_prog_def
  [bir_swap_pre_def]
  bir_swap_pre_def swap_riscv_pre_imp_bir_pre_thm
  [bir_swap_post_def] swap_riscv_post_imp_bir_post_thm
  bir_swap_riscv_lift_THM);

val _ = export_theory ();
