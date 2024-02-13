open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open swapTheory;

val _ = new_theory "swap_prop";

val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_swap_prog``;

(el 1)blocks;
(el 2)blocks;

bir_swap_riscv_lift_THM;

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_word (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_word ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_word (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_word ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

(* run symbolic execution of BIR to get two symbolic states  *)
(* connect this back to the riscv state via the lifting theorem *)

val _ = export_theory ();
