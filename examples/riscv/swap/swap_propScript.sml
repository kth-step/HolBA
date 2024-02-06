open HolKernel Parse bossLib;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open swapTheory;

val _ = new_theory "swap_prop";

val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_swap_prog``;

(el 1)blocks;
(el 2)blocks;

bir_swap_riscv_lift_THM;

val _ = export_theory ();
