open HolKernel Parse;
open examplesBinaryTheory;

val _ = new_theory "tutorial_lift";

bir_is_lifted_prog_def;
val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_add_reg_prog``;
(el 1)blocks;
(el 2)blocks;
(el ((0x3c div 4)+1))blocks;
(el ((0x40 div 4)+1))blocks;
(el ((0x4c div 4)+1))blocks;

bir_add_reg_arm8_lift_THM;
bir_exec_to_addr_label_def;
bir_lifting_machinesTheory.arm8_bmr_rel_EVAL;
bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC;

val _ = export_theory();
