(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

open bir_prog_add_regTheory;

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
