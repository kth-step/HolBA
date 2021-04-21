open HolKernel bossLib boolLib Parse m0_stepLib;
open examplesBinaryTheory bir_driver_condTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory bir_bool_expTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory bir_valuesTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps bslSyntax;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

(*
open driver_stateTheory driver_callTheory driver_writeTheory driver_readTheory driver_checkTheory driver_relationTheory;
*) 

val _ = new_theory "bir_driver_wp";

(* necessary arguments *)
val prefix = "ningdriver_prog_B_";

val prog_tm = (lhs o concl) bir_ningdriver_prog_def;

val first_block_label_tm = ``BL_Address (Imm64 0x40w)``; (* 2c *)

val ending_set = ``{BL_Address (Imm64 0x60w)}``; (* 3c *) 

val postcond_tm = ``bir_driver_segB_post v``;

val defs = [bir_ningdriver_prog_def, bir_driver_segB_postcond_def,
            bir_driver_segB_post_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_ningdriver_prog_B_ht, bir_ningdriver_prog_B_wp_tm) =
     bir_obtain_ht prog_tm first_block_label_tm
                   ending_set ending_set_to_sml_list
                   postcond_tm postcond_exp_from_label
                   prefix defs;

val _ = export_theory();
