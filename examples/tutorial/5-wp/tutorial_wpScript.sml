open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open easy_noproof_wpLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory bir_bool_expTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory bir_valuesTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples: *)
open examplesBinaryTheory;
open tutorial_bir_to_armTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorial_wp";

(* You may install the BIR pretty printers to get syntax
 * highlighting for matching pairs of parantheses:

  val _ = bir_ppLib.install_bir_pretty_printers ();
  val _ = bir_ppLib.remove_bir_pretty_printers ();

*)

(* Common abbreviations:
 * WP = Weakest precondition
 * HT = Hoare triple
*)

(* TODO: Think about where to put these... *)


(******************************************************************)
(******************************************************************)

val prog_tm = (lhs o concl) bir_add_reg_prog_def;
(****************     (1) bir_add_reg_entry      ******************)
(* The HT with the WP for the loop entry of the add_reg program is
 * generated and proved here. *)
(* 1c -> 38 -> 3c -> 40 *)

(* This prefix is used inside bir_obtain_ht to define uniquely
 * named terms, as well as assigning these definitions to uniquely
 * named SML values. *)
val prefix = "add_reg_entry_";
(* This is the label of the "first block" in HT execution,
 * meaning the block at the beginning of which execution starts.  *)
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``; (* 28 *)
(* This is the Ending blocks of HT execution: the HT postcondition
 * (on the final state) is predicated on the state when these blocks
 * are reached. *)
val ending_set =  ``{BL_Address (Imm64 0x40w); BL_Address (Imm64 0x48w)}``; (* 64, 72 *)
(* postcond_tm is the postcondition of the HT to be generated and
 * proved, which is obtained from the contract definitions in
 * tutorial_bir_to_armTheory. *)
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x40w))
                        then bir_add_reg_contract_1_post
                        else bir_exp_false``;
(* defs is a list of theorems - typically definitions - which is
 * used internally in bir_obtain_ht. This always contains the
 * program definition, the postcondition definition, and all other
 * nested definitions needed to rewrite these to regular BIR
 * terms using only the syntax in the theory/bir directory of
 * HolBA. *)
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_1_post_def,
            bir_add_reg_I_def, bir_exp_false_def, BType_Bool_def];

(* Here, bir_obtain_ht is called with the above arguments.
 * bir_obtain_ht is a convenient wrapper function created for this
 * tutorial, which in turn uses functions from bir_wpLib to generate
 * and prove the HT with the following:
 *
 * Precondition: Obtained from the below by the WP predicate
 *               transformer semantics
 * Execution: From first_block_label_tm to last_block_label_tm
 * Postcondition: postcond_tm (the contractual postcondition)
 *
 * The return value is a tuple of a theorem stating this HT and
 * a list of theorems with definitions occuring inside the HT.
 * *)
val (bir_add_reg_entry_ht, bir_add_reg_entry_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;
(* By creating a definition and saving the HT as a theorem, we 
 * allow them to be exported to later theories. *)
val bir_add_reg_entry_wp_def =
  Define `bir_add_reg_entry_wp = ^(bir_add_reg_entry_wp_tm)`;
val _ = save_thm ("bir_add_reg_entry_ht", bir_add_reg_entry_ht);


(******************************************************************)
(*                        LOOP VARIANT                            *)
(******************************************************************)
(* While the invariant describes what properties the loop keeps, 
 * the loop variant describes something which strictly decreases
 * or increases to some fixed lower or upper point, respectively.
 *
 * The loop variant can help us prove that the loop terminates. The
 * HTs we need for this state that the variant is strictly
 * decreasing for every loop continuation, and reaches its bound
 * upon exit.
 *
 * Concretely, we will prove HTs similar to those with the loop
 * invariant, only that this time we want to show that a variant
 * is strictly decreasing, instead of that the invariant is kept.
 * The variant (here R2) must obey the following:
 * 
 * 1. Strictly decrease as the loop body is executed
 * 2. When its lowest value is reached (zero), the loop terminates
 *
 * Depending on the algebraic properties of a variant, we might
 * also require that the starting value is inside some valid range.
 * *)

(**************    (2)  bir_add_reg_loop_variant     *************)
(* The WP for the loop content is generated and proved here. This
 * is similar to (2) above. *)
(* 20 -> 24 -> 28 -> 2c -> 30 -> 34 -> 38 -> 3c -> 40 *)
val prefix = "add_reg_loop_variant_";
val first_block_label_tm = ``BL_Address (Imm64 0x20w)``;
val ending_set =  ``{BL_Address (Imm64 0x40w); BL_Address (Imm64 0x48w)}``; (* 64, 72 *)
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x40w))
                         then bir_add_reg_contract_2_post_variant v
                         else bir_exp_false``;
val defs = [bir_add_reg_prog_def,
            bir_add_reg_contract_2_post_variant_def,
            bir_add_reg_I_def, bir_exp_false_def, BType_Bool_def];

val (bir_add_reg_loop_variant_ht, bir_add_reg_loop_variant_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_add_reg_loop_variant_wp_def = Define `
  bir_add_reg_loop_variant_wp v =
    ^(bir_add_reg_loop_variant_wp_tm)
`;
val _ = save_thm ("bir_add_reg_loop_variant_ht",
                  bir_add_reg_loop_variant_ht);


(*********   (3)  bir_add_reg_loop_continue_variant     **********)
(* This WP is for execution which starts at the loop condition and
 * then continues looping. *)
(* 40 -> 20 *)
val prefix = "add_reg_loop_continue_variant_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val ending_set = ``{BL_Address (Imm64 0x20w); BL_Address (Imm64 0x40w); BL_Address (Imm64 0x48w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x20w))
                         then bir_add_reg_contract_3_post_variant v
                         else bir_exp_false``;
val defs = [bir_add_reg_prog_def,
            bir_add_reg_contract_3_post_variant_def,
            bir_add_reg_I_def, bir_exp_false_def, BType_Bool_def];

val (bir_add_reg_loop_continue_variant_ht,
     bir_add_reg_loop_continue_variant_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_add_reg_loop_continue_variant_wp_def = Define `
  bir_add_reg_loop_continue_variant_wp v =
    ^(bir_add_reg_loop_continue_variant_wp_tm)
`;
val _ = save_thm ("bir_add_reg_loop_continue_variant_ht",
                  bir_add_reg_loop_continue_variant_ht);


(**************    (4)   bir_add_reg_loop_exit      ***************)
(* This WP is for execution which starts at the loop condition and
 * then exits the loop. Note that the blocks following 44 are
 * just SP manipulation and return. *)
(* 40 -> 48 *)
val prefix = "add_reg_loop_exit_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val ending_set = ``{BL_Address (Imm64 0x20w); BL_Address (Imm64 0x48w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm64 0x48w))
                         then bir_add_reg_contract_4_post
                         else bir_exp_false``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_4_post_def,
            bir_add_reg_post_def, bir_exp_false_def];

val (bir_add_reg_loop_exit_ht, bir_add_reg_loop_exit_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_add_reg_loop_exit_wp_def = Define
  `bir_add_reg_loop_exit_wp = ^(bir_add_reg_loop_exit_wp_tm)`;
val _ =
  save_thm ("bir_add_reg_loop_exit_ht", bir_add_reg_loop_exit_ht);


(************            SOME EXPERIMENTS            **************)
(* What about the preamble of the function, where the arguments are
 * loaded from the stack into registers? And the final instruction,
 * where the stack pointer is reset?
 *
 * This should also be verified, however it is not currently a part
 * of verification due to issues with memory simplification which
 * bungle the step involving the SMT solver.
 *
 * The below shows that we can still prove HTs for this
 * situation. *)

(*****************     (0) bir_add_reg_mem      *******************)
(* The WP for the memory part of the add_reg is generated and proved
 * here. *)
(* 0 -> 4 -> 8 -> c -> 10 -> 14 -> 18 -> 1c *)

(*
val prefix = "add_reg_mem_";
val first_block_label_tm = ``BL_Address (Imm64 0x0w)``; (* 28 *)
val ending_lam_disj =  ``BL_Address (Imm64 0x1cw)``; (* 64 *)
val blacklist = [];
val postcond_tm = ``bir_add_reg_contract_0_post``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_0_post_def,
            bir_add_reg_contract_0_pre_def];

val (bir_add_reg_mem_ht, bir_add_reg_mem_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm ending_lam_disj
                postcond_tm prefix blacklist defs;

val bir_add_reg_mem_wp_def = Define `
  bir_add_reg_mem_wp = ^(bir_add_reg_mem_wp_tm)
`;
val _ = save_thm ("bir_add_reg_mem_ht", bir_add_reg_mem_ht);
*)



(*
(* The precondition of contract zero *)
val contract_0_pre = eot ``bir_add_reg_contract_0_pre``;
(* The implication we need to prove for proving the contract *)
val contract_0_imp =
  prove_imp_w_smt contract_0_pre bir_add_reg_mem_wp_tm;

(* Display the model *)
val _ =
  Z3_SAT_modelLib.Z3_GET_SAT_MODEL (
    bir2bool (
      bimp(contract_0_pre, bir_add_reg_mem_wp)
    )
  )
*)

val _ = export_theory();
