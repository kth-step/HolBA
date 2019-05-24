open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib bir_htLib;
open easy_noproof_wpLib;
open bir_wpTheory bir_htTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory bir_valuesTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples: *)
open examplesBinaryTheory;
open tutorial_bir_to_armSupportTheory;
open tutorial_bir_to_armTheory;
open tutorial_wpSupportLib;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorial_wp";

(*
 val _ = bir_ppLib.remove_bir_pretty_printers ();
 val _ = bir_ppLib.install_bir_pretty_printers ();
*)

val prog_tm = (lhs o concl) bir_add_reg_prog_def;
(****************     (1) bir_add_reg_entry      ******************)
(* The WP for the loop entry of the add_reg is generated and proved
 * here. *)
(* 1c -> 38 -> 3c -> 40 *)
val prefix = "add_reg_entry_";
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``; (* 28 *)
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``; (* 64 *)
val false_label_l = [];
val postcond_tm = ``bir_add_reg_contract_1_post``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_1_post_def, bir_add_reg_I_def, BType_Bool_def];

(* bir_add_reg_entry_ht is the HT stating the generated WP: *)
val (bir_add_reg_entry_ht, bir_add_reg_entry_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
(* TODO: Add to end of HT-generating function *)
(* bir_add_reg_entry_wp is the weakest precondition obtained as a
 * term: *)
val bir_add_reg_entry_wp =
  get_wp_from_ht bir_add_reg_entry_ht;
val bir_add_reg_entry_wp_def =
  Define `bir_add_reg_entry_wp = ^(bir_add_reg_entry_wp)`;
val _ = save_thm ("bir_add_reg_entry_ht", bir_add_reg_entry_ht);


(****************    (2)  bir_add_reg_loop     ********************)
(* The WP for the loop content is generated and proved here. *)
(* 20 -> 24 -> 28 -> 2c -> 30 -> 34 -> 38 -> 3c -> 40 *)
val prefix = "add_reg_loop_";
val first_block_label_tm = ``BL_Address (Imm64 0x20w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
val false_label_l = [];
val postcond_tm = ``bir_add_reg_contract_2_post``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_2_post_def, bir_add_reg_I_def, BType_Bool_def];

val (bir_add_reg_loop_ht, bir_add_reg_loop_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_loop_wp =
  get_wp_from_ht bir_add_reg_loop_ht;
val bir_add_reg_loop_wp_def =
  Define `bir_add_reg_loop_wp = ^(bir_add_reg_loop_wp)`;
val _ = save_thm ("bir_add_reg_loop_ht", bir_add_reg_loop_ht);

(*************   (3)  bir_add_reg_loop_continue     ***************)
(* This WP is for execution which starts at the loop condition and
 * then continues looping. *)
(* 40 -> 20 *)
val prefix = "add_reg_loop_continue_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x20w)``;
val false_label_l = [``BL_Address (Imm64 0x44w)``];
val postcond_tm = ``bir_add_reg_contract_3_post``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_3_post_def, bir_add_reg_I_def, BType_Bool_def];

val (bir_add_reg_loop_continue_ht, bir_add_reg_loop_continue_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_loop_continue_wp =
  get_wp_from_ht bir_add_reg_loop_continue_ht;
val bir_add_reg_loop_continue_wp_def = Define
  `bir_add_reg_loop_continue_wp = ^(bir_add_reg_loop_continue_wp)`;

val _ = save_thm ("bir_add_reg_loop_continue_ht", bir_add_reg_loop_continue_ht);


(***************    (4)   bir_add_reg_loop_exit      *****************)
(* This WP is for execution which starts at the loop condition and
 * then exits the loop. Note that the blocks following 44 are
 * SP manipulation and return. *)
(* 40 -> 48 *)
val prefix = "add_reg_loop_exit_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x48w)``;
val false_label_l = [``BL_Address (Imm64 0x20w)``];
val postcond_tm = ``bir_add_reg_contract_4_post``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_4_post_def, bir_add_reg_post_def];

val (bir_add_reg_loop_exit_ht, bir_add_reg_loop_exit_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_loop_exit_wp =
  get_wp_from_ht bir_add_reg_loop_exit_ht;
val bir_add_reg_loop_exit_wp_def = Define
  `bir_add_reg_loop_exit_wp = ^(bir_add_reg_loop_exit_wp)`;

val _ = save_thm ("bir_add_reg_loop_exit_ht", bir_add_reg_loop_exit_ht);


(******************    (2v)  bir_add_reg_loop_variant     *********************)
(* The WP for the loop content is generated and proved here. *)
(* 20 -> 24 -> 28 -> 2c -> 30 -> 34 -> 38 -> 3c -> 40 *)
val prefix = "add_reg_loop_variant_";
val first_block_label_tm = ``BL_Address (Imm64 0x20w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
val false_label_l = [];
val postcond_tm =
  ``bir_add_reg_contract_2_post_variant v``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_2_post_variant_def, bir_add_reg_I_def, BType_Bool_def];

val (bir_add_reg_loop_variant_ht, bir_add_reg_loop_cariant_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_loop_variant_wp =
  get_wp_from_ht bir_add_reg_loop_variant_ht;
val bir_add_reg_loop_variant_wp_def = Define
  `bir_add_reg_loop_variant_wp v = ^(bir_add_reg_loop_variant_wp)`;

val _ = save_thm ("bir_add_reg_loop_variant_ht", bir_add_reg_loop_variant_ht);


(*************   (3v)  bir_add_reg_loop_continue_variant     ***************)
(* This WP is for execution which starts at the loop condition and
 * then continues looping. *)
(* 40 -> 20 *)
val prefix = "add_reg_loop_continue_variant_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x20w)``;
val false_label_l = [``BL_Address (Imm64 0x44w)``];
val postcond_tm = ``bir_add_reg_contract_3_post_variant v``;
val defs = [bir_add_reg_prog_def, bir_add_reg_contract_3_post_variant_def, bir_add_reg_I_def, BType_Bool_def];

val (bir_add_reg_loop_continue_variant_ht, bir_add_reg_loop_continue_variant_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_loop_continue_variant_wp =
  get_wp_from_ht bir_add_reg_loop_continue_variant_ht;
val bir_add_reg_loop_continue_variant_wp_def = Define
  `bir_add_reg_loop_continue_variant_wp v = ^(bir_add_reg_loop_continue_variant_wp)`;

val _ = save_thm ("bir_add_reg_loop_continue_variant_ht", bir_add_reg_loop_continue_variant_ht);


(******************     (0) bir_add_reg_mem      ********************)
(* The WP for the memory part of the add_reg is generated and proved
 * here. *)
(* 0 -> 1c *)
(*
val prefix = "add_reg_mem_";
val first_block_label_tm = ``BL_Address (Imm64 0x0w)``; (* 28 *)
val last_block_label_tm =  ``BL_Address (Imm64 0x1cw)``; (* 64 *)
val false_label_l = [];
val postcond_tm = ``bir_add_reg_contract_0_post``;
(* bir_add_reg_entry_htis the HT stating the generated WP: *)

val defs = [bir_add_reg_prog_def, bir_add_reg_contract_0_post_def, bir_add_reg_contract_0_pre_def];

val bir_add_reg_loop_continue_variant_wp =
  get_wp_from_ht bir_add_reg_loop_continue_variant_ht;
val bir_add_reg_loop_continue_variant_wp_def = Define
  `bir_add_reg_loop_continue_variant_wp v = ^(bir_add_reg_loop_continue_variant_wp)`;


val (bir_add_reg_mem_ht, _) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l defs;
val bir_add_reg_mem_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_mem_ht;

val bir_add_reg_mem_wp_def = Define `bir_add_reg_mem_wp = ^(bir_add_reg_mem_wp)`;

val _ = save_thm ("bir_add_reg_mem_ht", bir_add_reg_mem_ht);
*)

(************           RECENT EXPERIMENTS           **************)
(* 
(* Contract 1 *)
val contract_1_pre =
  eot ``bir_add_reg_contract_1_pre``
val contract_1_imp =
  prove_imp_w_smt contract_1_pre bir_add_reg_entry_wp;

(* Contract 2 *)
val contract_2_pre =
  eot ``bir_add_reg_contract_2_pre``;
val contract_2_imp =
  prove_imp_w_smt contract_2_pre bir_add_reg_loop_wp;

(* Contract 3 *)
val contract_3_pre =
  eot ``bir_add_reg_contract_3_pre``;
val contract_3_imp =
  prove_imp_w_smt contract_3_pre bir_add_reg_loop_continue_wp;

(* Contract 4 *)
val contract_4_pre = eot ``bir_add_reg_contract_4_pre``;
val contract_4_imp = prove_imp_w_smt contract_4_pre bir_add_reg_loop_exit_wp;
*)

(* Contract 0 *)
(*
val prefix = "add_reg_mem_";
val first_block_label_tm = ``BL_Address (Imm64 0x0w)``; (* 28 *)
val last_block_label_tm =  ``BL_Address (Imm64 0x8w)``; (* 64 *)
val false_label_l = [];
val postcond_tm =
  (snd o dest_eq o concl o EVAL) (btrue);
val postcond_tm = beq(``(BExp_Load
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)``, get_r0);


(* bir_add_reg_entry_htis the HT stating the generated WP: *)
val (bir_add_reg_mem_ht, _) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;
val bir_add_reg_mem_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_mem_ht;
val bir_add_reg_mem_wp_def = Define `bir_add_reg_mem_wp = ^(bir_add_reg_mem_wp)`;


val contract_0_pre = (rhs o concl o EVAL) ``bir_add_reg_contract_0_pre``;
val contract_0_imp = prove_imp_w_smt contract_0_pre bir_add_reg_mem_wp;

Z3_SAT_modelLib.Z3_GET_SAT_MODEL (bir2bool (bimp(contract_0_pre, bir_add_reg_mem_wp)))
*)

val _ = export_theory();
