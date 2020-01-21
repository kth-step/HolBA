open HolKernel Parse boolLib bossLib;
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;
open bslSyntax;
open tutorial_bir_to_armSupportTheory;
open tutorial_smtTheory;
open examplesBinaryTheory;
open bir_wm_instTheory;
open bin_hoare_logicTheory;
open bir_valuesTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_exp_equivTheory;
open bir_programTheory;

open tutorial_compositionLib;
open tutorial_wpSupportLib;

open bir_auxiliaryLib;

open HolBACoreSimps;
open HolBASimps;
open bin_hoare_logicSimps;

val _ = new_theory "tutorial_composition";

(* TODO: Where to place the below? *)
fun el_in_set elem set =
  EQT_ELIM (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) [] (pred_setSyntax.mk_in (elem, set)));

val mk_set = pred_setSyntax.mk_set;

val simp_delete_set_rule =
  SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
    [pred_setTheory.DELETE_DEF]

val simp_insert_set_rule =
  SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
    [(* ??? *)]

val simp_in_sing_set_rule =
  SIMP_RULE std_ss [pred_setTheory.IN_SING]

fun simp_inter_set_rule ht =
  REWRITE_RULE [EVAL (get_bir_map_triple_blist ht)] ht

val simp_in_set_tac =
  SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss++pred_setLib.PRED_SET_ss) []

val inter_set_ss = SSFRAG {ac = [],
                           congs = [],
                           convs = [{conv = K (K computeLib.EVAL_CONV),
                                    key= SOME ([], ``A INTER B``),
                                    name = "EVAL_CONV_INTER",
                                    trace = 2}],
                           dprocs = [], filter = NONE, name = SOME "inter_set_ss", rewrs = []};

val union_set_ss = SSFRAG {ac = [],
                           congs = [],
                           convs = [{conv = K (K computeLib.EVAL_CONV),
                                    key= SOME ([], ``A UNION B``),
                                    name = "EVAL_CONV_UNION",
                                    trace = 2}],
                           dprocs = [], filter = NONE, name = SOME "union_set_ss", rewrs = []};

(* DEBUG *)
val (get_labels_from_set_repr, el_in_set_repr,
     mk_set_repr, simp_delete_set_repr_rule,
     simp_insert_set_repr_rule, simp_in_sing_set_repr_rule, simp_inter_set_repr_rule, simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) = (ending_set_to_sml_list, el_in_set, mk_set, simp_delete_set_rule,
     simp_insert_set_rule, simp_in_sing_set_rule, simp_inter_set_rule, simp_in_set_tac, inter_set_ss, union_set_ss);
(************************************)

(****************************************************************)
(* Step 0: *)
(* Translate HTs from bir_exec_to_labels_triple to bir_triple,
 * Then replace preconditions with shorthands and prove the
 * validity of this. *)
(* TODO: use_impl_rule uses cheats! *)

(* 28 -> 64 *)
val bir_add_reg_entry_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_entry_ht)
    contract_1_imp_taut_thm;

(* 32 -> 64 *)
val bir_add_reg_loop_variant_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_variant_ht)
    (Q.SPEC `v` contract_2v_imp_taut_thm);

(* 64 -> 32 *)
val bir_add_reg_loop_continue_variant_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_continue_variant_ht)
    (Q.SPEC `v` contract_3v_imp_taut_thm);

(* 64 -> 72 *)
val bir_add_reg_loop_exit_comp_ht =
  use_impl_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_add_reg_loop_exit_ht)
    contract_4_imp_taut_thm;

(****************************************************************)
(* Step 1: *)
(* Compose 64 -> 32 and 32 -> 64 sequentially (using bir_map_std_seq_comp_thm) *)

(* For debugging: *)
  val ht1 = bir_add_reg_loop_continue_variant_comp_ht; (* 64 -> 32 *)
  val ht2 = bir_add_reg_loop_variant_comp_ht; (* 32 -> 64 *)
  (* The definitions of the program, plus any shorthands in postcondition of HT1
   * and precondition of HT2 *)
  (* TODO: Program definition could be bad to unfold in the wrong place, maybe that should be a
   * separate argument... *)
  val def_list = [bir_add_reg_prog_def, bir_add_reg_contract_3_post_variant_def,
		  bir_add_reg_contract_2_pre_variant_def];

val loop_map_ht =
   bir_compose_nonmap_seq ht1 ht2 def_list (get_labels_from_set_repr, el_in_set_repr,
                                            mk_set_repr, simp_delete_set_repr_rule,
	                                    simp_insert_set_repr_rule);

(****************************************************************)
(* Step 2: *)
(* Compose loop from loop_map_ht and bir_add_reg_loop_exit_comp_ht (using bir_while_rule_thm) *)

(* For debugging: *)
  val loop_map_ht = loop_map_ht;
  val loop_exit_ht = bir_add_reg_loop_exit_comp_ht;
  val loop_invariant = ``bir_add_reg_I``;
  val loop_condition = ``bir_add_reg_loop_condition``;
  val loop_variant = bden (bvar "R2" ``(BType_Imm Bit64)``);
  (* The definitions of the program, loop condition and both preconditions *)
  val def_list = [bir_add_reg_prog_def, bir_add_reg_loop_condition_def,
		  bir_add_reg_contract_3_pre_variant_def, bir_add_reg_contract_2_post_variant_def,
                  bir_add_reg_contract_4_pre_def];

val loop_and_exit_ht =
  bir_compose_loop loop_map_ht loop_exit_ht loop_invariant loop_condition loop_variant def_list;

(****************************************************************)
(* Step 3: *)
(* Compose loop intro with loop (using bir_map_std_seq_comp_thm) *)
  val ht1 = bir_add_reg_entry_comp_ht
  val ht2 = loop_and_exit_ht
  val def_list = [bir_add_reg_prog_def, bir_add_reg_contract_1_post_def];

(* TODO: Rename HT to tie to program name? *)
val final_ht =
   bir_compose_nonmap_seq ht1 ht2 def_list;

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

(* Specialise lift_contract_thm in order to obtain the antecedents enabling translation from BIR to
 * ARM HT. *)
val add_lift_thm =
  ISPECL [get_bir_map_triple_prog final_ht,
          ``bir_add_reg_progbin``,
          ``28w:word64``,
          ``{72w:word64}``,
          (((el 2) o snd o strip_comb o concl) examplesBinaryTheory.bir_add_reg_arm8_lift_THM),
          ``arm8_add_reg_pre``, ``arm8_add_reg_post``,
          get_bir_map_triple_pre final_ht,
          get_bir_map_triple_post final_ht] lift_contract_thm;

(* Prove the ARM triple by supplying the antecedents of lift_contract_thm *)
val arm_add_reg_contract_thm =
  prove(``arm8_triple bir_add_reg_progbin 28w {72w} arm8_add_reg_pre
            arm8_add_reg_post``,

irule add_lift_thm >>
REPEAT STRIP_TAC >| [
  (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
   *    set *)
  (* TODO: This subset computation is slooow... *)
  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++HolBASimps.VARS_OF_PROG_ss
                       ++pred_setLib.PRED_SET_ss)
    [bir_add_reg_prog_def, bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def, arm8_wf_varset_def,
     arm8_vars_def],

  (* 2. Starting address exists in program *)
  FULL_SIMP_TAC std_ss
    [EVAL ``MEM (^(get_bir_map_triple_start_label final_ht))
		(bir_labels_of_program bir_add_reg_prog)``],

  (* 3. Provide translation of the ARM8 precondition to the BIR precondition *)
  FULL_SIMP_TAC std_ss [bir_add_reg_contract_1_pre_def, arm8_pre_imp_bir_pre_thm],

  (* 4. Provide translation of the ARM8 postcondition to BIR postcondition *)
  FULL_SIMP_TAC std_ss [bir_add_reg_contract_4_post_def] >>
  ASSUME_TAC (Q.SPEC `{BL_Address (Imm64 ml') | ml' IN {72w}}` arm8_post_imp_bir_post_thm) >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_arm8_def] >>
  FULL_SIMP_TAC std_ss [],

  (* 5. Provide the lifter theorem of the program *)
  FULL_SIMP_TAC std_ss [examplesBinaryTheory.bir_add_reg_arm8_lift_THM],

  (* 6. Provide the BIR triple in the requisite format *)
  ASSUME_TAC (CONJUNCT2 (SIMP_RULE std_ss [bir_triple_from_map_triple_alt] final_ht)) >>
  FULL_SIMP_TAC std_ss [pred_setTheory.UNION_EMPTY] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>

  (*      Precondition: *)
  FULL_SIMP_TAC std_ss [bir_triple_def, weak_triple_def,
			bir_exec_to_labels_triple_precond_def,
			bir_exec_to_labels_triple_postcond_def, bir_and_op2,
			bir_is_bool_exp_env_REWRS] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  Cases_on `s'.bst_pc.bpc_label = BL_Address (Imm64 72w)` >> (
    FULL_SIMP_TAC std_ss [bir_and_op2, bir_is_bool_exp_env_REWRS]
  ) >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def, bir_weak_trs_def,
                                     bir_exec_to_labels_def,
                                     bir_exec_to_labels_n_def] >>
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
]
);

val _ = export_theory();
