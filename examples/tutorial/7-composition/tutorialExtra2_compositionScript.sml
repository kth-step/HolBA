open HolKernel Parse boolLib bossLib;
open bslSyntax;
open bir_wm_instTheory;
open bin_hoare_logicTheory;
open bir_valuesTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_exp_equivTheory;
open bir_programTheory;

open tutorial_compositionLib;
open tutorial_wpSupportLib;

open birExamples2BinaryTheory;
open tutorialExtra2_wpTheory;
open tutorialExtra2_smtTheory;

open bir_auxiliaryLib;

open HolBACoreSimps;
open HolBASimps;
open bin_hoare_logicSimps;

val _ = new_theory "tutorialExtra2_composition";

(************************************)
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
  SIMP_RULE std_ss [pred_setTheory.IN_SING, pred_setTheory.IN_INSERT]

fun simp_inter_set_rule ht =
  ONCE_REWRITE_RULE [EVAL (get_bir_map_triple_blist ht)] ht

val simp_in_set_tac =
  SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss++pred_setLib.PRED_SET_ss) []

(* DEBUG *)
val (get_labels_from_set_repr, el_in_set_repr,
     mk_set_repr, simp_delete_set_repr_rule,
     simp_insert_set_repr_rule, simp_in_sing_set_repr_rule, simp_inter_set_repr_rule, simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) = (ending_set_to_sml_list, el_in_set, mk_set, simp_delete_set_rule,
     simp_insert_set_rule, simp_in_sing_set_rule, simp_inter_set_rule, simp_in_set_tac, bir_inter_var_set_ss, bir_union_var_set_ss);
(************************************)

(* =============================================================== *)

val bir_ieo_sec_iseven_loop_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_ieo_sec_iseven_loop_ht)
    contract_1_imp_taut_thm;

val bir_ieo_sec_iseven_exit_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_ieo_sec_iseven_exit_ht)
    contract_2_imp_taut_thm;



(* =============================================================== *)

  val abs_intro = prove(``bir_ieo_sec_iseven_loop_post v1 v = \l. bir_ieo_sec_iseven_loop_post v1 v l``, EVAL_TAC >> REWRITE_TAC []);
  val abs_intro2 = prove(``bir_ieo_sec_iseven_exit_post v1 = \l. bir_ieo_sec_iseven_exit_post v1 l``, EVAL_TAC >> REWRITE_TAC []);

  val loop_ht = REWRITE_RULE [Once abs_intro] bir_ieo_sec_iseven_loop_comp_ht;
  val loop_map_ht_ = bir_map_triple_from_bir_triple loop_ht;

  val new_ending_label_set = ``{BL_Address (Imm32 0x204w); BL_Address (Imm32 0x200w)}``;
  val ht = REWRITE_RULE [Once abs_intro] bir_ieo_sec_iseven_exit_comp_ht;

  val loop_exit_simp_ht = bir_remove_labels_from_ending_set ht new_ending_label_set;

  val loop_exit_simp1_ht = (REWRITE_RULE [Once abs_intro2] loop_exit_simp_ht);
  val loop_exit_simp2_ht =
    use_post_weak_rule loop_exit_simp1_ht ``BL_Address (Imm32 0x000w)`` contract_3_imp_taut_thm;
  val loop_exit_simp3_ht = loop_exit_simp2_ht;


  val loop_map_ht_2  = REWRITE_RULE [bir_ieo_sec_iseven_loop_pre_def,
                                     bir_ieo_variant_def] loop_map_ht_;
  val loop_exit_ht = REWRITE_RULE [bir_ieo_sec_iseven_exit_pre_def,
                                   bir_ieo_variant_def] loop_exit_simp3_ht;

(* =============================================================== *)

(* For debugging: *)
  val loop_map_ht    = REWRITE_RULE [GSYM bir_ieo_sec_iseven_loop_post_def, Once abs_intro]
          (bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                   simp_delete_set_repr_rule, simp_insert_set_repr_rule)
           (REWRITE_RULE [GSYM abs_intro, bir_ieo_sec_iseven_loop_post_def] loop_map_ht_2));

  val loop_exit_ht   = loop_exit_ht;
  val loop_invariant = ``bir_ieo_invariant v1``;
  val loop_condition = ``bir_ieo_condition``;
  val loop_variant   = ``bir_ieo_variant``;

  val def_list = [bprog_is_even_odd_def,
                  bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_iseven_loop_post_def,
                  bir_ieo_sec_iseven_loop_pre_def,
                  bir_ieo_sec_iseven_exit_pre_def];

val loop_and_exit_ht =
  bir_compose_loop_unsigned (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss)
    loop_map_ht loop_exit_ht loop_invariant loop_condition loop_variant def_list;


(* =============================================================== *)

val is_even_1_ht =
  REWRITE_RULE [contract_4_imp_taut_thm] (use_pre_str_rule loop_and_exit_ht contract_4_imp_taut_thm);

val thm1 = ((Q.SPECL [`bprog_is_even_odd`,
          `BL_Address (Imm32 0w)`, `{BL_Address (Imm32 516w); BL_Address (Imm32 512w)}`,
          `bir_ieo_pre v1`, `bir_ieo_pre v1`,
          `\l.
            if l = BL_Address (Imm32 0w) then bir_ieo_invariant v1
            else bir_ieo_sec_iseven_exit_post v1 l`,
          `bir_ieo_sec_iseven_exit_post v1`])
	      bir_wm_instTheory.bir_consequence_rule_thm);
val thm2 = (fn x => REWRITE_RULE [(((REWRITE_CONV []) o fst o dest_imp o concl) x)] x) thm1;
val thm3 = REWRITE_RULE [is_even_1_ht] thm2;
val is_even_2_ht = REWRITE_RULE [prove(``^((fst o dest_imp o concl) thm3)``,
  SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >> (
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.bir_TYPES_ss++wordsLib.WORD_ss)
       [bir_ieo_sec_iseven_exit_post_def,
        bir_ieo_sec_iseven_loop_post_def,
        bir_exec_to_labels_triple_postcond_def]
  )
  )] thm3;


val bir_ieo_is_even_ht = save_thm("bir_ieo_is_even_ht",
  is_even_2_ht
);



val _ = export_theory();
