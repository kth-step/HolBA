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

fun not_empty_set set =
  EQT_ELIM (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) []
    (mk_neg (mk_eq (set, pred_setSyntax.mk_empty bir_label_t_ty))))
;

fun delete_not_empty_set elem set =
  let
    val delete_tm = pred_setSyntax.mk_delete (set, elem)

    val delete_thm =
      SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
	[pred_setTheory.DELETE_DEF]
	delete_tm

    val notempty_thm =
      SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) []
	(mk_neg (mk_eq ((snd o dest_eq o concl) delete_thm, pred_setSyntax.mk_empty bir_label_t_ty)))

  in
    EQT_ELIM (SIMP_CONV std_ss [delete_thm, notempty_thm] 
      (mk_neg (mk_eq (delete_tm, pred_setSyntax.mk_empty bir_label_t_ty)))
    )
  end
;

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
val (get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr,
     mk_set_repr, simp_delete_set_repr_rule,
     simp_insert_set_repr_rule, simp_in_sing_set_repr_rule, simp_inter_set_repr_rule, simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) = (ending_set_to_sml_list, el_in_set, delete_not_empty_set, mk_set, simp_delete_set_rule,
     simp_insert_set_rule, simp_in_sing_set_rule, simp_inter_set_rule, simp_in_set_tac, bir_inter_var_set_ss, bir_union_var_set_ss);
(************************************)

(* =============================================================== *)

val bir_ieo_sec_iseven_loop_comp_ht =
  use_pre_str_rule_map
    (HO_MATCH_MP (HO_MATCH_MP bir_label_ht_impl_weak_ht (not_empty_set (get_contract_ls bir_ieo_sec_iseven_loop_ht))) bir_ieo_sec_iseven_loop_ht)
    contract_ev_1_imp_taut_thm;

val bir_ieo_sec_iseven_exit_comp_ht =
  use_pre_str_rule_map
    (HO_MATCH_MP (HO_MATCH_MP bir_label_ht_impl_weak_ht (not_empty_set (get_contract_ls bir_ieo_sec_iseven_exit_ht))) bir_ieo_sec_iseven_exit_ht)
    contract_ev_2_imp_taut_thm;


val bir_ieo_sec_isodd_loop_comp_ht =
  use_pre_str_rule_map
    (HO_MATCH_MP (HO_MATCH_MP bir_label_ht_impl_weak_ht (not_empty_set (get_contract_ls bir_ieo_sec_isodd_loop_ht))) bir_ieo_sec_isodd_loop_ht)
    contract_od_1_imp_taut_thm;

val bir_ieo_sec_isodd_exit_comp_ht =
  use_pre_str_rule_map
    (HO_MATCH_MP (HO_MATCH_MP bir_label_ht_impl_weak_ht (not_empty_set (get_contract_ls bir_ieo_sec_isodd_exit_ht))) bir_ieo_sec_isodd_exit_ht)
    contract_od_2_imp_taut_thm;



(* =============================================================== *)

  val abs_ev_intro = prove(``bir_ieo_sec_iseven_loop_post v1 v = \l. bir_ieo_sec_iseven_loop_post v1 v l``, EVAL_TAC >> REWRITE_TAC []);
  val abs_ev_intro2 = prove(``bir_ieo_sec_iseven_exit_post v1 = \l. bir_ieo_sec_iseven_exit_post v1 l``, EVAL_TAC >> REWRITE_TAC []);

  val loop_map_ht_ = REWRITE_RULE [Once abs_ev_intro] bir_ieo_sec_iseven_loop_comp_ht;

  val new_ending_label_set = ``{BL_Address (Imm32 0x204w); BL_Address (Imm32 0x200w)}``;
  val ht = REWRITE_RULE [Once abs_ev_intro] bir_ieo_sec_iseven_exit_comp_ht;

  val loop_exit_simp_ht = bir_remove_labels_from_ending_set not_empty_set ht new_ending_label_set;

  val loop_exit_simp1_ht =
    REWRITE_RULE [Once abs_ev_intro2] loop_exit_simp_ht;
  val loop_exit_simp2_ht =
    use_post_weak_rule_map loop_exit_simp1_ht ``BL_Address (Imm32 0x000w)`` contract_ev_3_imp_taut_thm;
  val loop_exit_simp3_ht = loop_exit_simp2_ht;


  val loop_ev_map_ht_2  = REWRITE_RULE [bir_ieo_sec_iseven_loop_pre_def,
                                     bir_ieo_variant_def] loop_map_ht_;
  val loop_ev_exit_ht = REWRITE_RULE [bir_ieo_sec_iseven_exit_pre_def,
                                   bir_ieo_variant_def] loop_exit_simp3_ht;


  val abs_od_intro = prove(``bir_ieo_sec_isodd_loop_post v1 v = \l. bir_ieo_sec_isodd_loop_post v1 v l``, EVAL_TAC >> REWRITE_TAC []);
  val abs_od_intro2 = prove(``bir_ieo_sec_isodd_exit_post v1 = \l. bir_ieo_sec_isodd_exit_post v1 l``, EVAL_TAC >> REWRITE_TAC []);

  val loop_map_ht_ = REWRITE_RULE [Once abs_od_intro] bir_ieo_sec_isodd_loop_comp_ht;

  val new_ending_label_set = ``{BL_Address (Imm32 0x204w); BL_Address (Imm32 0x200w)}``;
  val ht = REWRITE_RULE [Once abs_od_intro] bir_ieo_sec_isodd_exit_comp_ht;

  val loop_exit_simp_ht = bir_remove_labels_from_ending_set not_empty_set ht new_ending_label_set;

  val loop_exit_simp1_ht = REWRITE_RULE [Once abs_od_intro2] loop_exit_simp_ht;
  val loop_exit_simp2_ht =
    use_post_weak_rule_map loop_exit_simp1_ht ``BL_Address (Imm32 0x000w)`` contract_od_3_imp_taut_thm;
  val loop_exit_simp3_ht = loop_exit_simp2_ht;


  val loop_od_map_ht_2  = REWRITE_RULE [bir_ieo_sec_isodd_loop_pre_def,
                                     bir_ieo_variant_def] loop_map_ht_;
  val loop_od_exit_ht = REWRITE_RULE [bir_ieo_sec_isodd_exit_pre_def,
                                   bir_ieo_variant_def] loop_exit_simp3_ht;

(* =============================================================== *)

(* For debugging: *)
  val loop_map_ht    = REWRITE_RULE [GSYM bir_ieo_sec_iseven_loop_post_def, Once abs_ev_intro]
          (bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr,
                                   delete_not_empty_set_repr, mk_set_repr,
                                   simp_delete_set_repr_rule, simp_insert_set_repr_rule)
           (REWRITE_RULE [GSYM abs_ev_intro, bir_ieo_sec_iseven_loop_post_def] loop_ev_map_ht_2));

  val loop_exit_ht   = loop_ev_exit_ht;
  val loop_invariant = ``bir_ieo_invariant v1``;
  val loop_condition = ``bir_ieo_condition``;
  val loop_variant   = ``bir_ieo_variant``;

  val def_list = [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_iseven_loop_post_def,
                  bir_ieo_sec_iseven_loop_pre_def,
                  bir_ieo_sec_iseven_exit_pre_def];

val loop_and_exit_ev_ht =
  bir_compose_map_loop_unsigned (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss)
    loop_map_ht loop_exit_ht loop_invariant loop_condition loop_variant bprog_is_even_odd_def def_list;


(* For debugging: *)
  val loop_map_ht    = REWRITE_RULE [GSYM bir_ieo_sec_isodd_loop_post_def, Once abs_od_intro]
          (bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr,
                                   delete_not_empty_set_repr, mk_set_repr,
                                   simp_delete_set_repr_rule, simp_insert_set_repr_rule)
           (REWRITE_RULE [GSYM abs_od_intro, bir_ieo_sec_isodd_loop_post_def] loop_od_map_ht_2));

  val loop_exit_map_ht   = loop_od_exit_ht;
  val loop_invariant = ``bir_ieo_invariant v1``;
  val loop_condition = ``bir_ieo_condition``;
  val loop_variant   = ``bir_ieo_variant``;

  val def_list = [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_isodd_loop_post_def,
                  bir_ieo_sec_isodd_loop_pre_def,
                  bir_ieo_sec_isodd_exit_pre_def];

val loop_and_exit_od_ht =
  bir_compose_map_loop_unsigned (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss)
    loop_map_ht loop_exit_map_ht loop_invariant loop_condition loop_variant bprog_is_even_odd_def def_list;


(* =============================================================== *)

val is_even_1_ht =
  REWRITE_RULE [contract_ev_4_imp_taut_thm] (use_pre_str_rule_map loop_and_exit_ev_ht contract_ev_4_imp_taut_thm);

val thm1 = ((Q.SPECL [`bprog_is_even_odd`, `bir_exp_true`,
          `BL_Address (Imm32 0w)`, `{BL_Address (Imm32 516w); BL_Address (Imm32 512w)}`, `{}`, `bir_ieo_pre v1`,
          `\l.
            if l = BL_Address (Imm32 0w) then bir_ieo_invariant v1
            else bir_ieo_sec_iseven_exit_post v1 l`,
          `bir_ieo_sec_iseven_exit_post v1`])
	      bir_wm_instTheory.bir_map_weakening_rule_thm);
val thm2 = REWRITE_RULE [is_even_1_ht] thm1;
val is_even_2_ht = REWRITE_RULE [prove(``^((fst o dest_imp o concl) thm2)``,
  SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >> (
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.bir_TYPES_ss++wordsLib.WORD_ss)
       [bir_ieo_sec_iseven_exit_post_def,
        bir_ieo_sec_iseven_loop_post_def,
        bir_exec_to_labels_triple_postcond_def]
  )
  )] thm2;


val bir_ieo_is_even_ht = save_thm("bir_ieo_is_even_ht",
  is_even_2_ht
);


val is_odd_1_ht =
  REWRITE_RULE [contract_od_4_imp_taut_thm] (use_pre_str_rule_map loop_and_exit_od_ht contract_od_4_imp_taut_thm);

val thm1 = ((Q.SPECL [`bprog_is_even_odd`, `bir_exp_true`,
          `BL_Address (Imm32 0x100w)`, `{BL_Address (Imm32 516w); BL_Address (Imm32 512w)}`, `{}`,
          `bir_ieo_pre v1`,
          `\l.
            if l = BL_Address (Imm32 0w) then bir_ieo_invariant v1
            else bir_ieo_sec_isodd_exit_post v1 l`,
          `bir_ieo_sec_isodd_exit_post v1`])
	      bir_wm_instTheory.bir_map_weakening_rule_thm);
val thm2 = REWRITE_RULE [is_odd_1_ht] thm1;
val is_odd_2_ht = REWRITE_RULE [prove(``^((fst o dest_imp o concl) thm2)``,
  SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >> (
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.bir_TYPES_ss++wordsLib.WORD_ss)
       [bir_ieo_sec_isodd_exit_post_def,
        bir_ieo_sec_isodd_loop_post_def,
        bir_exec_to_labels_triple_postcond_def]
  )
  )] thm2;


val bir_ieo_is_odd_ht = save_thm("bir_ieo_is_odd_ht",
  is_odd_2_ht
);


val _ = export_theory();
