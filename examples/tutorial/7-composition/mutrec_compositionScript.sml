open HolKernel Parse boolLib bossLib;
open bslSyntax;
open bir_tsTheory;

open bir_compositionLib;
open bir_wp_interfaceLib;

open bir_prog_mutrecTheory;
open mutrec_wpTheory;
open mutrec_smtTheory;

open bir_auxiliaryLib;

open HolBACoreSimps;
open HolBASimps;
open program_logicSimps;

val _ = new_theory "mutrec_composition";

(* =============================================================== *)

val bir_ieo_sec_iseven_loop_comp_ct =
  use_pre_str_rule_simp
    (HO_MATCH_MP (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls bir_ieo_sec_iseven_loop_ht))) bir_ieo_sec_iseven_loop_ht)
    contract_ev_1_imp_taut_thm;

val bir_ieo_sec_iseven_exit_comp_ct =
  use_pre_str_rule_simp
    (HO_MATCH_MP (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls bir_ieo_sec_iseven_exit_ht))) bir_ieo_sec_iseven_exit_ht)
    contract_ev_2_imp_taut_thm;


val bir_ieo_sec_isodd_loop_comp_ct =
  use_pre_str_rule_simp
    (HO_MATCH_MP (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls bir_ieo_sec_isodd_loop_ht))) bir_ieo_sec_isodd_loop_ht)
    contract_od_1_imp_taut_thm;

val bir_ieo_sec_isodd_exit_comp_ct =
  use_pre_str_rule_simp
    (HO_MATCH_MP (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls bir_ieo_sec_isodd_exit_ht))) bir_ieo_sec_isodd_exit_ht)
    contract_od_2_imp_taut_thm;



(* =============================================================== *)

  val abs_ev_intro = prove(``bir_ieo_sec_iseven_loop_post v1 v = \l. bir_ieo_sec_iseven_loop_post v1 v l``, EVAL_TAC >> REWRITE_TAC []);
  val abs_ev_intro2 = prove(``bir_ieo_sec_iseven_exit_post v1 = \l. bir_ieo_sec_iseven_exit_post v1 l``, EVAL_TAC >> REWRITE_TAC []);

  val loop_simp_ct_ = REWRITE_RULE [Once abs_ev_intro] bir_ieo_sec_iseven_loop_comp_ct;

  val new_ilist = ``{BL_Address (Imm32 0x204w); BL_Address (Imm32 0x200w)}``;
  val ht = REWRITE_RULE [Once abs_ev_intro] bir_ieo_sec_iseven_exit_comp_ct;

  val loop_exit_simp_ht = bir_remove_labels_from_ilist_predset ht new_ilist;

  val loop_exit_simp1_ht =
    REWRITE_RULE [Once abs_ev_intro2] loop_exit_simp_ht;
  val loop_exit_simp2_ht =
    use_post_weak_rule_simp loop_exit_simp1_ht ``BL_Address (Imm32 0x000w)`` contract_ev_3_imp_taut_thm;
  val loop_exit_simp3_ht = loop_exit_simp2_ht;


  val loop_ev_simp_ct_2  = REWRITE_RULE [bir_ieo_sec_iseven_loop_pre_def,
                                     bir_ieo_variant_def] loop_simp_ct_;
  val loop_ev_exit_ht = REWRITE_RULE [bir_ieo_sec_iseven_exit_pre_def,
                                   bir_ieo_variant_def] loop_exit_simp3_ht;


  val abs_od_intro = prove(``bir_ieo_sec_isodd_loop_post v1 v = \l. bir_ieo_sec_isodd_loop_post v1 v l``, EVAL_TAC >> REWRITE_TAC []);
  val abs_od_intro2 = prove(``bir_ieo_sec_isodd_exit_post v1 = \l. bir_ieo_sec_isodd_exit_post v1 l``, EVAL_TAC >> REWRITE_TAC []);

  val loop_simp_ct_ = REWRITE_RULE [Once abs_od_intro] bir_ieo_sec_isodd_loop_comp_ct;

  val new_ilist = ``{BL_Address (Imm32 0x204w); BL_Address (Imm32 0x200w)}``;
  val ht = REWRITE_RULE [Once abs_od_intro] bir_ieo_sec_isodd_exit_comp_ct;

  val loop_exit_simp_ht = bir_remove_labels_from_ilist_predset ht new_ilist;

  val loop_exit_simp1_ht = REWRITE_RULE [Once abs_od_intro2] loop_exit_simp_ht;
  val loop_exit_simp2_ht =
    use_post_weak_rule_simp loop_exit_simp1_ht ``BL_Address (Imm32 0x000w)`` contract_od_3_imp_taut_thm;
  val loop_exit_simp3_ht = loop_exit_simp2_ht;


  val loop_od_simp_ct_2  = REWRITE_RULE [bir_ieo_sec_isodd_loop_pre_def,
                                     bir_ieo_variant_def] loop_simp_ct_;
  val loop_od_exit_ht = REWRITE_RULE [bir_ieo_sec_isodd_exit_pre_def,
                                   bir_ieo_variant_def] loop_exit_simp3_ht;

(* =============================================================== *)

  val loop_simp_ct    = REWRITE_RULE [GSYM bir_ieo_sec_iseven_loop_post_def, Once abs_ev_intro]
          (bir_populate_elist_predset
           (REWRITE_RULE [GSYM abs_ev_intro, bir_ieo_sec_iseven_loop_post_def] loop_ev_simp_ct_2));
(* For debugging:
  val loop_map_ct   = loop_simp_ct;
  val loop_exit_map_ct   = loop_ev_exit_ht;
  val loop_invariant = ``bir_ieo_invariant v1``;
  val loop_condition = ``bir_ieo_condition``;
  val loop_variant   = ``bir_ieo_variant``;
  val prog_def = mutrec_def;
  val def_list = [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_iseven_loop_post_def,
                  bir_ieo_sec_iseven_loop_pre_def,
                  bir_ieo_sec_iseven_exit_pre_def];
 *)
val loop_and_exit_ev_ht =
  bir_compose_simp_loop_unsigned_predset
    loop_simp_ct loop_ev_exit_ht ``bir_ieo_invariant v1`` ``bir_ieo_condition`` ``bir_ieo_variant`` mutrec_def [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_iseven_loop_post_def,
                  bir_ieo_sec_iseven_loop_pre_def,
                  bir_ieo_sec_iseven_exit_pre_def];


(* For debugging: *)
  val loop_simp_ct    = REWRITE_RULE [GSYM bir_ieo_sec_isodd_loop_post_def, Once abs_od_intro]
          (bir_populate_elist_predset
           (REWRITE_RULE [GSYM abs_od_intro, bir_ieo_sec_isodd_loop_post_def] loop_od_simp_ct_2));
(*
  val loop_exit_simp_ct   = loop_od_exit_ht;
  val loop_invariant = ``bir_ieo_invariant v1``;
  val loop_condition = ``bir_ieo_condition``;
  val loop_variant   = ``bir_ieo_variant``;
  val prog_def = bprog_is_even_odd_def;
  val def_list = [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_isodd_loop_post_def,
                  bir_ieo_sec_isodd_loop_pre_def,
                  bir_ieo_sec_isodd_exit_pre_def];
*)
val loop_and_exit_od_ht =
  bir_compose_simp_loop_unsigned_predset
    loop_simp_ct loop_od_exit_ht ``bir_ieo_invariant v1`` ``bir_ieo_condition`` ``bir_ieo_variant`` mutrec_def [bir_ieo_condition_def,
		  bir_ieo_variant_def,
                  bir_ieo_invariant_def,
                  bir_ieo_sec_isodd_loop_post_def,
                  bir_ieo_sec_isodd_loop_pre_def,
                  bir_ieo_sec_isodd_exit_pre_def];


(* =============================================================== *)

val is_even_1_ht =
  REWRITE_RULE [contract_ev_4_imp_taut_thm] (use_pre_str_rule_simp loop_and_exit_ev_ht contract_ev_4_imp_taut_thm);

val thm1 = ((Q.SPECL [`mutrec`, `bir_exp_true`,
          `BL_Address (Imm32 0w)`, `{BL_Address (Imm32 516w); BL_Address (Imm32 512w)}`, `{}`, `bir_ieo_pre v1`,
          `\l.
            if l = BL_Address (Imm32 0w) then bir_ieo_invariant v1
            else bir_ieo_sec_iseven_exit_post v1 l`,
          `bir_ieo_sec_iseven_exit_post v1`])
	      bir_tsTheory.bir_post_weak_rule_thm);
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
  REWRITE_RULE [contract_od_4_imp_taut_thm] (use_pre_str_rule_simp loop_and_exit_od_ht contract_od_4_imp_taut_thm);

val thm1 = ((Q.SPECL [`mutrec`, `bir_exp_true`,
          `BL_Address (Imm32 0x100w)`, `{BL_Address (Imm32 516w); BL_Address (Imm32 512w)}`, `{}`,
          `bir_ieo_pre v1`,
          `\l.
            if l = BL_Address (Imm32 0w) then bir_ieo_invariant v1
            else bir_ieo_sec_isodd_exit_post v1 l`,
          `bir_ieo_sec_isodd_exit_post v1`])
	      bir_tsTheory.bir_post_weak_rule_thm);
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
