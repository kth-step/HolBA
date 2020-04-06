open HolKernel Parse boolLib bossLib;
open bslSyntax;
open birExamplesBinaryTheory;
open bir_wm_instTheory;
open bin_hoare_logicTheory;
open bir_valuesTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_exp_equivTheory;
open bir_programTheory;

open tutorial_compositionLib;
open tutorial_wpSupportLib;

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
  SIMP_RULE std_ss [pred_setTheory.IN_SING]

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

val bir_ieo_sec_iseven_1_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_ieo_sec_iseven_1_ht)
    contract_1_imp_taut_thm;

val bir_ieo_sec_isodd_1_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_ieo_sec_isodd_1_ht)
    contract_2_imp_taut_thm;


(* =============================================================== *)


val _ = export_theory();
