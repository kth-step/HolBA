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

open tutorial_bir_to_armTheory;

open tutorial_compositionLib;
open tutorial_wpSupportLib;

open tutorialExtra_wpTheory;
open tutorialExtra_smtTheory;

open bir_auxiliaryLib;

open HolBACoreSimps;
open HolBASimps;
open bin_hoare_logicSimps;

val _ = new_theory "tutorialExtra_composition";

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


val bir_att_sec_add_1_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_att_sec_add_1_ht)
    contract_1_imp_taut_thm;

val bir_att_sec_call_1_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_att_sec_call_1_ht)
    contract_2_imp_taut_thm;

val bir_att_sec_call_2_comp_ht =
  use_pre_str_rule
    (HO_MATCH_MP bir_label_ht_impl_weak_ht bir_att_sec_call_2_ht)
    contract_3_imp_taut_thm;




(* TODO: in composition function, make conditional "return" jump work *)
(* TODO: enable usage of variable blacklist set with assumptions -> bigger compositional reasoning *)

fun try_disch_all_assump_w_EVAL t =
  let
    val t_d      = DISCH_ALL t;
    val assum_tm = (fst o dest_imp o concl) t_d;
    val t_as     = EVAL assum_tm;
    val t2       = REWRITE_RULE [t_as] (DISCH assum_tm t)
  in
    try_disch_all_assump_w_EVAL t2
  end
  handle HOL_ERR _ => t;


(* ====================================== *)
(* ADD function *)
  val ht_assmpt = ``(FINITE v4s) /\
                    ((BL_Address (Imm32 v3)) NOTIN v4s) /\
                    ((BL_Address (Imm32 260w)) NOTIN ((BL_Address (Imm32 v3)) INSERT v4s))``;

  val assumes = ASSUME ht_assmpt;

val notin_insert_thm = prove(``(A NOTIN (B INSERT C)) ==> (A NOTIN C)``, 
  Cases_on `A = B` >> (
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
  )
);
  val fix3_thm = (UNDISCH_ALL o prove) (``
^ht_assmpt ==>
(!l.
          l IN BL_Address (Imm32 v3) INSERT v4s ==>
          ((if l = BL_Address (Imm32 260w) then
              bir_att_sec_add_1_post v1 v2 v3
            else bir_exp_false) =
           bir_exp_false))``,
  REPEAT STRIP_TAC >>
  CASE_TAC >>
  METIS_TAC []
);
  val fix3_2_thm = (UNDISCH_ALL o prove) (``
^ht_assmpt ==>
(!l.
          l IN v4s ==>
          ((if l = BL_Address (Imm32 v3) then
              bir_att_sec_add_2_post v1 v2
            else bir_exp_false) =
           bir_exp_false))``,
  REPEAT STRIP_TAC >>
  CASE_TAC >>
  METIS_TAC []
);


  fun fix_assmt map_ht =
    REWRITE_RULE [(SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) [assumes] o
                  fst o dest_imp o concl) map_ht] map_ht;
  fun fix_assmt2 map_ht =
    REWRITE_RULE [(SIMP_CONV (std_ss) [assumes, pred_setTheory.SUBSET_OF_INSERT] o
                  fst o dest_imp o concl) map_ht] map_ht;
  fun fix_assmt3 map_ht =
    REWRITE_RULE [(SIMP_CONV (std_ss) [fix3_thm, fix3_2_thm] o
                  fst o dest_imp o concl) map_ht] map_ht;

  fun populate_blacklist_set_hack elabels map_ht =
    let
  val map_ht1 =
  ((SPEC elabels) o
   (HO_MATCH_MP bir_map_triple_move_set_to_blacklist))
  map_ht;
  val map_ht1_1 = fix_assmt map_ht1;
  val map_ht1_2 = fix_assmt2 map_ht1_1;
  val map_ht1_3 = fix_assmt3 map_ht1_2;
  val map_ht1 = REWRITE_RULE [pred_setTheory.UNION_EMPTY,
                              pred_setTheory.INSERT_DIFF,
                              pred_setTheory.COMPONENT,
                              (REWRITE_RULE [pred_setTheory.SUBSET_OF_INSERT]
                               (Q.SPECL [`a`,`b INSERT a`] pred_setTheory.SUBSET_DIFF_EMPTY)),
                              pred_setTheory.DIFF_EQ_EMPTY,
                              assumes]
                             map_ht1_3
    in
      map_ht1
    end;

  val ht1 = bir_att_sec_add_1_comp_ht;
  val map_ht1_ = bir_map_triple_from_bir_triple ht1;

  val elabels = ``(BL_Address (Imm32 v3)) INSERT v4s``;
  val map_ht1 = populate_blacklist_set_hack elabels map_ht1_;

  val ht2 = 
    (HO_MATCH_MP bir_label_ht_impl_weak_ht ((UNDISCH o UNDISCH o (Q.SPECL [`v1`, `v2`, `v3`, `v4s`])) bir_att_sec_add_2_ht));
  val map_ht2_ = bir_map_triple_from_bir_triple ht2;

  val elabels = ``v4s:bir_label_t->bool``;
  val map_ht2 = populate_blacklist_set_hack elabels map_ht2_;



  val def_list = [bprog_add_times_two_def, bir_att_sec_add_2_post_def,
		  bir_att_sec_add_1_post_def];

  val assmpt = ht_assmpt;
  val bir_att_sec_add_ht = bir_compose_seq_assmpt (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                                           simp_inter_set_repr_rule)
                           map_ht1 map_ht2 def_list assmpt;




(* ====================================== *)
(* call 1 *)
val bir_att_sec_add_0x4_ht = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x004w:word32``,
                                      ``v4s:bir_label_t->bool`` |-> ``{BL_Address (Imm32 0x008w)}``])))
                             bir_att_sec_add_ht;

val bir_att_sec_call_1_comp_map_ht =
REWRITE_RULE [(EVAL THENC
(REWRITE_CONV [GSYM (EVAL ``bir_att_sec_add_1_pre v1 v2 4w``)]))
``bir_att_sec_call_1_post v1 v2``]
(
          bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                 (bir_map_triple_from_bir_triple bir_att_sec_call_1_comp_ht)
)

val bir_att_sec_call_1_map_ht =
bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
                bir_att_sec_call_1_comp_map_ht
                bir_att_sec_add_0x4_ht
                def_list;




(* ====================================== *)
(* call 2 *)
val bir_att_sec_add_0x8_ht = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x008w:word32``,
                                      ``v4s:bir_label_t->bool`` |-> ``{}:bir_label_t->bool``,
                                      ``v2:word32`` |-> ``v1:word32``])))
                             bir_att_sec_add_ht;

val bir_att_sec_call_2_comp_map_ht =
REWRITE_RULE [(EVAL THENC
(REWRITE_CONV [GSYM (EVAL ``bir_att_sec_add_1_pre v1 v1 8w``)]))
``bir_att_sec_call_2_post v1``]
(
          bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                 (bir_map_triple_from_bir_triple bir_att_sec_call_2_comp_ht)
)

val bir_att_sec_call_2_map_ht =
bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
                bir_att_sec_call_2_comp_map_ht
                bir_att_sec_add_0x8_ht
                def_list;




(* ====================================== *)
(* composition of the function body *)
val bir_att_sec_call_1_map_ht_fix =
  bir_att_sec_call_1_map_ht;

val bir_att_sec_call_2_map_ht_inst =
  (INST [``v1:word32`` |-> ``(v1:word32) + (v2:word32)``])
  bir_att_sec_call_2_map_ht;

val bir_att_sec_call_2_map_ht_fix =
  use_pre_str_rule_map
    bir_att_sec_call_2_map_ht_inst
    bir_att_sec_call_1_taut_thm;


val bir_att_body_map_ht =
  bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                   simp_inter_set_repr_rule)
    bir_att_sec_call_1_map_ht_fix
    bir_att_sec_call_2_map_ht_fix
    def_list;


(* experiment with post condition weakening *)
val map_ht_thm =     bir_att_sec_call_1_map_ht
val post1_impl_post2 =    bir_att_sec_call_1_taut_thm;
val l2 = ``BL_Address (Imm32 4w)``;

val bir_att_sec_call_1_map_ht_alt =
  use_post_weak_rule_map map_ht_thm l2 post1_impl_post2;

val bir_att_body_map_ht_alt =
  bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                   simp_inter_set_repr_rule)
    bir_att_sec_call_1_map_ht_alt
    bir_att_sec_call_2_map_ht_inst
    def_list;

val _ = if concl bir_att_body_map_ht_alt = concl bir_att_body_map_ht then
          ()
        else
          raise ERR "composition of example code" "composition using two types of contract weakening does not give the same result";

(* ====================================== *)
(* final composition, needs post condition weakening *)
val bir_att_post_ht =
  use_post_weak_rule_map
    bir_att_body_map_ht_alt
    ``BL_Address (Imm32 8w)``
    bir_att_post_taut_thm;


(* ====================================== *)
(* store theorem after final composition *)
val bir_att_ht = save_thm("bir_att_ht",
  REWRITE_RULE [bir_att_sec_2_post_def, bir_att_sec_call_1_pre_def] bir_att_post_ht
);

val _ = export_theory();

