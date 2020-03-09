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


  val ht_assmpt = ``((v3:word32) <> 260w) /\ ((v4:word32) <> 260w) /\ (v4 <> v3)``;

  val ht1 = bir_att_sec_add_1_comp_ht;

  val ht2 = 
    (HO_MATCH_MP bir_label_ht_impl_weak_ht ((UNDISCH o UNDISCH o (Q.SPECL [`v1`, `v2`, `v3`, `v4`])) bir_att_sec_add_2_ht));

  val def_list = [bprog_add_times_two_def, bir_att_sec_add_2_post_def,
		  bir_att_sec_add_1_post_def];

val bir_att_sec_add_ht =
   bir_compose_nonmap_seq_assmpt ht1 ht2 ht_assmpt def_list (get_labels_from_set_repr, el_in_set_repr,
                                            mk_set_repr, simp_delete_set_repr_rule,
	                                    simp_insert_set_repr_rule,
                                            simp_in_sing_set_repr_rule,
                                            simp_inter_set_repr_rule);

(* ====================================== *)
(* call 1 *)
val bir_att_sec_add_0x4_ht = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x004w:word32``,
                                      ``v4:word32`` |-> ``0x008w:word32``])))
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
(* introduce dummy address 0x200 (hack for simplification) *)
val bir_att_sec_add_0x8_ht = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x008w:word32``,
                                      ``v4:word32`` |-> ``0x200w:word32``,
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
(*
local
open tutorial_smtSupportLib;
in
val bir_att_sec_call_1_taut = prove_exp_is_taut
       (bimp (``bir_att_sec_add_2_post v1 v2``, ``bir_att_sec_call_2_pre (v1+v2)``));
end

val contract_2_imp_taut_thm = save_thm ("contract_2_imp_taut_thm",
  prove_exp_is_taut contract_2_imp);

val bir_att_sec_call_1_map_ht_fix =
 bir_att_sec_call_1_map_ht;
(* TODO: need theorem and procedure for implied-rule on bir_map_triple *)

val bir_att_sec_call_2_map_ht_fix =
(INST [``v1:word32`` |-> ``(v1:word32) + (v2:word32)``])
bir_att_sec_call_2_map_ht;

val bir_att_body_map_ht =
bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
bir_att_sec_call_1_map_ht_fix
bir_att_sec_call_2_map_ht_fix
                def_list;



val bir_att_sec_call_2_comp_ht =
  use_impl_rule
    bir_att_sec_call_1_map_ht
    bir_att_sec_call_1_taut;
*)


(* ====================================== *)
(* final composition *)
(*
local
open tutorial_smtSupportLib;
in
val bir_att_post_taut = prove_exp_is_taut
       (bimp (``bir_att_sec_add_2_post (v1 + v2) (v1 + v2)``, ``bir_att_sec_2_post v1 v2``));
end

*)

(*
val assmpt = ht_assmpt
val map_triple = (bir_map_triple_from_bir_triple ht1)
val post = 	  (get_bir_map_triple_post map_triple);
val (_::h::t) = 	  (get_labels_from_set_repr (get_bir_map_triple_wlist map_triple));
*)

val _ = export_theory();

