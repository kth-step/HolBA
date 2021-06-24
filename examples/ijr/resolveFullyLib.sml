structure resolveFullyLib =
struct
open HolKernel Parse boolLib bossLib;

open optionSyntax bir_htSyntax bir_wm_instSyntax;

open bir_wp_interfaceLib;
open tutorial_smtSupportLib;
open bir_compositionLib;

open listTheory;
open resolveFullyTheory;
open timersLib;

fun resolve_indirect_jumps(prog'_name, prog_tm, args) =
  let
    val prog'_thm = EVAL “resolve_fully_n ^prog_tm ^args”
    val prog'_tm = (dest_some o rhs o concl) prog'_thm
    val prog'_var = mk_var(prog'_name, type_of prog'_tm)
    val prog'_def = Define `^prog'_var = ^prog'_tm`
    val prog'_tm' = (lhs o concl) prog'_def
    val prog'_thm' = REWRITE_RULE [GSYM prog'_def] prog'_thm
  in
    (prog'_def, prog'_thm')
  end

fun transfer_bir_exec_to_labels_triple(prog'_thm, ht_thm) =
  let
    val prog_tm = (el 1 o snd o strip_comb o lhs o concl) prog'_thm
    val ht_tm = concl ht_thm
    val (_, entry_tm, exits_tm, _, _) = dest_bir_exec_to_labels_triple ht_tm
    val entry_thm = prove (
      “MEM ^entry_tm (bir_labels_of_program ^prog_tm)”,
      EVAL_TAC)
    val ending_thm = prove (
      “^exits_tm SUBSET (set (bir_labels_of_program ^prog_tm))”,
      EVAL_TAC)
    val res_thm = MATCH_MP resolve_fully_n_contract_transfer prog'_thm
    val res_thm = MATCH_MP res_thm entry_thm
    val res_thm = MATCH_MP res_thm ending_thm
  in
    MATCH_MP res_thm ht_thm
  end

fun transfer_contract(prog'_thm, ht_thm) =
  let
    val prog_tm = (el 1 o snd o strip_comb o lhs o concl) prog'_thm
    val ht_tm = concl ht_thm
    val (_, _, entry_tm, wl_tm, bl_tm, _, _) = dest_bir_simp_jgmt ht_tm
    val entry_thm = prove (
      “MEM ^entry_tm (bir_labels_of_program ^prog_tm)”,
      EVAL_TAC)
    val wl_thm = prove (
      “^wl_tm SUBSET (set (bir_labels_of_program ^prog_tm))”,
      EVAL_TAC)
    val bl_thm = prove (
      “^bl_tm SUBSET (set (bir_labels_of_program ^prog_tm))”,
      EVAL_TAC)
    val res_thm = MATCH_MP resolve_fully_n_bir_simp_jgmt_transfer prog'_thm
    val res_thm = MATCH_MP res_thm entry_thm
    val res_thm = MATCH_MP res_thm wl_thm
    val res_thm = MATCH_MP res_thm bl_thm
  in
    MATCH_MP res_thm ht_thm
  end

fun prove_and_transfer_contract(prog'_thm, prefix, pre_tm, entry_label_tm, ending_labels_tm, post_tm, defs) =
  let
    (*Add exit points*)
    val args_tm = (el 2 o snd o strip_comb o lhs o concl) prog'_thm
    val bl_tm1 = EVAL “set (MAP (BL_Label o SND o LAST o SND) ^args_tm)”
    val bl_tm2 = REWRITE_RULE [LIST_TO_SET] bl_tm1
    val bl_tm3 = (rhs o concl) bl_tm2
    val ending_labels_tm = (rhs o concl o EVAL) “^ending_labels_tm UNION ^bl_tm3”

    val wp_start = timer_start ()
    val prog'_tm = (dest_some o rhs o concl) prog'_thm
    (*Obtain WP contract*)
    val (ht_thm, wp_tm) =
      bir_obtain_ht 
        prog'_tm entry_label_tm
        ending_labels_tm ending_set_to_sml_list
        post_tm postcond_exp_from_label
        prefix defs
    val _ = print ("WP time: " ^ timer_stop_str wp_start ^ "\n")
    
    (*Simplify WP contract*)
    val wp_var = mk_var(prefix ^ "_wp", type_of wp_tm)
    val wp_def = Define `^(wp_var) = ^(wp_tm)`
    val ht_thm' = REWRITE_RULE [GSYM wp_def] ht_thm
    
    (*Prove implication using SMT solvers*)
    val smt_start = timer_start ()
    val contract_imp = bimp (pre_tm, (lhs o concl) wp_def)
    val contract_imp_taut_thm = prove_exp_is_taut contract_imp
    val contract = label_ct_to_simp_ct_predset ht_thm' contract_imp_taut_thm
    val _ = print ("SMT time: " ^ timer_stop_str smt_start ^ "\n")

    (*Remove new exit points*)
    val contract = bir_remove_labels_from_blist_predset contract bl_tm3

    (*Transfer WP contract*)
    val transfer_start = timer_start ()
    val contract = transfer_contract(prog'_thm, contract)
    val _ = print ("Transfer time: " ^ timer_stop_str transfer_start ^ "\n")
  in
    contract
  end

end
