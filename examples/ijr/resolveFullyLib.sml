structure resolveFullyLib =
struct
open HolKernel Parse boolLib bossLib;

open optionSyntax bir_htSyntax;

open bir_wp_interfaceLib;
open tutorial_smtSupportLib;
open bir_compositionLib;

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
    (prog'_tm', prog'_def, prog'_thm')
  end

fun transfer_contract(prog_tm, prog'_thm, ht_thm) =
  let
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

fun prove_and_transfer_contract(prog_tm, prog'_tm, prog'_thm, prefix, pre_tm, entry_label_tm, ending_labels_tm, post_tm, defs) =
  let
    val wp_start = timer_start ()
    (*Obtain WP contract*)
    val (ht_thm, wp_tm) =
      bir_obtain_ht 
        prog'_tm entry_label_tm
        ending_labels_tm ending_set_to_sml_list
        post_tm postcond_exp_from_label
        prefix defs
    val _ = print ("WP time: " ^ timer_stop_str wp_start ^ "\n")
    
    val wp_var = mk_var(prefix ^ "_wp", type_of wp_tm)
    val wp_def = Define `^(wp_var) = ^(wp_tm)`
    val ht_thm' = REWRITE_RULE [GSYM wp_def] ht_thm
    
    (*Transfer WP contract*)
    val transfer_start = timer_start ()
    val ht'_thm = transfer_contract(prog_tm, prog'_thm, ht_thm')
    val _ = print ("Transfer time: " ^ timer_stop_str transfer_start ^ "\n")

    (*Prove implication using SMT solvers*)
    val smt_start = timer_start ()
    val contract_imp = bimp (pre_tm, (lhs o concl) wp_def)
    val contract_imp_taut_thm = prove_exp_is_taut contract_imp
    val res = label_ct_to_simp_ct_predset ht'_thm contract_imp_taut_thm
    val _ = print ("SMT time: " ^ timer_stop_str smt_start ^ "\n")
  in
    res
  end

end
