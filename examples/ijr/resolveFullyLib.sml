structure resolveFullyLib =
struct
open HolKernel Parse boolLib bossLib;

open optionSyntax bir_htSyntax;

open resolveFullyTheory;

fun resolve_indirect_jumps(prog_tm, args) =
  let
    val prog'_thm = EVAL “resolve_fully_n ^prog_tm ^args”
    val prog'_tm = (dest_some o rhs o concl) prog'_thm
    val prog'_var = mk_var("prog'", type_of prog'_tm)
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

end
