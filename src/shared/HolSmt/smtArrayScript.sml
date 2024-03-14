open HolKernel Parse boolLib bossLib;

open finite_mapTheory;

val _ = new_theory "smtArray";

val select_def = Q.new_definition("select_def", `select = \arr i. FAPPLY arr i`);
val store_def = Q.new_definition("store_def", `store = \arr i v. FUPDATE arr (i, v)`);
val const_array_def = Q.new_definition("const_array_def", `const_array = \v. FUN_FMAP (K (v)) (UNIV)`);

Theorem apply_to_select_REWR:
  !array index. (FAPPLY array index) = (select array index)
Proof
SIMP_TAC std_ss [select_def]
QED

Theorem update_to_store_REWR:
  !array index value. (FUPDATE array (index, value)) = (store array index value)
Proof
SIMP_TAC std_ss [store_def]
QED

Theorem const_map_to_const_array_REWR:
  !value. (FUN_FMAP (K (value)) (UNIV)) = (const_array value)
Proof
SIMP_TAC std_ss [const_array_def]
QED

val _ = export_theory();

