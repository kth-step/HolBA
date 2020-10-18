open HolKernel Parse boolLib bossLib;

open finite_mapTheory;

val _ = new_theory "smtArray";

val select_def = Q.new_definition("select_def", `select = \arr i. FAPPLY arr i`);
val store_def = Q.new_definition("store_def", `store = \arr i v. FUPDATE arr (i, v)`);

val apply_to_select_REWR = store_thm ("apply_to_select_REWR",
  ``!array index. (FAPPLY array index) = (select array index)``,
  SIMP_TAC std_ss [select_def]
);

val update_to_store_REWR = store_thm ("update_to_store_REWR",
  ``!array index value. (FUPDATE array (index, value)) = (store array index value)``,
  SIMP_TAC std_ss [store_def]
);

val _ = export_theory();

