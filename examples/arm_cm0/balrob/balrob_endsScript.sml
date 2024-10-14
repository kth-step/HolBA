open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

val _ = new_theory "balrob_ends";

val entry_name = "__clzsi2";
val reqs = get_fun_usage entry_name;
val locs =
  (0x100013b4,
   0x100013dc);

val symb_exec_thm = birs_summary birs_prog_config reqs locs;

Theorem balrob_clzsi2_symb_exec_thm = symb_exec_thm

val _ = export_theory ();
