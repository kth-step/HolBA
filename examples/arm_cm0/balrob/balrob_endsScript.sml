open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

val _ = new_theory "balrob_ends";

(* __clzsi2 *)
val reqs = (0,21);
val init_addr = ``0x100013b4w : word32``;
val end_addr = ``0x100013dcw : word32``;

val symb_exec_thm = birs_summary birs_prog_config reqs (init_addr, end_addr);

Theorem balrob_clzsi2_symb_exec_thm = symb_exec_thm

val _ = export_theory ();
