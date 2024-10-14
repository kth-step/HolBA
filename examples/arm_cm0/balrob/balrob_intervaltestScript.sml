open HolKernel Parse boolLib bossLib;

open birs_intervalLib;

open balrob_endsTheory;

val _ = new_theory "balrob_intervaltest";

(* ------------------- *)
(* introduce interval  *)
(* ------------------- *)
(*
val interval_thm = birs_intervals_Pi_unify_RULE "countw" balrob_clzsi2_symb_exec_thm;
*)
(*
val interval_thm = birs_intervals_Pi_RULE "countw" balrob_clzsi2_symb_exec_thm;

Theorem balrob_clzsi2_symb_interval_thm = interval_thm
*)

val _ = export_theory ();
