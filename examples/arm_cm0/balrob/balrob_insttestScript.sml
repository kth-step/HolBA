open HolKernel Parse boolLib bossLib;

open birs_utilsLib;
open birs_instantiationLib;
open birs_composeLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_insttest";

(* insttest *)
val reqs = (0,63);
val locs =
  (0x100012d6,
   0x100013b4);

val symb_exec_thm = birs_summary birs_prog_config reqs locs;

Theorem balrob_summary_insttest_thm = symb_exec_thm


(* now instantiate *)
val A_thm = balrob_summary_insttest_thm;
val B_thm = balrob_summary___clzsi2_thm;
val inst_thm = birs_basic_instantiate birs_prog_config A_thm B_thm;

Theorem balrob_insttest_symb_inst_thm = inst_thm

val _ = export_theory ();


