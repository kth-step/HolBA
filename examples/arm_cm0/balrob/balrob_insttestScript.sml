open HolKernel Parse boolLib bossLib;

open birs_instantiationLib;
open birs_composeLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_insttest";

(* instantiation test *)
val reqs = (0,63);
val init_addr = ``0x100012d6w : word32``;
val end_addrs = [``0x100013b4w : word32``];

val symb_exec_thm = birs_summary_execute birs_prog_config reqs (init_addr, end_addrs);

Theorem balrob_insttest_symb_exec_thm = symb_exec_thm


(* now try to instantiate *)
val _ = print "prepare generic SEQ thm\n";
val bprog_tm = (fst o dest_eq o concl) balrobLib.bir_balrob_prog_def;
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;

val A_thm = balrob_insttest_symb_exec_thm;
val B_thm = balrob_clzsi2_symb_merged_thm;
(*
val _ = print_thm A_thm;
val _ = print_thm B_thm;
*)

val _ = print "start instantiation\n";
val cont_thm = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm bir_symbLib.pcond_gen_symb A_thm B_thm;

Theorem balrob_insttest_symb_inst_thm = cont_thm

(* now continue execution after that *)

val _ = export_theory ();


