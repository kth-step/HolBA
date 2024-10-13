open HolKernel Parse boolLib bossLib;

(* TODO: for merging, should go into birs_summary_execute later *)
open birs_mergeLib;
open birs_utilsLib;

open balrob_supportLib;

val _ = new_theory "balrob_ends";

(* __clzsi2 *)
val reqs = (0,21);
val init_addr = ``0x100013b4w : word32``;
val end_addrs = [``0x100013dcw : word32``];

val symb_exec_thm = birs_summary_execute birs_prog_config reqs (init_addr, end_addrs);

Theorem balrob_clzsi2_symb_exec_thm = symb_exec_thm

val _ = print_thm balrob_clzsi2_symb_exec_thm;
val _ = print "\n\n";


(* ------------------- *)
(* introduce interval  *)
(* ------------------- *)
val interval_thm = birs_intervalLib.birs_intervals_Pi_RULE "countw" balrob_clzsi2_symb_exec_thm;
Theorem balrob_clzsi2_symb_interval_thm = interval_thm


(* ----------- *)
(* merging     *)
(* ----------- *)
val _ = print "starting merging\n\n\n";
(* move this to balrob_endsScript when interval handling is in place (for countw and SP) *)
val merged_thm = birs_Pi_merge_RULE interval_thm;

fun list_minus eq_fun l1 l2 =
  List.filter (fn x => not (list_in eq_fun x l2)) l1;

(* get conjuncts as list *)
(* check that the path condition has only changed in ways we want *)
val pcond_sysl = (dest_band o get_birs_sys_pcond o concl) merged_thm;
val pcond_Pifl = (dest_band o get_birs_Pi_first_pcond o concl) merged_thm;
val pcond_sys_extral = list_minus term_id_eq pcond_sysl pcond_Pifl;
val pcond_Pif_extral = list_minus term_id_eq pcond_Pifl pcond_sysl;
fun check_extra extra =
  if (length extra = 0) orelse ((length extra = 1) andalso (birsSyntax.is_BExp_IntervalPred (hd extra))) then () else
  raise Fail ("should be none or exactly one conjunct that is a BExp_IntervalPred, something is wrong:" ^ (term_to_string (bslSyntax.bandl extra)));
val _ = check_extra pcond_sys_extral;
val _ = check_extra pcond_Pif_extral;

Theorem balrob_clzsi2_symb_merged_thm = merged_thm

val _ = export_theory ();
