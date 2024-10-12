open HolKernel Parse boolLib bossLib;

open birs_mergeLib;
open birs_utilsLib;

open balrob_endsTheory;

val _ = new_theory "balrob_ends_merge";

val _ = print_thm balrob_clzsi2_symb_exec_thm;
val _ = print "\n\n";

(* --------------------------- *)
(* merging     *)
(* --------------------------- *)
val _ = print "starting merging\n\n\n";
(* move this to balrob_endsScript when interval handling is in place (for countw and SP) *)
val merged_thm = birs_Pi_merge_RULE balrob_clzsi2_symb_exec_thm;

(* get conjuncts as list *)
(* TODO: this will not be true later when we include countw and stack pointer intervals in the path condition, need to "forward" them into the new path condition and merge them as part of the instantiation *)
val pcond_sysl = (dest_band o get_birs_sys_pcond o concl) merged_thm;
val pcond_Pifl = (dest_band o get_birs_Pi_first_pcond o concl) merged_thm;
val _ = if list_eq_contents term_id_eq pcond_sysl pcond_Pifl then () else
        raise Fail "path condition changed";

Theorem balrob_clzsi2_symb_merged_thm = merged_thm


val _ = export_theory ();
