open HolKernel Parse boolLib bossLib;

open birs_mergeLib;

open balrob_endsTheory;

val _ = new_theory "balrob_ends_merge";

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag balrob_clzsi2_symb_analysis_thm);
val _ = print_thm balrob_clzsi2_symb_analysis_thm;
val _ = print "\n\n";

(* --------------------------- *)
(* merging     *)
(* --------------------------- *)
val _ = print "starting merging\n\n\n";

val merged_thm = birs_Pi_merge_RULE balrob_clzsi2_symb_analysis_thm;

(* get conjuncts as list *)
val pcond_sysl = (dest_band o get_birs_sys_pcond o concl) merged_thm;
val pcond_Pifl = (dest_band o get_birs_Pi_first_pcond o concl) merged_thm;
val _ = if list_eq_contents term_id_eq pcond_sysl pcond_Pifl then () else
        raise Fail "path condition changed";

val _ = Portable.pprint Tag.pp_tag (tag merged_thm);
val _ = print_thm merged_thm;

Theorem balrob_clzsi2_symb_merged_thm = merged_thm


val _ = export_theory ();
