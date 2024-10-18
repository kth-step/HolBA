open HolKernel Parse boolLib bossLib;

open bir_symbLib;
open birs_mergeLib;

open distribute_generic_stuffTheory;

open swapTheory;
open swap_specTheory;

val _ = new_theory "swap_symb_exec";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_swap_prog_def
  swap_init_addr_def [swap_end_addr_def]
  bspec_swap_pre_def swap_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);
val _ = print_thm symb_analysis_thm;
val _ = print "\n\n";

(* !!! now merge *)
val _ = print "starting merging\n\n\n";

val merged_thm = birs_Pi_merge_RULE symb_analysis_thm;

(* get conjuncts as list *)
val pcond_sysl = (dest_bandl o get_birs_sys_pcond o concl) merged_thm;
val pcond_Pifl = (dest_bandl o get_birs_Pi_first_pcond o concl) merged_thm;
val _ = if list_eq_contents term_id_eq pcond_sysl pcond_Pifl then () else
        raise Fail "path condition changed";

val _ = Portable.pprint Tag.pp_tag (tag merged_thm);
val _ = print_thm merged_thm;

val _ = export_theory ();
