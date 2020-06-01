open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

open tutorial_compositionTheory;
open tutorialExtra_compositionTheory;
open tutorialExtra2_compositionTheory;

val _ = print "HolBA tutorial example:\n";
val _ = print "===============================\n";
val _ = (Hol_pp.print_thm arm_add_reg_contract_thm; print "\n");
val _ = print "\n\n";

val _ = print "Example \"BIR function reuse\":\n";
val _ = print "===============================\n";
val _ = (Hol_pp.print_thm bir_att_ht; print "\n");
val _ = print "\n\n";

val _ = print "Example \"BIR optimized mutual recursion\" - is_even:\n";
val _ = print "===============================\n";
val _ = (Hol_pp.print_thm bir_ieo_is_even_ht; print "\n");
val _ = print "\n\n";

val _ = print "Example \"BIR optimized mutual recursion\" - is_odd:\n";
val _ = print "===============================\n";
val _ = (Hol_pp.print_thm bir_ieo_is_odd_ht; print "\n");
val _ = print "\n\n";
