open HolKernel Parse boolTheory boolLib pairTheory

open HolKernel Parse boolLib bossLib;
open bir_bool_expSyntax;
open bir_exp_substitutionsSyntax;
open bir_extra_expsSyntax;
open bir_interval_expSyntax;

val _ = print "HolBA bir-support files successfully loaded.\n";

val _ = Process.exit Process.success;
