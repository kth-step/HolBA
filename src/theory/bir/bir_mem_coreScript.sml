open HolKernel Parse boolLib bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;

val _ = new_theory "bir_mem_core";

val _ = export_theory ();

