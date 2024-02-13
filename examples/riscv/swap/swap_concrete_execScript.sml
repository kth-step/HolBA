open HolKernel Parse;

open bir_exec_envLib;
open bir_execLib;
open swapTheory;

val _ = new_theory "swap_concrete_exec";

val _ = export_theory ();
