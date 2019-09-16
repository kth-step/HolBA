(*
load "bir_symb_execLib";
load "toyBinaryTheory";
*)

open bir_symb_masterLib;
open toyBinaryTheory;

val maxdepth = (~1);
val precond = ``bir_exp_true``
val prog = (snd o dest_comb o concl) toy_arm8_THM;

val leafs = symb_exec_process_to_leafs_nosmt maxdepth precond prog;

