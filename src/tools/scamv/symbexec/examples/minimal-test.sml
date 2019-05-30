(*
load "bir_symb_execLib";
load "toyBinaryTheory";
*)

open bir_symb_execLib;
open toyBinaryTheory;

val prog = (snd o dest_comb o concl) toy_arm8_THM;
val tree = symb_exec_program prog;

