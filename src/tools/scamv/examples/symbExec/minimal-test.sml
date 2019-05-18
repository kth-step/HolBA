(*
load "bir_symb_execLib";
load "toyBinaryTheory";
*)

open bir_symb_execLib;
open toyBinaryTheory;

val prog = (snd o dest_comb o concl) toy_arm8_THM;
val tree = symb_exec_program prog;

val _ = print "Failing states:\n";
val _ = print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";
val _ = ((List.map print_term) o snd) tree;


