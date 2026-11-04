(* definitions (also inside libraries) need a current theory, which HOL4 no longer opens by default *)
val _ = Theory.new_theory "scratch";

val _ = print "-------------- INCREMENT --------------\n";
val _ = ex_incrementLib.benchmark (); 

val _ = print "-------------- MEM_INCR ---------------\n";
val _ = ex_mem_incrLib.benchmark ();

val _ = print "-------------- SUM_LIST ---------------\n";
val _ = ex_sum_listLib.benchmark_one_step ();

val _ = print "------------- CV SUM_LIST -------------\n";
val _ = ex_cv_sum_listLib.benchmark_one_step ();

val _ = print "-------------- JUMP_CHAIN -------------\n";
val _ = ex_jump_chainLib.benchmark_one_step ();
