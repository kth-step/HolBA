open ex_jump_chainLib;

(* definitions (also inside libraries) need a current theory, which HOL4 no longer opens by default *)
val _ = Theory.new_theory "scratch";

val _ = benchmark_one_step ();
