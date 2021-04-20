open HolKernel Parse boolLib bossLib;

open bslSyntax bir_execLib;

open resolveTheory;

val _ = new_theory "examples";


val observe_type = Type `: 'a`
val bdefprog_list = bdefprog_list observe_type

val block1 = (blabel_addr32 0,
              [bassign (bvarimm32 "y", bconst32 4)],
              (bjmp o belabel_expr o bden o bvarimm32) "y")

val block2: term * term list * term  = (blabel_addr32 4, [], (bhalt o bconst32) 0)

val prog_def = bdefprog_list "prog" [block1, block2]
val prog = (snd o dest_eq o concl) prog_def

val n_max = 10;
val _ = bir_exec_prog_print "prog" prog n_max NONE NONE NONE;

val prog'_def = EVAL “resolve_fail ^prog (BL_Address (Imm32 0w))”
val prog' = (dest_some o snd o dest_eq o concl) prog'_def

val _ = bir_exec_prog_print "prog'" prog' n_max NONE NONE NONE;

val prog'_def = EVAL “resolve ^prog (BL_Address (Imm32 0w)) (Imm32 10w) "fresh"”
val prog' = (dest_some o snd o dest_eq o concl) prog'_def

(*val _ = bir_exec_prog_print "prog'" prog' n_max NONE NONE NONE;*)


val _ = export_theory();

