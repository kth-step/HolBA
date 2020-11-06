structure bir_multicoreSyntax :> bir_multicoreSyntax =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_multicoreTheory;

  (**********)
  (* sys_st *)
  (**********)

  val (core_tm, mk_core, dest_core, is_core) = syntax_fns3 "bir_multicore" "core";

  val (mem_tm, mk_mem, dest_mem, is_mem) = syntax_fns1 "bir_multicore" "mem";


end
