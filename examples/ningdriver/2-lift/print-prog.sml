open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.linewidth := 100;

val _ = bir_ppLib.install_bir_pretty_printers ();

(*
val _ = Globals.show_tags := true;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
*)

val level_log = ref (logLib.INFO: int)
val {error, warn, info, debug, trace, ...} = logLib.gen_log_fns "print-prog-test" level_log;

fun term_to_ppstring term = (ppstring pp_term) term
fun thm_to_ppstring thm = (ppstring pp_thm) thm
fun pprint_term term = ((print o ppstring pp_term) term; print "\n")
fun pprint_thm thm = ((print o ppstring pp_thm) thm; print "\n")

(* End of prelude
 ****************************************************************************)

(* Configuration *)
val dot_path = "./cfg.dot";
val show_cfg = false;

(* Load the program *)
val _ = info "Loading the program...";
val program_tm = (rhs o concl) examplesBinaryTheory.bir_ningdriver_prog_def;
val _ = info "Done.";

(* Print the program *)
val _ = pprint_term program_tm;

(* Export the CFG *)
val _ = info "Exporting the CFG...";
val _ = bir_old_cfgVizLib.bir_export_graph_from_prog program_tm dot_path;
val _ = if show_cfg then graphVizLib.convertAndView (OS.Path.base dot_path) else ();
val _ = info "Done.";

val _ = info "Now run: 'dot -Tpdf cfg.dot -o cfg.pdf'";
