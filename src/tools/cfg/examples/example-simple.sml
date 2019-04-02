open HolKernel Parse boolLib bossLib;
open bslSyntax;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.linewidth := 100;

(*
val _ = Globals.show_tags := true;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
*)

(* Configuration *)
val dot_path = "./simple-test-cfg.dot";
val show_cfg = true;

(* Create a simple BIR program *)
val program_tm = bprog_list alpha [
    (blabel_str "entry", [], (bjmp o belabel_str) "a"),
    (blabel_str "a", [bassign (bvarimm1 "x1", bconst32 1)], bcjmp (bconst1 0, belabel_str "b",
                                                                              belabel_str "d")),
    (blabel_str "b", [bassign (bvarimm1 "x2", bconst32 2)], bcjmp (bconst1 0, belabel_str "c",
                                                                              belabel_str "e")),
    (blabel_str "c", [bassign (bvarimm1 "x3", bconst32 3)], (bjmp o belabel_str) "end"),
    (blabel_str "d", [bassign (bvarimm1 "x4", bconst32 4)], (bjmp o belabel_str) "f"),
    (blabel_str "e", [bassign (bvarimm1 "x5", bconst32 5)], (bjmp o belabel_str) "f"),
    (blabel_str "f", [bassign (bvarimm1 "x6", bconst32 6)], (bjmp o belabel_str) "end"),
    (blabel_str "end", [], bhalt (bconst32 0))
  ];

(* Print the program *)
val _ = print "Here is the program:\n";
val _ = Hol_pp.print_term program_tm;

(* Export the CFG *)
val _ = print "Exporting the CFG...\n";
val _ = bir_cfgVizLib.bir_export_graph_from_prog program_tm dot_path;
val _ = if show_cfg then (
  print "Opening the CFG...\n";
  graphVizLib.convertAndView (OS.Path.base dot_path)
  ) else ();
val _ = print "Done.\n";

