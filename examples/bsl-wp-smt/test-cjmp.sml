open HolKernel Parse boolLib bossLib;
open bslSyntax;
open pretty_exnLib;

(* Load dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "easy_noproof_wpLib"; (* ../lib *)
  load "HolSmtLib"; (* HOL/src/HolSmt *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 0;
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 2;
val _ = Feedback.set_trace "easy_noproof_wpLib" logLib.TRACE;
val _ = Feedback.set_trace "Define.storage_message" 1;
*)

(* BIR program *)
val _ = print "Defining BIR program...\n";
val cjmp_prog_def = bdefprog_list alpha "cjmp_prog" [
  (blabel_str "entry", [], (bjmp o belabel_str) "assign_x_1"),

  (blabel_str "assign_x_1", [
    bassign (bvarimm32 "x", bconst32 1)
  ], (bjmp o belabel_str) "cjmp"),

  (blabel_str "cjmp", [],
    bcjmp (beq ((bden o bvarimm32) "x", bconst32 1),
           belabel_str "assign_y_100",
           belabel_str "assign_y_200")),

  (blabel_str "assign_y_100", [
    bassign (bvarimm32 "y", bconst32 100)
  ], (bjmp o belabel_str) "epilogue"),

  (blabel_str "assign_y_200", [
    bassign (bvarimm32 "y", bconst32 200)
  ], (bjmp o belabel_str) "epilogue"),

  (blabel_str "epilogue", [], (bjmp o belabel_str) "end"),
  (blabel_str "end", [], bhalt (bconst32 0))
];
val _ = (Hol_pp.print_thm cjmp_prog_def; print "\n");
val _ = print "Done!\n";

val show_cfg = false;
val dot_path = "./cjmp-test.dot";
val _ = if not show_cfg then () else
  let
    val _ = bir_cfgVizLib.bir_export_graph_from_prog ((snd o dest_eq o concl) cjmp_prog_def) dot_path;
    val _ = graphVizLib.convertAndView (OS.Path.base dot_path);
  in () end;

(* *)
val cjmp_thm =
  let
    (* prog + P + Q => ``P ==> WP`` *)
    val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm "cjmp"
      (* prog_def *) cjmp_prog_def
      (* Precondition *) (
        blabel_str "entry",
        bconst1 1
      )
      (* Postconditions *) (
        [blabel_str "end"],
        beq ((bden o bvarimm32) "y", bconst32 100)
      )
      handle e => raise pp_exn_s "compute_p_imp_wp_tm failed" e

    (* BIR expr => SMT-ready expr*)
    val smt_ready_tm = bir_exp_to_wordsLib.bir2bool p_imp_wp_bir_tm
      handle e => raise pp_exn_s "bir2bool failed" e

    val _ = (Hol_pp.print_term smt_ready_tm; print "\n")
  in
    HolSmtLib.Z3_ORACLE_PROVE smt_ready_tm
      handle e => raise pp_exn_s "Z3_ORACLE_PROVE failed" e
  end;
val _ = (Hol_pp.print_thm cjmp_thm; print "\n");
