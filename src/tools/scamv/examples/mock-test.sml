open HolKernel Parse boolLib bossLib;
open bir_exp_to_wordsLib;
open bir_rel_synthLib;
open bslSyntax;
open wordsSyntax;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "../Z3_SAT_modelLib"; (* ../ *)
  load "../bir_exp_to_wordsLib"; (* ../ *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Globals.show_assums := true;
val _ = Globals.show_types := true;
*)

val cond = bandl [ble (bconst64 (0x30000 + 0x80000000),
                       bden (bvarimm64 "R1")),
                  ble (bden (bvarimm64 "R1"), bconst64 (0x42ff8 + 0x80000000)),
                  (*``BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64)))``*)
                  beq (
                    band ((bden o bvarimm64) "R1", bconst64 0xF),
                    bconst64 0
                  )
                 ];

val bir_true = ``BExp_Const (Imm1 1w)``;

val prog_obss_paths =
    [
      (bnot cond, NONE),
      (cond,
       SOME [
           (bir_true, ``BExp_BinExp BIExp_And
                        (BExp_Const (Imm64 0x1FC0w))
                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))``)
      ])
    ];

val relation = mkRel prog_obss_paths;

(* Prints a model, one variable per line. *)
fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

fun to_sml_ints model = List.map (fn (name, tm) => (name, uint_of_word tm)) model;

(*val word_relation = bir2bool relation;*)
val word_relation = ``^(bir2bool relation) /\ (R1 <> R1')``;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));

val sml_model = to_sml_ints model;

