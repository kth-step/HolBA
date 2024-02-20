open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* To simplify the life of our poor vim users *)
if !Globals.interactive then let
  val _ = load "HolBA_HolSmtLib";
  val _ = load "tutorial_smtSupportLib";
in () end else ();

(* From examples: *)
open tutorial_smtSupportLib;

if !Globals.interactive then let
  val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
  val _ = Globals.show_tags := true;
  val _ = Globals.linewidth := 100;
  val _ = Feedback.set_trace "HolBA_HolSmtLib" 2;
  val _ = bir_ppLib.install_bir_pretty_printers ();
  (*
  val _ = bir_ppLib.remove_bir_pretty_printers ();
  val _ = Feedback.set_trace "HolBA_HolSmtLib" 0;
  val _ = Feedback.set_trace "HolBA_HolSmtLib" 1;
  val _ = Feedback.set_trace "HolBA_HolSmtLib" 3;
  val _ = Feedback.set_trace "HolBA_HolSmtLib" 4;
  *)
in () end else ();

(* The fun starts here *)

(*****************************************************************************)
(* 1. Prove the truth to check that Z3 is working                            *)

val TRUTH = HolBA_HolSmtLib.Z3_ORACLE_PROVE ``T``;

(* You can raise the trace level to see what is sent to Z3.

val _ = Feedback.set_trace "HolBA_HolSmtLib" 4;
*)

(*****************************************************************************)
(* 2. The arithmetic theory                                                  *)

(* Fix me! *)
val LESS_TRANS = Z3_prove_or_print_model ``!m n p: int. m < n ∧ p < n ==> m < p``;

(*****************************************************************************)
(* 3. The bit-vector theory                                                  *)

(* Fix me! *)
val INC_GREATER = Z3_prove_or_print_model ``!x: word32. x + 1w >+ x``;

(*****************************************************************************)
(* 4. Proving BIR expressions                                                *)

val bir_exp_tm = bandl [
  btrue,
  ble (bplus (bconstii 32 10, bconstii 32 8), bconstii 32 50)
];
val words_exp_tm = bir2bool bir_exp_tm;
val bir_exp_thm = Z3_prove_or_print_model words_exp_tm

