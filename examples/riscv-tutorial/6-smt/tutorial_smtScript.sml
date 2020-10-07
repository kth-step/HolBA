open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* To simplify the life of our poor vim users *)
if !Globals.interactive then let
  val _ = load "HolSmtLib";
  val _ = load "tutorial_bir_to_armTheory";
  val _ = load "tutorial_wpTheory";
  val _ = load "tutorial_smtSupportLib";
in () end else ();

(* From examples: *)
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;
open tutorial_smtSupportLib;

if !Globals.interactive then let
  val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
  val _ = Globals.show_tags := true;
  val _ = Globals.linewidth := 100;
  val _ = Feedback.set_trace "HolSmtLib" 2;
  val _ = bir_ppLib.install_bir_pretty_printers ();
  (*
  val _ = bir_ppLib.remove_bir_pretty_printers ();
  val _ = Feedback.set_trace "HolSmtLib" 0;
  val _ = Feedback.set_trace "HolSmtLib" 1;
  val _ = Feedback.set_trace "HolSmtLib" 3;
  val _ = Feedback.set_trace "HolSmtLib" 4;
  *)
in () end else ();

val _ = new_theory "tutorial_smt";

(*****************************************************************************)
(* 1.1. Prove Hoare triples                                                  *)

(* (1) bir_add_reg_entry
 * 
 * Hoare triple: {T} entry {I}
 *
 * So we need to show that: T ==> WP(I, entry)
 *)
val contract_1_pre = btrue;
val contract_1_wp  = (lhs o concl) bir_add_reg_entry_wp_def;
val contract_1_imp = bimp (contract_1_pre, contract_1_wp);

val contract_1_imp_taut_thm = prove_exp_is_taut contract_1_imp
  handle e => (print "This didn't work.\n"; TRUTH);

(* Oh my, that didn't work!
 *
 * Note: We use `TRUTH` in the handle statement for type-correctness.
 * In normal proofs, we wouldn't have failing proofs, so that's just
 * a hack here.
 * 
 * If proving `P ==> WP` fails, and WP is indeed the weakest precondition,
 * then the reason must be that the precondition isn't strong enough.
 *
 * Of course, `T` is the weakest possible precondition, so we need a
 * stronger one: `x >= 0` (actually it's more complicated, you can
 * evaluate `bir_add_reg_contract_1_pre_def` to see the actual
 * precondition).
 *
 * Hoare triple: {x >= 0} entry {I}
 *)

val contract_1_pre = (lhs o concl) bir_add_reg_contract_1_pre_def;
val contract_1_imp = bimp (contract_1_pre, contract_1_wp);

val contract_1_imp_taut_thm = save_thm ("contract_1_imp_taut_thm",
  prove_exp_is_taut contract_1_imp);

(*********************************)

(* (2) bir_add_reg_loop_variant
 * 
 * Hoare triple: {I /\ C /\ lx = v} loop {I /\ 0 <= lx < v}
 *
 * Note: We need to specialize the definitions for the variants because
 * of the free variable.
 *)
val contract_2v_freevar = mk_var ("v", Type `:word64`)
val contract_2v_pre = (lhs o concl o (SPEC contract_2v_freevar))
  bir_add_reg_contract_2_pre_variant_def;
val contract_2v_wp  = (lhs o concl o (SPEC contract_2v_freevar))
  bir_add_reg_loop_variant_wp_def;
val contract_2v_imp = bimp (contract_2v_pre, contract_2v_wp);

val contract_2v_imp_taut_thm = save_thm ("contract_2v_imp_taut_thm",
  prove_exp_is_taut contract_2v_imp);

(*********************************)

(* (3) bir_add_reg_loop_continue_variant
 * 
 * Hoare triple: {I /\ C /\ lx = v} loop {I /\ C /\ lx = v}
 *)
val contract_3v_freevar = mk_var ("v", Type `:word64`)
val contract_3v_pre = (lhs o concl o (SPEC contract_3v_freevar))
  bir_add_reg_contract_3_pre_variant_def;
val contract_3v_wp  = (lhs o concl o (SPEC contract_3v_freevar))
  bir_add_reg_loop_continue_variant_wp_def;
val contract_3v_imp = bimp (contract_3v_pre, contract_3v_wp);

val contract_3v_imp_taut_thm = save_thm ("contract_3v_imp_taut_thm",
  prove_exp_is_taut contract_3v_imp);

(*********************************)

(* (4) bir_add_reg_loop_exit
 * 
 * Hoare triple: {I /\ ~C} loop {Q}
 *)
val contract_4_pre = (lhs o concl) bir_add_reg_contract_4_pre_def;
val contract_4_wp  = (lhs o concl) bir_add_reg_loop_exit_wp_def;
val contract_4_imp = bimp (contract_4_pre, contract_4_wp);

val contract_4_imp_taut_thm = save_thm ("contract_4_imp_taut_thm",
  prove_exp_is_taut contract_4_imp);

(*****************************************************************************)
(* 1.2. Hoare triples containing memories                                    *)
(*                                                                           *)
(* !!! WARNING !!!                                                           *)
(*                                                                           *)
(* This is WIP, you can stop here for the tutorial.                          *)
(*                                                                           *)

(* (0) bir_add_reg_mem
 * 
 * Hoare triple: {} pre {}
 *)
(*
val contract_0_pre = (lhs o concl) bir_add_reg_contract_0_pre_def;
val contract_0_wp  = (lhs o concl) bir_add_reg_mem_wp_def;
val contract_0_imp = bimp (contract_0_pre, contract_0_wp);

val contract_0_imp_taut_thm = save_thm ("contract_0_imp_taut_thm",
  prove_exp_is_taut contract_0_imp);
*)

val _ = export_theory();

