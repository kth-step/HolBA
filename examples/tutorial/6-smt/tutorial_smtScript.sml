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

(******************     (1) bir_add_reg_entry      ********************)
(* {T} entry {I}, i.e. T ==> WP(I, entry) *)
val contract_1_pre = btrue;
val contract_1_wp  = (lhs o concl) bir_add_reg_entry_wp_def;

val contract_1_imp_tm = bimp (contract_1_pre, contract_1_wp);

val contract_1_imp_taut_thm = prove_exp_is_taut contract_1_imp_tm
  handle e => (print "This didn't work.\n"; TRUTH);

(******************     (1) now fixed      ********************)
(* T isn't strong enough: {x >= 0} entry {I} *)
val contract_1_pre = (lhs o concl) bir_add_reg_contract_1_pre_def;

val contract_1_imp_taut_thm = save_exp_is_taut_imp ("contract_1_imp_taut_thm",
  contract_1_pre, contract_1_wp);

(******************    (2)  bir_add_reg_loop     *********************)
val contract_2_pre = (lhs o concl) bir_add_reg_contract_2_pre_def;
val contract_2_wp  = (lhs o concl) bir_add_reg_loop_wp_def;

val contract_2_imp_taut_thm = save_exp_is_taut_imp ("contract_2_imp_taut_thm",
  contract_2_pre, contract_2_wp);

(**************   (3)  bir_add_reg_loop_continue     *****************)
val contract_3_pre = (lhs o concl) bir_add_reg_contract_3_pre_def;
val contract_3_wp  = (lhs o concl) bir_add_reg_loop_continue_wp_def;

val contract_3_imp_taut_thm = save_exp_is_taut_imp ("contract_3_imp_taut_thm",
  contract_3_pre, contract_3_wp);

(***************   (4)    bir_add_reg_loop_exit      *****************)
val contract_4_pre = (lhs o concl) bir_add_reg_contract_4_pre_def;
val contract_4_wp  = (lhs o concl) bir_add_reg_loop_exit_wp_def;

val contract_4_imp_taut_thm = save_exp_is_taut_imp ("contract_4_imp_taut_thm",
  contract_4_pre, contract_4_wp);



(***************   (2v)    bir_add_reg_loop_variant      *****************)
val contract_2v_freevar = ``abcdefg:word64``;
val contract_2v_pre = (lhs o concl o (SPEC contract_2v_freevar)) bir_add_reg_contract_2_pre_variant_def;
val contract_2v_wp  = (lhs o concl o (SPEC contract_2v_freevar)) bir_add_reg_loop_variant_wp_def;

val contract_2v_imp_taut_thm = save_exp_is_taut_imp ("contract_2v_imp_taut_thm",
  contract_2v_pre, contract_2v_wp);

(***************   (3v)    bir_add_reg_loop_continue_variant      *****************)
val contract_3v_freevar = ``abcdefg:word64``;
val contract_3v_pre = (lhs o concl o (SPEC contract_3v_freevar)) bir_add_reg_contract_3_pre_variant_def;
val contract_3v_wp  = (lhs o concl o (SPEC contract_3v_freevar)) bir_add_reg_loop_continue_variant_wp_def;

val contract_3v_imp_taut_thm = save_exp_is_taut_imp ("contract_3v_imp_taut_thm",
  contract_3v_pre, contract_3v_wp);


val _ = export_theory();

