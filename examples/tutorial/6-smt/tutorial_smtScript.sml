open HolKernel Parse boolLib bossLib;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

if !Globals.interactive then let
  (* To simplify the life of our poor vim users *)
  val _ = load "HolSmtLib";
  val _ = load "tutorial_bir_to_armTheory";
  val _ = load "tutorial_wpTheory";
in () end else ();

(* From examples: *)
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;

if !Globals.interactive then let
  val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
  val _ = Globals.show_tags := true;
  val _ = Globals.linewidth := 100;
  val _ = Feedback.set_trace "HolSmtLib" 1;
  val _ = bir_ppLib.install_bir_pretty_printers ();
  (*
  val _ = bir_ppLib.remove_bir_pretty_printers ();
  val _ = Feedback.set_trace "HolSmtLib" 0;
  val _ = Feedback.set_trace "HolSmtLib" 2;
  val _ = Feedback.set_trace "HolSmtLib" 3;
  val _ = Feedback.set_trace "HolSmtLib" 4;
  *)
in () end else ();

val _ = new_theory "tutorial_smt";

(* This function will prove `ante => conseq` using an SMT solver.
 * If this fails, it will print a SAT model.
 * 
 * This function uses an oracle to create theorems about the generated
 * words expression.
 *)
fun prove_imp_w_smt ante conseq =
  let
    val wrap_exn = Feedback.wrap_exn "tutorial_smt" "prove_imp_w_smt"
    (* Create the implication as a BIR expression *)
    val bir_impl = bor (bnot ante, conseq)
      handle e => raise pp_exn_s
        ( "Failed to create the implication. "
        ^ "Make sure that `ante` and `conseq` are BIR expression terms.")
        (wrap_exn e) 
    val w_tm = bir2bool bir_impl
    val proved_w_thm = HolSmtLib.Z3_ORACLE_PROVE w_tm
      handle HOL_ERR e =>
        let
          fun print_model model = List.foldl
            (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
            () (rev model);
          val neg_tm = mk_neg w_tm
          val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL neg_tm
          val _ = print "Failed to prove the implication. Here is a counter-example:\n";
          val _ = print_model model;
        in
          raise HOL_ERR e
        end
  in
    proved_w_thm
  end
    handle e => raise pp_exn e;

val EVALed_def_as_term = (rhs o concl o EVAL o rhs o concl)

(******************     (1) bir_add_reg_entry      ********************)
val contract_1_pre = EVALed_def_as_term bir_add_reg_contract_1_pre_def;
val contract_1_wp  = EVALed_def_as_term bir_add_reg_entry_wp_def;
val contract_1_imp = prove_imp_w_smt contract_1_pre contract_1_wp;

(******************    (2)  bir_add_reg_loop     *********************)
val contract_2_pre = EVALed_def_as_term bir_add_reg_contract_2_pre_def;
val contract_2_wp  = EVALed_def_as_term bir_add_reg_loop_wp_def;
val contract_2_imp = prove_imp_w_smt contract_2_pre contract_2_wp;

(**************   (3)  bir_add_reg_loop_continue     *****************)
val contract_3_pre = EVALed_def_as_term bir_add_reg_contract_3_pre_def;
val contract_3_wp  = EVALed_def_as_term bir_add_reg_loop_continue_wp_def;
val contract_3_imp = prove_imp_w_smt contract_3_pre contract_3_wp;

(***************       bir_add_reg_loop_exit      *****************)
val contract_4_pre = EVALed_def_as_term bir_add_reg_contract_4_pre_def;
val contract_4_wp  = EVALed_def_as_term bir_add_reg_loop_exit_wp_def;
val contract_4_imp = prove_imp_w_smt contract_4_pre contract_4_wp;

val _ = List.map save_thm [
  ("contract_1_imp", contract_1_imp),
  ("contract_2_imp", contract_2_imp),
  ("contract_3_imp", contract_3_imp),
  ("contract_4_imp", contract_4_imp)
];

val _ = export_theory();

