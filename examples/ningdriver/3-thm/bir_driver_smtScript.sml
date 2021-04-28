open HolKernel Parse boolLib bossLib HolSmtLib;
open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* From examples: *)
open bir_driver_condTheory;
open bir_driver_wpTheory;
open tutorial_smtSupportLib;

val _ = new_theory "bir_driver_smt";

(* Prove P ==> WP(progB, Q) for part B of the driver's program
 * It means {P}progB{Q} holds.
 *)
val (v,pre_exp) = (dest_forall o concl) bir_driver_segB_precond_def;
val contract_B_pre = lhs pre_exp;
val (v1, wp_exp) = (dest_forall o concl) bir_ningdriver_prog_B_wp_def;
val contract_B_wp = lhs wp_exp;
val contract_B_imp = bimp (contract_B_pre, contract_B_wp);
val contract_B_imp_taut_thm = save_thm ("contract_B_imp_taut_thm",
  prove_exp_is_taut contract_B_imp);


val _ = export_theory ();
