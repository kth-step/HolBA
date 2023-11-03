open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* From examples: *)
open mutrec_wpTheory;
open tutorial_smtSupportLib;


val _ = new_theory "mutrec_smt";

(* The HOL4 variables *)
val h_vars = [mk_var ("v1", Type `:word64`),
              mk_var ("v",  Type `:word64`)];
(* Takes a definition, then specialises the LHS with a variable chosen
 * from h_vars using n *)
fun get_contract_vars n = (lhs o concl o (SPECL (List.take(h_vars,n))));


(* =============================================================== *)
(* is_even implications *)

(* Construct the term holding the implication *)
val contract_ev_1_pre = get_contract_vars 2 bir_ieo_sec_iseven_loop_pre_def;
val contract_ev_1_wp  = get_contract_vars 2 bir_ieo_sec_iseven_loop_wp_def;
val contract_ev_1_imp = bimp (contract_ev_1_pre, contract_ev_1_wp);

(* Prove the implication and save it properly as a theorem *)
val contract_ev_1_imp_taut_thm = save_thm ("contract_ev_1_imp_taut_thm",
  prove_exp_is_taut contract_ev_1_imp);


val contract_ev_2_pre = get_contract_vars 1 bir_ieo_sec_iseven_exit_pre_def;
val contract_ev_2_wp  = get_contract_vars 1 bir_ieo_sec_iseven_exit_wp_def;
val contract_ev_2_imp = bimp (contract_ev_2_pre, contract_ev_2_wp);

val contract_ev_2_imp_taut_thm = save_thm ("contract_ev_2_imp_taut_thm",
  prove_exp_is_taut contract_ev_2_imp);


val contract_ev_3_pre = ``bir_ieo_sec_iseven_exit_post v1 (BL_Address (Imm32 0w))``;
val contract_ev_3_wp  = get_contract_vars 1 bir_ieo_invariant_def;
val contract_ev_3_imp = bimp (contract_ev_3_pre, contract_ev_3_wp);

val contract_ev_3_imp_taut_thm = save_thm ("contract_ev_3_imp_taut_thm",
  prove_exp_is_taut contract_ev_3_imp);

(* To be used by PreStr rule *)
val contract_ev_4_pre = ``bir_ieo_pre v1``;
val contract_ev_4_wp  = ``bir_ieo_invariant v1``;
val contract_ev_4_imp = bimp (contract_ev_4_pre, contract_ev_4_wp);

val contract_ev_4_imp_taut_thm = save_thm ("contract_ev_4_imp_taut_thm",
  prove_exp_is_taut contract_ev_4_imp);

(* =============================================================== *)

val contract_od_1_pre = get_contract_vars 2 bir_ieo_sec_isodd_loop_pre_def;
val contract_od_1_wp  = get_contract_vars 2 bir_ieo_sec_isodd_loop_wp_def;
val contract_od_1_imp = bimp (contract_od_1_pre, contract_od_1_wp);

val contract_od_1_imp_taut_thm = save_thm ("contract_od_1_imp_taut_thm",
  prove_exp_is_taut contract_od_1_imp);


val contract_od_2_pre = get_contract_vars 1 bir_ieo_sec_isodd_exit_pre_def;
val contract_od_2_wp  = get_contract_vars 1 bir_ieo_sec_isodd_exit_wp_def;
val contract_od_2_imp = bimp (contract_od_2_pre, contract_od_2_wp);

val contract_od_2_imp_taut_thm = save_thm ("contract_od_2_imp_taut_thm",
  prove_exp_is_taut contract_od_2_imp);


val contract_od_3_pre = ``bir_ieo_sec_isodd_exit_post v1 (BL_Address (Imm32 0w))``;
val contract_od_3_wp  = get_contract_vars 1 bir_ieo_invariant_def;
val contract_od_3_imp = bimp (contract_od_3_pre, contract_od_3_wp);

val contract_od_3_imp_taut_thm = save_thm ("contract_od_3_imp_taut_thm",
  prove_exp_is_taut contract_od_3_imp);


val contract_od_4_pre = ``bir_ieo_pre v1``;
val contract_od_4_wp  = ``bir_ieo_invariant v1``;
val contract_od_4_imp = bimp (contract_od_4_pre, contract_od_4_wp);

val contract_od_4_imp_taut_thm = save_thm ("contract_od_4_imp_taut_thm",
  prove_exp_is_taut contract_od_4_imp);


val _ = export_theory();

