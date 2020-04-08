open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* From examples: *)
open tutorialExtra2_wpTheory;
open tutorial_smtSupportLib;


val _ = new_theory "tutorialExtra2_smt";



val h_var_v1 = mk_var ("v1", Type `:word64`);
val h_var_v  = mk_var ("v",  Type `:word64`);

val h_vars = [h_var_v1, h_var_v];

fun get_contract_vars n = (lhs o concl o (SPECL (List.take(h_vars,n))));


val contract_1_pre = get_contract_vars 2 bir_ieo_sec_iseven_loop_pre_def;
val contract_1_wp  = get_contract_vars 2 bir_ieo_sec_iseven_loop_wp_def;
val contract_1_imp = bimp (contract_1_pre, contract_1_wp);

val contract_1_imp_taut_thm = save_thm ("contract_1_imp_taut_thm",
  prove_exp_is_taut contract_1_imp);


val contract_2_pre = get_contract_vars 1 bir_ieo_sec_iseven_exit_pre_def;
val contract_2_wp  = get_contract_vars 1 bir_ieo_sec_iseven_exit_wp_def;
val contract_2_imp = bimp (contract_2_pre, contract_2_wp);

val contract_2_imp_taut_thm = save_thm ("contract_2_imp_taut_thm",
  prove_exp_is_taut contract_2_imp);


val contract_3_pre = ``bir_ieo_sec_iseven_exit_post v1 (BL_Address (Imm32 0w))``;
val contract_3_wp  = get_contract_vars 1 bir_ieo_invariant_def;
val contract_3_imp = bimp (contract_3_pre, contract_3_wp);

val contract_3_imp_taut_thm = save_thm ("contract_3_imp_taut_thm",
  prove_exp_is_taut contract_3_imp);


val contract_4_pre = ``bir_ieo_ev_pre v1``;
val contract_4_wp  = ``bir_ieo_invariant v1``;
val contract_4_imp = bimp (contract_4_pre, contract_4_wp);

val contract_4_imp_taut_thm = save_thm ("contract_4_imp_taut_thm",
  prove_exp_is_taut contract_4_imp);


val _ = export_theory();

