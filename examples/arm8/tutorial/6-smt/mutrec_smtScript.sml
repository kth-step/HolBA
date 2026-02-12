open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_smtLib bslSyntax;
open pretty_exnLib;

(* From examples: *)
open mutrec_wpTheory;


val _ = new_theory "mutrec_smt";



val h_var_v1 = mk_var ("v1", Type `:word64`);
val h_var_v  = mk_var ("v",  Type `:word64`);

val h_vars = [h_var_v1, h_var_v];

fun get_contract_vars n = (lhs o concl o (SPECL (List.take(h_vars,n))));


(* =============================================================== *)

val contract_ev_1_pre = get_contract_vars 2 bir_ieo_sec_iseven_loop_pre_def;
val contract_ev_1_wp  = get_contract_vars 2 bir_ieo_sec_iseven_loop_wp_def;
val contract_ev_1_imp = bimp (contract_ev_1_pre, contract_ev_1_wp);

val contract_ev_1_imp_taut_thm = save_thm ("contract_ev_1_imp_taut_thm",
  bir_smt_prove_is_taut contract_ev_1_imp);


val contract_ev_2_pre = get_contract_vars 1 bir_ieo_sec_iseven_exit_pre_def;
val contract_ev_2_wp  = get_contract_vars 1 bir_ieo_sec_iseven_exit_wp_def;
val contract_ev_2_imp = bimp (contract_ev_2_pre, contract_ev_2_wp);

val contract_ev_2_imp_taut_thm = save_thm ("contract_ev_2_imp_taut_thm",
  bir_smt_prove_is_taut contract_ev_2_imp);


val contract_ev_3_pre = ``bir_ieo_sec_iseven_exit_post v1 (BL_Address (Imm32 0w))``;
val contract_ev_3_wp  = get_contract_vars 1 bir_ieo_invariant_def;
val contract_ev_3_imp = bimp (contract_ev_3_pre, contract_ev_3_wp);

val contract_ev_3_imp_taut_thm = save_thm ("contract_ev_3_imp_taut_thm",
  bir_smt_prove_is_taut contract_ev_3_imp);


val contract_ev_4_pre = ``bir_ieo_pre v1``;
val contract_ev_4_wp  = ``bir_ieo_invariant v1``;
val contract_ev_4_imp = bimp (contract_ev_4_pre, contract_ev_4_wp);

val contract_ev_4_imp_taut_thm = save_thm ("contract_ev_4_imp_taut_thm",
  bir_smt_prove_is_taut contract_ev_4_imp);

(* =============================================================== *)

val contract_od_1_pre = get_contract_vars 2 bir_ieo_sec_isodd_loop_pre_def;
val contract_od_1_wp  = get_contract_vars 2 bir_ieo_sec_isodd_loop_wp_def;
val contract_od_1_imp = bimp (contract_od_1_pre, contract_od_1_wp);

val contract_od_1_imp_taut_thm = save_thm ("contract_od_1_imp_taut_thm",
  bir_smt_prove_is_taut contract_od_1_imp);


val contract_od_2_pre = get_contract_vars 1 bir_ieo_sec_isodd_exit_pre_def;
val contract_od_2_wp  = get_contract_vars 1 bir_ieo_sec_isodd_exit_wp_def;
val contract_od_2_imp = bimp (contract_od_2_pre, contract_od_2_wp);

val contract_od_2_imp_taut_thm = save_thm ("contract_od_2_imp_taut_thm",
  bir_smt_prove_is_taut contract_od_2_imp);


val contract_od_3_pre = ``bir_ieo_sec_isodd_exit_post v1 (BL_Address (Imm32 0w))``;
val contract_od_3_wp  = get_contract_vars 1 bir_ieo_invariant_def;
val contract_od_3_imp = bimp (contract_od_3_pre, contract_od_3_wp);

val contract_od_3_imp_taut_thm = save_thm ("contract_od_3_imp_taut_thm",
  bir_smt_prove_is_taut contract_od_3_imp);


val contract_od_4_pre = ``bir_ieo_pre v1``;
val contract_od_4_wp  = ``bir_ieo_invariant v1``;
val contract_od_4_imp = bimp (contract_od_4_pre, contract_od_4_wp);

val contract_od_4_imp_taut_thm = save_thm ("contract_od_4_imp_taut_thm",
  bir_smt_prove_is_taut contract_od_4_imp);


val _ = export_theory();

