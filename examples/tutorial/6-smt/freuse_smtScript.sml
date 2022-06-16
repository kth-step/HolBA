open HolKernel Parse boolLib bossLib;

open bir_expSyntax;
open bir_exp_tautologiesTheory;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;
open pretty_exnLib;

(* From examples: *)
open freuse_wpTheory;
open tutorial_smtSupportLib;


val _ = new_theory "freuse_smt";



val h_var_v1 = mk_var ("v1", Type `:word32`)
val h_var_v2 = mk_var ("v2", Type `:word32`)
val h_var_v3 = mk_var ("v3", Type `:word32`)
val h_varlist = [h_var_v1, h_var_v2, h_var_v3];

fun get_contract_vars n = (lhs o concl o (SPECL (List.take (h_varlist, n))));

val contract_1_pre = get_contract_vars 3 bir_att_sec_add_1_pre_def;
val contract_1_wp  = get_contract_vars 3 bir_att_sec_add_1_wp_def;
val contract_1_imp = bimp (contract_1_pre, contract_1_wp);

val contract_1_imp_taut_thm = save_thm ("contract_1_imp_taut_thm",
  prove_exp_is_taut contract_1_imp);

val contract_2_pre = get_contract_vars 2 bir_att_sec_call_1_pre_def;
val contract_2_wp  = get_contract_vars 2 bir_att_sec_call_1_wp_def;
val contract_2_imp = bimp (contract_2_pre, contract_2_wp);

val contract_2_imp_taut_thm = save_thm ("contract_2_imp_taut_thm",
  prove_exp_is_taut contract_2_imp);

val contract_3_pre = get_contract_vars 1 bir_att_sec_call_2_pre_def;
val contract_3_wp  = get_contract_vars 1 bir_att_sec_call_2_wp_def;
val contract_3_imp = bimp (contract_3_pre, contract_3_wp);

val contract_3_imp_taut_thm = save_thm ("contract_3_imp_taut_thm",
  prove_exp_is_taut contract_3_imp);

(* meeting the subcontracts *)
val bir_att_sec_call_1_taut_thm = save_thm("bir_att_sec_call_1_taut_thm",
((*(Q.SPECL [`v2`, `v1`]) o *) prove_exp_is_taut)
       (bimp (``bir_att_sec_add_2_post v1 v2``, ``bir_att_sec_call_2_pre (v1+v2)``))
);

val bir_att_post_taut_thm = save_thm("bir_att_post_taut_thm",
prove_exp_is_taut
       (bimp (``bir_att_sec_add_2_post (v1 + v2) (v1 + v2)``, ``bir_att_sec_2_post v1 v2``))
);


val _ = export_theory();

