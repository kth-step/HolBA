open HolKernel Parse boolLib bossLib
open bir_envTheory bir_basicTheory bir_binexpTheory bir_unaryexpTheory
open bir_evalTheory bir_computeTheory



val _ = new_theory "bir_meta"


Theorem bir_eval_exp_eq_compute_exp:
    !env e v. bir_eval_exp env e v <=> (bir_compute_exp e env = SOME v)
Proof
    Cases_on `env` >>
    Induct_on `e` >| [

        rw [Once bir_eval_exp_cases, bir_compute_exp_def] >>
        METIS_TAC [],

        rw [Once bir_eval_exp_cases, bir_env_lookup_rel_cases] >>
        Cases_on `b` >>
        rw [bir_var_t_11, bir_var_environment_t_11] >>
        rw [bir_compute_exp_def, bir_env_lookup_def],

        rw [Once bir_eval_exp_cases, bir_compute_exp_def] >>
        Cases_on `bir_compute_exp e (BEnv f)` >>
        Cases_on `bir_compute_exp e' (BEnv f)` >> 
            rw [bir_compute_binexp_def, bir_eval_binexp_eq_compute_binexp],

        rw [Once bir_eval_exp_cases, bir_compute_exp_def] >>
        Cases_on `bir_compute_exp e (BEnv f)` >>
            rw [bir_compute_unaryexp_def, bir_eval_unaryexp_eq_compute_unaryexp]
    ]
QED




val _ = export_theory ()
