open HolKernel Parse boolLib bossLib
open bir_envTheory bir_basicTheory bir_binexpTheory bir_unaryexpTheory
open bir_binpredTheory bir_ifthenelseTheory
open bir_evalTheory bir_computeTheory bir_typingTheory



val _ = new_theory "bir_meta"





Theorem bir_eval_exp_correct_type:
    !env e v ty.
        bir_eval_exp env e v ==>
        type_of_bir_exp env e ty ==>
        type_of_bir_val v = ty
Proof
    Induct_on `e` >| [

        (* BExp_Const *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def],

        (* BExp_Den *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [bir_env_lookup_rel_inj],

        (* BExp_BinExp *)
        simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [bir_eval_binexp_def, bir_eval_binexp_keep_type, type_of_bir_val_def],

        (* BExp_UnaryExp *)
        simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [bir_eval_unaryexp_def, bir_eval_unaryexp_keep_type, type_of_bir_val_def],

        (* BExp_BinPred *)
        simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [bir_eval_binpred_cases, bir_eval_binpred_correct_type, type_of_bir_val_def],

        (* BExp_IfThenElse *)
        simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [bir_eval_ifthenelse_cases, bir_eval_ifthenelse_keep_type, type_of_bir_val_def]
    ]
QED



Theorem well_typed_bir_eval_exp_value:
    !env e ty.
        type_of_bir_exp env e ty ==>
        ?v. bir_eval_exp env e v
Proof
    Induct_on `e` >| [

        (* BExp_Const *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def],

        (* BExp_Den *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        METIS_TAC [],

        (* BExp_BinExp *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        `?v1. bir_eval_exp env e v1` by METIS_TAC [] >>
        `?v2. bir_eval_exp env e' v2` by METIS_TAC [] >>
        qrefinel [`_`, `v1`, `v2`] >>
        METIS_TAC [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_binexp],

        (* BExp_UnaryExp *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        `?v1. bir_eval_exp env e v1` by METIS_TAC [] >>
        qrefinel [`_`, `v1`] >>
        METIS_TAC [bir_eval_exp_correct_type, always_bir_eval_unaryexp],

        (* BExp_BinPred *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        `?v1. bir_eval_exp env e v1` by METIS_TAC [] >>
        `?v2. bir_eval_exp env e' v2` by METIS_TAC [] >>
        qrefinel [`_`, `v1`, `v2`] >>
        METIS_TAC [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_binpred],

        (* BExp_IfThenElse *)
        rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
        `?v. bir_eval_exp env e v` by METIS_TAC [] >>
        `?v1. bir_eval_exp env e' v1` by METIS_TAC [] >>
        `?v2. bir_eval_exp env e'' v2` by METIS_TAC [] >>
        qrefinel [`_`, `v`, `v1`, `v2`] >>
        METIS_TAC [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_ifthenelse]
    ]
QED



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
