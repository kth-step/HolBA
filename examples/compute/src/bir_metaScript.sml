open HolKernel Parse boolLib bossLib ;
open bir_envTheory bir_basicTheory bir_binexpTheory bir_unaryexpTheory ;
open bir_binpredTheory bir_ifthenelseTheory ;
open bir_evalTheory bir_computeTheory bir_typingTheory ;



val _ = new_theory "bir_meta" ;




(* A typed expression evaluates to a value of the same type *)
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


(* A typed expression always evaluates to some value *)
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



(* Eval and compute are similar *)
Theorem bir_eval_exp_eq_compute_exp:
  !env e v ty. type_of_bir_exp env e ty ==> 
    (bir_eval_exp env e v <=> (bir_compute_exp e env = SOME v))
Proof
  Cases_on `env` >>
  Induct_on `e` >| [

    (* BExp_Const *)
    rw [Once bir_eval_exp_cases, bir_compute_exp_def] >>
    METIS_TAC [],

    (* BExp_Den *)
    rw [Once bir_eval_exp_cases] >>
    Cases_on `b` >>
    rw [bir_compute_exp_def, bir_env_lookup_rel_def, bir_env_lookup_def],

    (* BExp_BinExp *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >> 
      rw [Once type_of_bir_exp_cases, bir_compute_binexp_def, bir_eval_binexp_eq_compute_binexp] >>
      METIS_TAC [],

    (* BExp_UnaryExp *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
      rw [Once type_of_bir_exp_cases, bir_compute_unaryexp_def, bir_eval_unaryexp_eq_compute_unaryexp] >>
      METIS_TAC [],

    (* BExp_BinPred *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >>
      rw [Once type_of_bir_exp_cases, bir_compute_binpred_def, well_typed_bir_eval_binpred_eq_compute_binpred] >>
      METIS_TAC [well_typed_bir_eval_binpred_eq_compute_binpred, bir_eval_exp_correct_type],



    (* BExp_IfThenElse *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >>
    Cases_on `bir_compute_exp e'' (BEnv f)` >>
      rw [Once type_of_bir_exp_cases, bir_compute_ifthenelse_def] >>
      METIS_TAC [well_typed_bir_eval_exp_value, bir_eval_ifthenelse_eq_compute_ifthenelse,
        bir_eval_exp_correct_type, bir_eval_ifthenelse_cases]
  ]
QED




val _ = export_theory () ;
