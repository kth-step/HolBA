(* --------------------------------------------------------------------------- *)
(*  Theorems regarding the meta language properties like typing and evaluation *)
(* --------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open birTheory bir_computeTheory;
open bir_programTheory bir_typing_programTheory;
open ottTheory;


val _ = new_theory "bir_meta";


(* ----------------------------------------------- *)
(* --------------------- EXP --------------------- *)
(* ----------------------------------------------- *)


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

    (* BExp_MemConst *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def],

    (* BExp_Den *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_env_lookup_rel_inj],

    (* BExp_BinExp *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_binexp_def, bir_eval_binexp_keep_type, type_of_bir_val_def],

    (* BExp_UnaryExp *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_unaryexp_def, bir_eval_unaryexp_keep_type, type_of_bir_val_def],

    (* BExp_BinPred *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_binpred_cases, bir_eval_binpred_correct_type, type_of_bir_val_def],

    (* BExp_IfThenElse *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_ifthenelse_cases, bir_eval_ifthenelse_keep_type, type_of_bir_val_def],

    (* BExp_Load *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_load_def, bir_eval_load_correct_type, type_of_bir_val_def],

    (* BExp_Store *)
    simp [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def] >>
    metis_tac [bir_eval_store_def, bir_eval_store_correct_type, type_of_bir_val_def]
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
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def],

    (* BExp_MemConst *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def],

    (* BExp_Den *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    metis_tac [],

    (* BExp_BinExp *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v1. bir_eval_exp env e v1` by metis_tac [] >>
    `?v2. bir_eval_exp env e' v2` by metis_tac [] >>
    qrefinel [`_`, `v1`, `v2`] >>
    metis_tac [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_binexp],

    (* BExp_UnaryExp *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v1. bir_eval_exp env e v1` by metis_tac [] >>
    qrefinel [`_`, `v1`] >>
    metis_tac [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_unaryexp],

    (* BExp_BinPred *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v1. bir_eval_exp env e v1` by metis_tac [] >>
    `?v2. bir_eval_exp env e' v2` by metis_tac [] >>
    qrefinel [`_`, `v1`, `v2`] >>
    metis_tac [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_binpred],

    (* BExp_IfThenElse *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v. bir_eval_exp env e v` by metis_tac [] >>
    `?v1. bir_eval_exp env e' v1` by metis_tac [] >>
    `?v2. bir_eval_exp env e'' v2` by metis_tac [] >>
    qrefinel [`_`, `v`, `v1`, `v2`] >>
    metis_tac [bir_eval_exp_correct_type, type_of_bir_val_imp_bir_eval_ifthenelse],

    (* BExp_Load *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v_mem. bir_eval_exp env e v_mem` by metis_tac [] >>
    `?v_addr. bir_eval_exp env e' v_addr` by metis_tac [] >>
    qrefinel [`_`, `v_mem`, `v_addr`] >>
    metis_tac [bir_eval_exp_correct_type, 
      type_of_bir_val_imp_bir_eval_load_bigendian,
      type_of_bir_val_imp_bir_eval_load_littleendian,
      type_of_bir_val_imp_bir_eval_load_noendian],

    (* BExp_Store *)
    rw [Once type_of_bir_exp_cases, Once bir_eval_exp_cases, type_of_bir_val_def,clause_name_def] >>
    `?v_mem. bir_eval_exp env e v_mem` by metis_tac [] >>
    `?v_addr. bir_eval_exp env e' v_addr` by metis_tac [] >>
    qrefinel [`_`, `v_mem`, `v_addr`] >>
    metis_tac [bir_eval_exp_correct_type, 
      type_of_bir_val_imp_bir_eval_store_bigendian,
      type_of_bir_val_imp_bir_eval_store_littleendian,
      type_of_bir_val_imp_bir_eval_store_noendian]
  ]
QED



(* Eval and compute are similar *)
Theorem bir_eval_exp_eq_compute_exp:
  !env e v ty. type_of_bir_exp env e ty ==> 
    (bir_eval_exp env e v <=> (bir_compute_exp e env = SOME v))
Proof
  Cases_on `env` >> Induct_on `e` >| [

    (* BExp_Const *)
    rw [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    metis_tac [],

    (* BExp_MemConst *)
    rw [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    metis_tac [],

    (* BExp_Den *)
    rw [Once bir_eval_exp_cases,clause_name_def] >>
    Cases_on `b` >>
    rw [bir_compute_exp_def, bir_env_lookup_rel_def, bir_env_lookup_def],

    (* BExp_BinExp *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >| [
      rw [Once type_of_bir_exp_cases, bir_compute_binexp_def, bir_eval_binexp_eq_compute_binexp],
      rw [Once type_of_bir_exp_cases, bir_compute_binexp_def, bir_eval_binexp_eq_compute_binexp],
      Cases_on `x` >>
      rw [Once type_of_bir_exp_cases, bir_compute_binexp_def, bir_eval_binexp_eq_compute_binexp],
      rw [Once type_of_bir_exp_cases, bir_eval_binexp_eq_compute_binexp]
    ] >>
    metis_tac [],

    (* BExp_UnaryExp *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    rw [Once type_of_bir_exp_cases, bir_compute_unaryexp_def, bir_eval_unaryexp_eq_compute_unaryexp] >>
    metis_tac [],

    (* BExp_BinPred *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >| [
      all_tac,
      all_tac,
      Cases_on `x`,
      all_tac
    ] >>
    rw [Once type_of_bir_exp_cases, bir_compute_binpred_def, well_typed_bir_eval_binpred_eq_compute_binpred] >>
    metis_tac [well_typed_bir_eval_binpred_eq_compute_binpred, bir_eval_exp_correct_type],



    (* BExp_IfThenElse *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >>
    Cases_on `bir_compute_exp e'' (BEnv f)` >>
    rw [Once type_of_bir_exp_cases, bir_compute_ifthenelse_def] >>
    metis_tac [well_typed_bir_eval_exp_value, bir_eval_ifthenelse_eq_compute_ifthenelse,
     bir_eval_exp_correct_type, bir_eval_ifthenelse_cases],

    (* BExp_Load *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >| [
      all_tac,
      all_tac,
      Cases_on `x`,
      all_tac
    ] >>
    rw [Once type_of_bir_exp_cases, bir_compute_load_def, bir_eval_load_eq_compute_load] >>
    metis_tac [bir_eval_load_eq_compute_load, bir_eval_exp_correct_type],

    (* BExp_Store *)
    simp [Once bir_eval_exp_cases, bir_compute_exp_def,clause_name_def] >>
    Cases_on `bir_compute_exp e (BEnv f)` >>
    Cases_on `bir_compute_exp e' (BEnv f)` >>
    Cases_on `bir_compute_exp e'' (BEnv f)` >| [
      all_tac,
      all_tac,
      all_tac,
      all_tac,
      Cases_on `x`,
      Cases_on `x`,
      Cases_on `x` >> Cases_on `x'`,
      all_tac
    ] >>
    rw [Once type_of_bir_exp_cases, bir_compute_store_def, bir_eval_store_eq_compute_store] >>
    metis_tac [bir_eval_store_eq_compute_store, bir_eval_exp_correct_type]
  ]
QED

(* ----------------------------------------------- *)
(* ------------------ PROGRAMS ------------------- *)
(* ----------------------------------------------- *)

Theorem bir_eval_label_exp_eq_compute_label_exp:
  !le env l prog.
    is_label_exp_typed_in_env env prog le ==>
    (bir_eval_label_exp le env l <=> (bir_compute_label_exp le env = SOME l))
Proof
  Cases_on `le` >> Cases_on `l` >>
  rw [bir_eval_label_exp_def, bir_compute_label_exp_def] >| [
    Cases_on `bir_compute_exp b env` >> TRY (Cases_on `x`) >> rw [],

    `?ity. type_of_bir_exp env b (BType_Imm ity)` by metis_tac [is_label_exp_typed_in_env_def] >>
    `bir_eval_exp env b (BVal_Imm b') = (bir_compute_exp b env = SOME (BVal_Imm b'))`
      by metis_tac [bir_eval_exp_eq_compute_exp] >>
    Cases_on `bir_compute_exp b env` >> 
      TRY (Cases_on `x`) >>
      rw []
  ]
QED

Theorem well_typed_bir_eval_label_exp_value:
  !le env prog.
    is_label_exp_typed_in_env env prog le ==>
    ?l. bir_eval_label_exp le env l
Proof
  `!f. (?l. f l) <=> ((?l. f (BL_Label l)) \/ (?a. f (BL_Address a)))` by
    (rw [] >>
    eq_tac >| [
      rw [] >> Cases_on `l` >> metis_tac [],
      rw [] >> metis_tac []
    ])>>
  Cases_on `le` >> 
  rw [bir_eval_label_exp_def] >| [
    Cases_on `b` >> rw [],

    fs [is_label_exp_typed_in_env_def, is_exp_well_typed_def] >>
    `?v. bir_eval_exp env b v` by metis_tac [well_typed_bir_eval_exp_value] >>
    Cases_on `v` >| [
      metis_tac [],
      `type_of_bir_val (BVal_Mem b' b0 f) = BType_Imm ity` by 
        metis_tac [bir_eval_exp_correct_type] >>
      fs [type_of_bir_val_def]
    ]
  ]
QED

Theorem bir_eval_stmt_jmp_eq_compute_stmt_jmp:
  !p le st st'.
    is_label_exp_typed_in_env (st.bst_environ) p le ==>
    (bir_eval_stmt_jmp p le st st' <=> (bir_compute_stmt_jmp p le st = st'))
Proof
  rw [bir_eval_stmt_jmp_def, bir_compute_stmt_jmp_def] >>
  `!l. bir_eval_label_exp le st.bst_environ l = (bir_compute_label_exp le st.bst_environ = SOME l)`
    by metis_tac [bir_eval_label_exp_eq_compute_label_exp] >>
  `?l. bir_eval_label_exp le (st.bst_environ) l` 
    by metis_tac [well_typed_bir_eval_label_exp_value] >>
  CASE_TAC >>
  fs []
QED

Theorem bir_eval_stmtE_eq_compute_stmtE:
  !p bst st st'.
    is_stmt_end_typed_in_env (st.bst_environ) p bst ==>
    (bir_eval_stmtE p bst st st' <=> (bir_compute_stmtE p bst st = st'))
Proof
  Cases_on `bst` >>
  simp [bir_eval_stmtE_def, bir_compute_stmtE_def] >>
  rw [bir_eval_label_exp_eq_compute_label_exp, is_stmt_end_typed_in_env_def] >| [
    rw [bir_eval_stmt_jmp_eq_compute_stmt_jmp],

    rw [bir_eval_stmt_cjmp_def, bir_compute_stmt_cjmp_def] >>
    rw [bir_eval_stmt_jmp_eq_compute_stmt_jmp] >| [
      `bir_compute_exp b st.bst_environ = SOME birT` by metis_tac [bir_eval_exp_eq_compute_exp] >>
      rw [bir_dest_bool_val_def, birT_def],
    
      `?v. bir_eval_exp st.bst_environ b v` by metis_tac [well_typed_bir_eval_exp_value] >>
      `type_of_bir_val v = BType_Imm Bit1` by metis_tac [bir_eval_exp_correct_type] >>
      `v = birF` by metis_tac [bit1_is_boolean] >>
      `bir_compute_exp b st.bst_environ = SOME birF` by metis_tac [bir_eval_exp_eq_compute_exp] >>
      rw [bir_dest_bool_val_def, birF_def]
    ]
  ]
QED

Theorem bir_eval_stmtB_eq_compute_stmtB:
  !p bst st st'.
    is_stmt_basic_typed_in_env st.bst_environ bst ==>
    (bir_eval_stmtB bst st st' <=> (bir_compute_stmtB bst st = st'))
Proof
  Cases_on `bst` >>
  rw [bir_eval_stmtB_def, bir_compute_stmtB_def, bir_compute_stmt_assign_def] >>
  fs [is_stmt_basic_typed_in_env_def, is_exp_well_typed_def] >>
  `!va. bir_eval_exp st.bst_environ b0 va = (bir_compute_exp b0 st.bst_environ = SOME va)`
    by metis_tac [bir_eval_exp_eq_compute_exp] >>
  eq_tac >| [
    CASE_TAC >> rw [],
    `?va. bir_eval_exp st.bst_environ b0 va` by metis_tac [well_typed_bir_eval_exp_value] >>
    CASE_TAC >> fs []
  ]
QED


Theorem bir_eval_step_eq_compute_step:
  !p st st'.
    (~bir_state_is_terminated st) ==>
    (is_prog_typed_in_env st.bst_environ p) ==>
    (bir_eval_step p st st' <=> (bir_compute_step p st = st'))
Proof
  rw [bir_eval_step_cases, bir_compute_step_def] >>
  Cases_on `bir_get_current_statement p st.bst_pc` >| [
    simp [] >>
    metis_tac [],

    `is_stmt_typed_in_env st.bst_environ p x`
      by metis_tac [is_prog_typed_get_current_statement] >>
    Cases_on `x` >>
    rw [bir_compute_stmt_def] >>
    fs [is_stmt_typed_in_env_def] >>
    metis_tac [bir_eval_stmtB_eq_compute_stmtB, bir_eval_stmtE_eq_compute_stmtE] 
  ]
QED



val _ = export_theory ();
