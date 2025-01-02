(* --------------------------------------------------------------------------- *)
(*  Theorems regarding the meta language properties like typing and evaluation *)
(* --------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open wordsTheory;
open birTheory bir_computeTheory;
open bir_programTheory bir_typing_programTheory;
open ottTheory;

val _ = new_theory "bir_meta";

(* Correction Theorems of boolean functions *)
Theorem bool2b_T_eq_birT:
  BVal_Imm (bool2b T) = birT
Proof
  rw [bool2b_def, bool2w_def, birT_def]
QED

Theorem bool2b_F_eq_birF:
  BVal_Imm (bool2b F) = birF
Proof
  rw [bool2b_def, bool2w_def, birF_def]
QED

(* 1 bit values are booleans *)
Theorem bit1_is_boolean:
  !v. type_of_bir_val v = (BType_Imm Bit1) ==> (v = birT \/ v = birF)
Proof
  Cases_on `v` >>
    Cases_on `b` >>
      rw [birT_def, birF_def, type_of_bir_val_def, type_of_bir_imm_def] >>
      Cases_on `c` >>
        fs [dimword_1]
QED

Theorem size_of_bir_immtype_leq_1:
  !b. 1 <= 2 ** (size_of_bir_immtype b)
Proof
  Cases_on `b` >>
  rw [size_of_bir_immtype_def]
QED

Theorem bir_env_lookup_empty:
  !var v. ~(bir_env_lookup_rel bir_empty_env var v)
Proof
  Cases_on `var` >>
  rw [bir_empty_env_def, bir_env_lookup_rel_def]
QED

Theorem bir_env_lookup_rel_update:
  !env var v. bir_env_lookup_rel (bir_env_update env var v) var v 
Proof
  Cases_on `var` >> Cases_on `env` >>
  rw [bir_env_update_def, bir_env_lookup_rel_def]
QED

Theorem bir_env_lookup_update:
  !env var v. bir_env_lookup (bir_env_update env var v) var = SOME v 
Proof
  rpt gen_tac >>
  Cases_on `var` >> Cases_on `env` >>
  rw [bir_env_update_def, bir_env_lookup_def]
QED

Theorem bir_env_lookup_update_neq:
  !env var1 var2 v. 
    var1 <> var2 ==>
      bir_env_lookup (bir_env_update env var1 v) var2 = bir_env_lookup env var2
Proof
  Cases_on `var1` >> Cases_on `var2` >>
  rw [fetch "bir" "bir_var_t_11"] >>
  Cases_on `env` >>
  simp [bir_env_update_def] >>
  rw [bir_env_lookup_def] >>
  EVAL_TAC >>
  metis_tac []
QED

(* Lookup and relation are the same *)
Theorem bir_env_lookup_eq_rel:
  !env var v. bir_env_lookup_rel env var v <=> bir_env_lookup env var = SOME v
Proof
  rpt strip_tac >>
  Cases_on `env` >>
  Cases_on `var` >>
    rw [bir_env_lookup_def, bir_env_lookup_rel_def]
QED

(* Injective *)
Theorem bir_env_lookup_rel_inj:
  !env var v1 v2.
    bir_env_lookup_rel env var v1 ==>
    bir_env_lookup_rel env var v2 ==>
    v1 = v2
Proof
  Cases_on `env` >> Cases_on `var` >>
    simp [bir_env_lookup_rel_def]
QED

(* bitstring_split will never be NONE *)
Theorem bitstring_split_aux_size_of_bir_immtype:
  !ty acc bs. ?ll. bitstring_split_aux (size_of_bir_immtype ty) acc bs = SOME ll
Proof
  gen_tac >>
  `?n. size_of_bir_immtype ty = SUC n` by (Cases_on `ty` >> simp [size_of_bir_immtype_def]) >>
  measureInduct_on `LENGTH bs` >>
    Cases_on `bs` >>
    fs [bitstring_split_def, bitstring_split_aux_def] >>
    `LENGTH (DROP n t) < SUC (LENGTH t)` by rw [listTheory.LENGTH_DROP] >>
    metis_tac [bitstring_split_aux_def, listTheory.LENGTH_DROP]
QED

Theorem bitstring_split_size_of_bir_immtype:
  !ty bs. bitstring_split (size_of_bir_immtype ty) bs <> NONE
Proof
  simp [bitstring_split_def] >>
  metis_tac [bitstring_split_aux_size_of_bir_immtype, optionTheory.NOT_SOME_NONE]
QED

(* If the operands are typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_binexp:
  !binexp v1 v2 ty.
    ((type_of_bir_val v1 = BType_Imm ty) /\ (type_of_bir_val v2 = BType_Imm ty)) ==>
    ?v. bir_eval_binexp binexp v1 v2 v
Proof
  Cases_on `binexp` >>
  Cases_on `v1` >> Cases_on `v2` >>
  Cases_on `b` >> Cases_on `b'` >>
    rw [bir_eval_binexp_eq_compute_binexp] >>
    rw [bir_compute_binexp_def, bir_compute_binexp_imm_def] >>
    rw [val_from_imm_option_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def]
QED

(* Type conservation Theorem *)
Theorem bir_eval_binexp_keep_type:
  !binexp v1 v2 v ty.
    bir_eval_binexp binexp v1 v2 v ==>
    ((type_of_bir_val v1 = ty /\ type_of_bir_val v2 = ty) <=>
      type_of_bir_val v = ty)
Proof
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
  rw [type_of_bir_val_def, bir_eval_binexp_cases, type_of_bir_imm_def, bir_eval_binexp_imm_cases]
QED

(* Unary_exp always evaluates *)
Theorem type_of_bir_val_imp_bir_eval_unaryexp:
  !unaryexp v ty.
    (type_of_bir_val v = BType_Imm ty) ==>
    ?v'. bir_eval_unaryexp unaryexp v v'
Proof
  Cases_on `unaryexp` >>
  Cases_on `v` >>
  Cases_on `b` >>
    rw [bir_eval_unaryexp_eq_compute_unaryexp, type_of_bir_val_def] >>
    rw [bir_compute_unaryexp_def, bir_compute_unaryexp_imm_def] >>
    rw [val_from_imm_option_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def]
QED

(* Type conservation theorem *)
Theorem bir_eval_unaryexp_keep_type:
  !unaryexp v1 v2 ty.
    bir_eval_unaryexp unaryexp v1 v2 ==>
    (type_of_bir_val v1 = type_of_bir_val v2)
Proof
  Cases_on `v1` >> Cases_on `v2` >>
  Cases_on `b` >> Cases_on `b'` >>
    rw [type_of_bir_val_def, bir_eval_unaryexp_def, type_of_bir_imm_def, bir_eval_unaryexp_imm_cases]
QED

(* If the operands are typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_binpred:
  !binpred v1 v2 ty.
    ((type_of_bir_val v1 = BType_Imm ty) /\ (type_of_bir_val v2 = BType_Imm ty)) ==>
    ?v. bir_eval_binpred binpred v1 v2 v
Proof
  Cases_on `v1` >> Cases_on `v2` >>
  Cases_on `b` >> Cases_on `b'` >>
    rw [well_typed_bir_eval_binpred_eq_compute_binpred] >>
    rw [bir_compute_binpred_def, bir_compute_binpred_imm_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def]
QED

(* Type conservation theorem *)
Theorem bir_eval_binpred_correct_type:
  !binpred v1 v2 v ty.
    bir_eval_binpred binpred v1 v2 v ==>
    ((type_of_bir_val v1 = type_of_bir_val v2) /\ type_of_bir_val v = (BType_Imm Bit1))
Proof
  Cases_on `v1` >> Cases_on `v2` >> Cases_on `v` >>
  Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >>
    rw [type_of_bir_val_def, bir_eval_binpred_cases, type_of_bir_imm_def, bir_eval_binpred_imm_cases, bool2b_def]
QED

(* If the condition is typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_ifthenelse:
  !v v1 v2.
    (type_of_bir_val v = (BType_Imm Bit1)) ==>
    ?v3. bir_eval_ifthenelse v v1 v2 v3
Proof
  rw [bir_eval_ifthenelse_eq_compute_ifthenelse] >>
  Cases_on `v` >| [
    Cases_on `b` >>
    Cases_on `c` >>
      metis_tac [bir_compute_ifthenelse_def, bit1_is_boolean],

    fs [type_of_bir_val_def]
    ]
QED

(* Type conservation Theorem *)
Theorem bir_eval_ifthenelse_keep_type:
  !v v1 v2 v3 ty.
    bir_eval_ifthenelse v v1 v2 v3 ==>
    (type_of_bir_val v1 = ty /\ type_of_bir_val v2 = ty) ==>
    (type_of_bir_val v = (BType_Imm Bit1) <=> type_of_bir_val v3 = ty)
Proof
  Cases_on `v` >> Cases_on `v1` >> Cases_on `v2` >> Cases_on `v3` >>
  Cases_on `b` >> Cases_on `b'` >> Cases_on `b''` >> Cases_on `b'''` >>
  rw [type_of_bir_val_def, bir_eval_ifthenelse_cases, type_of_bir_imm_def,
    birT_def, birF_def]
QED

(* If the operands are correctly typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_load_bigendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_BigEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_load_littleendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_LittleEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_load_noendian:
  !aty vty v_mem v_addr rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) = 1))
  ==>
  ?v. bir_eval_load v_mem v_addr BEnd_NoEndian rty v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
    rw [bir_eval_load_eq_compute_load] >>
    rw [bir_compute_load_def, bir_compute_load_from_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    rw [val_from_imm_option_def] >>
    metis_tac [size_of_bir_immtype_leq_1]
QED


(* Type of bir_mem_concat *)
Theorem type_of_bir_imm_bir_mem_concat:
  !vl rty. type_of_bir_imm (bir_mem_concat vl rty) = rty
Proof
  Cases_on `rty` >>
    rw [bir_mem_concat_def, v2bs_def, n2bs_def] >>
    rw [type_of_bir_imm_def]
QED  

(* Type conservation theorem *)
Theorem bir_eval_load_correct_type:
  !v_mem v_addr en rty v.
    bir_eval_load v_mem v_addr en rty v ==>
    (type_of_bir_val v = (BType_Imm rty))
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >>
  Cases_on `en` >>

  simp [bir_eval_load_def, bir_eval_load_from_mem_cases] >>
  metis_tac [type_of_bir_val_def, type_of_bir_imm_def, type_of_bir_imm_bir_mem_concat]
QED

(* If the operands are correctly typed, then the expression evaluates *)
Theorem type_of_bir_val_imp_bir_eval_store_bigendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_BigEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype, bitstring_split_def] >>
      metis_tac [bitstring_split_aux_size_of_bir_immtype]
QED

Theorem type_of_bir_val_imp_bir_eval_store_littleendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_LittleEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype] >>
      metis_tac []
QED

Theorem type_of_bir_val_imp_bir_eval_store_noendian:
  !aty vty v_mem v_addr v_result rty.
  ((type_of_bir_val v_mem = (BType_Mem aty vty)) /\ 
    (type_of_bir_val v_addr = BType_Imm aty) /\
    (type_of_bir_val v_result = BType_Imm rty) /\
     ((size_of_bir_immtype rty) MOD (size_of_bir_immtype vty) = 0) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) <= 
        2 **(size_of_bir_immtype aty)) /\
     ((size_of_bir_immtype rty) DIV (size_of_bir_immtype vty) = 1))
  ==>
  ?v. bir_eval_store v_mem v_addr BEnd_NoEndian v_result v
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
    rw [bir_eval_store_eq_compute_store] >>
    rw [bir_compute_store_def, bir_compute_store_in_mem_def, bir_number_of_mem_splits_def] >>
    fs [type_of_bir_val_def, type_of_bir_imm_def] >>
    TRY CASE_TAC >>
      fs [bitstring_split_size_of_bir_immtype] >>
      metis_tac [size_of_bir_immtype_leq_1]
QED

(* Type conservation theorem *)
Theorem bir_eval_store_correct_type:
  !v_mem v_addr en v_result v.
    bir_eval_store v_mem v_addr en v_result v ==>
    (type_of_bir_val v = type_of_bir_val v_mem)
Proof
  Cases_on `v_mem` >> Cases_on `v_addr` >> Cases_on `v_result` >>
  Cases_on `en` >>

  simp [bir_eval_store_def, bir_eval_store_in_mem_cases] >>
  rw [type_of_bir_val_def, type_of_bir_imm_def] >>
  metis_tac [type_of_bir_val_def, type_of_bir_imm_def]
QED

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
    metis_tac [bir_eval_binexp_cases, bir_eval_binexp_keep_type, type_of_bir_val_def],

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
