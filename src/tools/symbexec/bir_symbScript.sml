open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;

open bir_valuesTheory;
open bir_expTheory;
open bir_envTheory;
open bir_programTheory;
open bir_typing_expTheory;

open bir_bool_expTheory;
open bir_exp_substitutionsTheory;

open optionTheory;
open pred_setTheory;

val _ = new_theory "bir_symb";

(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
- 'a_label    = bir_programcounter_t
- 'b_var      = string
- 'c_val      = bir_val_t
- 'd_extra    = bir_status_t

- 'e_symbol   = bir_var_t
- 'f_symbexpr = bir_exp_t
- 'g_type     = bir_type_t
*)
(*
"bir_concst_t = (bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t"
"bir_symbst_t = (bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t"
*)


(* functions to convert between conrete states *)
(* TODO: have to add observation in symbolic execution, could have this for another instance also?! no, probably not useful to split this *)
val birs_symb_to_concst_def = Define `
    birs_symb_to_concst s =
      (SymbConcSt
        s.bst_pc
        (\bvn. bir_env_lookup bvn s.bst_environ)
        s.bst_status)
`;

val birs_symb_from_concst_def = Define `
    birs_symb_from_concst (SymbConcSt lbl env status) =
      <|
        bst_pc       := lbl;
        bst_environ  := BEnv env;
        bst_status   := status
      |>
`;

(* sr_step_conc is in principle "bir_exec_step" *)


(* sr_step_symb, must define "birs_exec_step" now *)

(* first some general functions to deal with symbolic expressions (symbolic evaluation and interpretation) *)
val bir_exp_typeerror_def = Define `
    bir_exp_typeerror = BExp_BinExp BIExp_And (BExp_Const (Imm1 0w)) (BExp_Const (Imm8 0w))
`;
val birs_eval_exp_subst_def = Define `
    birs_eval_exp_subst e senv =
      bir_exp_subst
        (FUN_FMAP
          (\x. case senv (bir_var_name x) of
                | SOME x_ex =>
                    if type_of_bir_exp (x_ex) = SOME (bir_var_type x) then
                      x_ex
                    else
                      bir_exp_typeerror
                | NONE => bir_exp_typeerror)
          (bir_vars_of_exp e))
        e
`;
val birs_eval_exp_def = Define `
    birs_eval_exp e senv =
      let e' = birs_eval_exp_subst e senv; in
        OPTION_MAP (\et. (e', et)) (type_of_bir_exp e')
`;


val bir_val_to_constexp_def = Define `
   (bir_val_to_constexp (BVal_Imm i) = BExp_Const i) /\
   (bir_val_to_constexp (BVal_Mem aty vty mmap) = BExp_MemConst aty vty mmap)
`;
val birs_interpret_fun_def = Define `
    birs_interpret_fun i e =
      bir_eval_exp (bir_exp_subst (FUN_FMAP (\x. bir_val_to_constexp (THE (symb_interpr_get i x))) (bir_vars_of_exp e)) e) bir_env_empty
`;

(*
bir_type_of_bir_exp_NONE
    (type_of_bir_exp ex = NONE) ==>
    (bir_eval_exp ex env = NONE)

type_of_bir_exp_THM_with_envty
    (type_of_bir_exp e = SOME ty) ==>
    (bir_envty_includes_vs envty (bir_vars_of_exp e)) ==>
    (bir_env_satisfies_envty env envty) ==>
    (?v. ((bir_eval_exp e env) = SOME v) /\ (type_of_bir_val v = ty))``,
*)

val bir_eval_exp_NONE_IMP_bir_type_of_bir_exp_thm = store_thm(
   "bir_eval_exp_NONE_IMP_bir_type_of_bir_exp_thm", ``
!env envty e.
(bir_envty_of_env env = envty) ==>
(
  (bir_eval_exp e env = NONE)
  ==>
  ((type_of_bir_exp e = NONE) \/
   (~bir_envty_includes_vs envty (bir_vars_of_exp e)))
)
``,
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>

  `?ty. type_of_bir_exp e = SOME ty` by (
    METIS_TAC [NOT_IS_SOME_EQ_NONE, IS_SOME_EXISTS]
  ) >>

  METIS_TAC [type_of_bir_exp_THM_with_envty,
             NOT_NONE_SOME,
             bir_env_satisfies_envty_of_env]
);

val NOT_bir_v_in_envty_env_IMP = store_thm(
   "NOT_bir_v_in_envty_env_IMP", ``
!envty env bv vo.
  (~bir_envty_includes_v envty bv) ==>
  (bir_envty_of_env env = envty) ==>
  (bir_env_lookup (bir_var_name bv) env = vo) ==>
  (OPTION_ALL (\v. ~(type_of_bir_val v = bir_var_type bv)) vo)
``,
  Cases_on `envty` >> Cases_on `env` >>
  FULL_SIMP_TAC std_ss [bir_envty_includes_v_def, bir_envty_of_env_def, bir_env_lookup_def] >>

  REPEAT STRIP_TAC >>
  `f = (OPTION_MAP type_of_bir_val) o f'` by (
    METIS_TAC (type_rws (mk_thy_type {Tyop="bir_var_environment_typing_t", Thy="bir_env", Args=[]}))
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  Cases_on `f' (bir_var_name bv)` >- (
    METIS_TAC [OPTION_ALL_def]
  ) >>
  FULL_SIMP_TAC std_ss [OPTION_ALL_def]
);

val bir_eval_exp_with_var_not_in_env_thm = store_thm(
   "bir_eval_exp_with_var_not_in_env_thm", ``
!bv env vo e.
  (bv IN (bir_vars_of_exp e)) ==>
  (bir_env_lookup (bir_var_name bv) env = vo) ==>
  (OPTION_ALL (\v. ~(type_of_bir_val v = bir_var_type bv)) vo) ==>
  (bir_eval_exp e env = NONE)
``,
  Induct_on `e` >- (
    (* BExp_Const *)
    METIS_TAC [bir_vars_of_exp_def, NOT_IN_EMPTY]
  ) >- (
    (* BExp_MemConst *)
    METIS_TAC [bir_vars_of_exp_def, NOT_IN_EMPTY]
  ) >- (
    (* BExp_Den *)
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [bir_vars_of_exp_def, bir_eval_exp_def, bir_env_read_def,
       bir_env_check_type_def, bir_env_lookup_type_def] >>

    Cases_on `bir_env_lookup (bir_var_name b) env` >- (
      METIS_TAC []
    ) >>
    FULL_SIMP_TAC std_ss []
  ) >> (
    (* all combination forms *)
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_eval_exp_def, UNION_DEF, GSPECIFICATION] >>

    METIS_TAC
      [bir_eval_cast_REWRS,
       bir_eval_unary_exp_REWRS,
       bir_eval_bin_exp_REWRS,
       bir_eval_bin_pred_REWRS,
       bir_eval_memeq_REWRS,
       bir_eval_ifthenelse_REWRS,
       bir_eval_load_NONE_REWRS,
       bir_eval_store_NONE_REWRS]
  )
);

val NOT_bir_envty_includes_vs_IMP_bir_eval_exp_thm = store_thm(
   "NOT_bir_envty_includes_vs_IMP_bir_eval_exp_thm", ``
!env envty e.
(bir_envty_of_env env = envty) ==>
(
  (~bir_envty_includes_vs envty (bir_vars_of_exp e))
  ==>
  (bir_eval_exp e env = NONE)
)
``,
  REPEAT STRIP_TAC >>

  `?bv vo. (bv IN (bir_vars_of_exp e)) /\
   (bir_env_lookup (bir_var_name bv) env = vo) /\
   (OPTION_ALL (\v. ~(type_of_bir_val v = bir_var_type bv)) vo)` by (
    METIS_TAC [bir_envty_includes_vs_def, NOT_bir_v_in_envty_env_IMP]
  ) >>

  METIS_TAC [bir_eval_exp_with_var_not_in_env_thm]
);

val bir_eval_exp_NONE_EQ_bir_type_of_bir_exp_thm = store_thm(
   "bir_eval_exp_NONE_EQ_bir_type_of_bir_exp_thm", ``
!env envty e.
(bir_envty_of_env env = envty) ==>
(
  ((type_of_bir_exp e = NONE) \/
   (~bir_envty_includes_vs envty (bir_vars_of_exp e)))
  <=>
  (bir_eval_exp e env = NONE)
)
``,
  METIS_TAC [bir_type_of_bir_exp_NONE,
             bir_eval_exp_NONE_IMP_bir_type_of_bir_exp_thm,
             NOT_bir_envty_includes_vs_IMP_bir_eval_exp_thm]
);

val bir_number_of_mem_splits_1_IMP_types_thm = store_thm(
   "bir_number_of_mem_splits_1_IMP_types_thm", ``
!vty rty aty.
  (bir_number_of_mem_splits vty rty aty = SOME 1) ==>
  (vty = rty)
``,
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `rty` >> Cases_on `vty` >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
  )
);

val bir_load_from_mem_BEnd_NoEndian_IMP_types_thm = store_thm(
   "bir_load_from_mem_BEnd_NoEndian_IMP_types_thm", ``
!vty rty aty mmap en a v.
  (bir_load_from_mem vty rty aty mmap en a = SOME v) ==>
  (en = BEnd_NoEndian) ==>
  (vty = rty)
``,
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_load_from_mem_def] >>
  REPEAT GEN_TAC >>
  Cases_on `bir_number_of_mem_splits vty rty aty` >> (
    FULL_SIMP_TAC std_ss []
  ) >>

  FULL_SIMP_TAC std_ss [LET_DEF] >>
  CASE_TAC >>

  METIS_TAC [bir_number_of_mem_splits_1_IMP_types_thm]
);

val bir_load_from_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm = store_thm(
   "bir_load_from_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm", ``
!vty rty aty mmap en a v.
  (bir_load_from_mem vty rty aty mmap en a = SOME v) ==>
  (~(en = BEnd_NoEndian)) ==>
  (~(bir_number_of_mem_splits vty rty aty = NONE))
``,
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_load_from_mem_def] >>
  Cases_on `bir_number_of_mem_splits vty rty aty` >> (
    FULL_SIMP_TAC std_ss []
  )
);

val bir_store_in_mem_BEnd_NoEndian_IMP_types_thm = store_thm(
   "bir_store_in_mem_BEnd_NoEndian_IMP_types_thm", ``
!vty aty res mmap en a v.
  (bir_store_in_mem vty aty res mmap en a = SOME v) ==>
  (en = BEnd_NoEndian) ==>
  (type_of_bir_imm res = vty)
``,
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_store_in_mem_def] >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  REPEAT GEN_TAC >>
  Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm res) aty` >> (
    FULL_SIMP_TAC std_ss []
  ) >>

  CASE_TAC >>

  METIS_TAC [bir_number_of_mem_splits_1_IMP_types_thm]
);

val bir_store_in_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm = store_thm(
   "bir_store_in_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm", ``
!vty aty res mmap en a v.
  (bir_store_in_mem vty aty res mmap en a = SOME v) ==>
  (~(en = BEnd_NoEndian)) ==>
  (~(bir_number_of_mem_splits vty (type_of_bir_imm res) aty = NONE))
``,
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_store_in_mem_def] >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  REPEAT GEN_TAC >>
  Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm res) aty` >> (
    FULL_SIMP_TAC std_ss []
  )
);


val bir_eval_exp_SOME_IMP_type_of_bir_exp_thm = store_thm(
   "bir_eval_exp_SOME_IMP_type_of_bir_exp_thm", ``
!env e v ty.
  ((bir_eval_exp e env) = SOME v) ==>
  (type_of_bir_val v = ty) ==>
  (type_of_bir_exp e = SOME ty)
``,
  Induct_on `e` >- (
    (* BExp_Const *)
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def, type_of_bir_val_def, bir_eval_exp_def]
  ) >- (
    (* BExp_MemConst *)
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def, type_of_bir_val_def, bir_eval_exp_def]
  ) >- (
    (* BExp_Den *)
    FULL_SIMP_TAC std_ss [type_of_bir_exp_def, bir_eval_exp_def] >>
    FULL_SIMP_TAC std_ss [bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss []
  ) >> (
    ALL_TAC
  ) >| [
    (* BExp_Cast *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `bir_eval_exp e env` >- (
      METIS_TAC [bir_eval_cast_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    `type_of_bir_exp e1 = SOME ty1` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> (
      FULL_SIMP_TAC std_ss [bir_eval_cast_def]
    ) >>

    METIS_TAC [bir_exp_immTheory.type_of_bir_gencast, type_of_bir_val_def, bir_type_is_Imm_def]
  ,
    (* BExp_UnaryExp *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `bir_eval_exp e env` >- (
      METIS_TAC [bir_eval_unary_exp_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    `type_of_bir_exp e1 = SOME ty1` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> (
      FULL_SIMP_TAC std_ss [bir_eval_unary_exp_def]
    ) >>

    METIS_TAC [bir_exp_immTheory.type_of_bir_unary_exp, type_of_bir_val_def, bir_type_is_Imm_def]
  ,
    (* BExp_BinExp *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_bin_exp b1 (bir_eval_exp e1 env) (bir_eval_exp e2 env)` >>
    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_bin_exp_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_bin_exp_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    `type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> (
      FULL_SIMP_TAC std_ss [bir_eval_bin_exp_def]
    ) >>

    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [] >>

    METIS_TAC [bir_exp_immTheory.type_of_bir_bin_exp, type_of_bir_val_def, bir_type_is_Imm_def]
  ,
    (* BExp_BinPred *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_bin_pred b1 (bir_eval_exp e1 env) (bir_eval_exp e2 env)` >>
    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_bin_pred_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_bin_pred_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    `type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> (
      FULL_SIMP_TAC std_ss [bir_eval_bin_pred_def]
    ) >>

    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [] >>

    METIS_TAC [BType_Bool_def, bir_immTheory.type_of_bool2b, type_of_bir_val_def, bir_type_is_Imm_def]
  ,
    (* BExp_MemEq *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_memeq (bir_eval_exp e1 env) (bir_eval_exp e2 env)` >>
    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_memeq_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_memeq_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    `type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> (
      FULL_SIMP_TAC std_ss [bir_eval_memeq_def]
    ) >>

    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [] >>

    Q.UNABBREV_TAC `ty1` >> Q.UNABBREV_TAC `ty2` >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def] >>

    METIS_TAC [BType_Bool_def, bir_immTheory.type_of_bool2b, type_of_bir_val_def]
  ,
    (* BExp_IfThenElse *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_ifthenelse (bir_eval_exp ec env) (bir_eval_exp e1 env)
          (bir_eval_exp e2 env)` >>

    Cases_on `bir_eval_exp ec env` >- (
      METIS_TAC [bir_eval_ifthenelse_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp ec env = SOME vc` >>
    Q.ABBREV_TAC `tyc = type_of_bir_val vc` >>

    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_ifthenelse_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_ifthenelse_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    `type_of_bir_exp ec = SOME tyc /\ type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2` by (
      METIS_TAC []
    ) >>

    Cases_on `vc` >> (
      FULL_SIMP_TAC std_ss [bir_eval_ifthenelse_def]
    ) >>
    rename1 `bir_eval_exp ec env = SOME (BVal_Imm bc)` >>
    Cases_on `bc` >> (
      FULL_SIMP_TAC std_ss [bir_eval_ifthenelse_def]
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> (
      Q.UNABBREV_TAC `tyc` >> Q.UNABBREV_TAC `ty1` >> Q.UNABBREV_TAC `ty2` >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_ifthenelse_def]
    ) >> (
      (* the two cases where the true and false values are both immediates or memories *)
      CASE_TAC >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [] >>
      CASE_TAC >>
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [] >>

      METIS_TAC [BType_Bool_def, bir_immTheory.type_of_bool2b, type_of_bir_val_def]
    )
  ,
    (* BExp_Load *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_load (bir_eval_exp e1 env) (bir_eval_exp e2 env)` >>
    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_load_NONE_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_load_NONE_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    `type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> (
      FULL_SIMP_TAC std_ss [bir_eval_load_def]
    ) >>

    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [] >> (
      Q.UNABBREV_TAC `ty1` >> Q.UNABBREV_TAC `ty2` >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def] >>

      Cases_on `bir_load_from_mem b0 b1 b f b2 (b2n b')` >> (
        FULL_SIMP_TAC std_ss []
      ) >>

      `BType_Imm b1 = ty` by (
        METIS_TAC [bir_exp_memTheory.type_of_bir_load_from_mem, BType_Bool_def, type_of_bir_val_def]
      ) >>
      FULL_SIMP_TAC std_ss []
    ) >> (
      METIS_TAC [bir_load_from_mem_BEnd_NoEndian_IMP_types_thm,
                 bir_load_from_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm]
    )
  ,
    (* BExp_Store *)
    REWRITE_TAC [bir_eval_exp_def, type_of_bir_exp_def] >>
    REPEAT STRIP_TAC >>

    rename1 `bir_eval_store (bir_eval_exp e1 env) (bir_eval_exp e2 env) b2 (bir_eval_exp e3 env)` >>
    Cases_on `bir_eval_exp e1 env` >- (
      METIS_TAC [bir_eval_store_NONE_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e1 env = SOME v1` >>
    Q.ABBREV_TAC `ty1 = type_of_bir_val v1` >>

    Cases_on `bir_eval_exp e2 env` >- (
      METIS_TAC [bir_eval_store_NONE_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e2 env = SOME v2` >>
    Q.ABBREV_TAC `ty2 = type_of_bir_val v2` >>

    Cases_on `bir_eval_exp e3 env` >- (
      METIS_TAC [bir_eval_store_NONE_REWRS, NOT_NONE_SOME]
    ) >>
    rename1 `bir_eval_exp e3 env = SOME v3` >>
    Q.ABBREV_TAC `ty3 = type_of_bir_val v3` >>

    `type_of_bir_exp e1 = SOME ty1 /\ type_of_bir_exp e2 = SOME ty2 /\ type_of_bir_exp e3 = SOME ty3` by (
      METIS_TAC []
    ) >>

    Cases_on `v1` >> Cases_on `v2` >> Cases_on `v3` >> (
      FULL_SIMP_TAC std_ss [bir_eval_store_def]
    ) >>

    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [] >> (
      Q.UNABBREV_TAC `ty1` >> Q.UNABBREV_TAC `ty2` >> Q.UNABBREV_TAC `ty3` >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def] >>

      Cases_on `bir_store_in_mem b0 b b'' f b2 (b2n b')` >> (
        FULL_SIMP_TAC std_ss []
      )
    ) >- (
      (* NOENDIANNESS *)
      METIS_TAC [bir_store_in_mem_BEnd_NoEndian_IMP_types_thm, bir_exp_memTheory.type_of_bir_load_from_mem, BType_Bool_def, type_of_bir_val_def]
    ) >>

    (* OTHER ENDIANNESS *)
    METIS_TAC [bir_store_in_mem_NOT_BEnd_NoEndian_IMP_mem_splits_thm, type_of_bir_val_def]
  ]
);


val bir_eval_exp_SOME_IMP_type_of_bir_exp_envty_incl_thm = store_thm(
   "bir_eval_exp_SOME_IMP_type_of_bir_exp_envty_incl_thm", ``
!env envty e ty.
(bir_envty_of_env env = envty) ==>
(
  (?v. ((bir_eval_exp e env) = SOME v) /\ (type_of_bir_val v = ty))
  ==>
  ((type_of_bir_exp e = SOME ty) /\
  (bir_envty_includes_vs envty (bir_vars_of_exp e)))
)
``,
  REPEAT STRIP_TAC >- (
    METIS_TAC [bir_eval_exp_SOME_IMP_type_of_bir_exp_thm]
  ) >>

  CCONTR_TAC >>
  METIS_TAC [NOT_bir_envty_includes_vs_IMP_bir_eval_exp_thm, NOT_NONE_SOME]
);

val type_of_bir_exp_SOME_IMP_bir_eval_exp_thm = store_thm(
   "type_of_bir_exp_SOME_IMP_bir_eval_exp_thm", ``
!env envty e ty.
(bir_envty_of_env env = envty) ==>
(
  (type_of_bir_exp e = SOME ty) /\
  (bir_envty_includes_vs envty (bir_vars_of_exp e))
  <=>
  (?v. ((bir_eval_exp e env) = SOME v) /\ (type_of_bir_val v = ty))
)
``,
  METIS_TAC [type_of_bir_exp_THM_with_envty,
             bir_eval_exp_SOME_IMP_type_of_bir_exp_envty_incl_thm,
             bir_env_satisfies_envty_of_env]
);


(* now a symbolic state *)
val _ = Datatype `birs_state_t = <|
  bsst_pc       : bir_programcounter_t;
  bsst_environ  : string -> bir_exp_t option;
  bsst_status   : bir_status_t;
  bsst_pcond    : bir_exp_t
|>`;

val birs_symb_to_symbst_def = Define `
    birs_symb_to_symbst s =
      (SymbSymbSt
        s.bsst_pc
        s.bsst_environ
        s.bsst_pcond
        s.bsst_status)
`;

val birs_symb_from_symbst_def = Define `
    birs_symb_from_symbst (SymbSymbSt lbl env pcond status) =
      <|
        bsst_pc       := lbl;
        bsst_environ  := env;
        bsst_pcond    := pcond;
        bsst_status   := status
      |>
`;

val birs_state_is_terminated_def = Define `
    birs_state_is_terminated st =
      (st.bsst_status <> BST_Running)
`;
val birs_state_set_typeerror_def = Define `
    birs_state_set_typeerror st =
      (st with bsst_status := BST_TypeError)`;
val birs_state_set_failed_def = Define `
    birs_state_set_failed st =
      (st with bsst_status := BST_Failed)
`;


(* now the definition of a symbolic execution step *)


(* ... *)

val birs_exec_stmt_assign_def = Define `
    birs_exec_stmt_assign v ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, vaty) =>
         if vaty = bir_var_type v then
           {st with bsst_environ := ((bir_var_name v =+ (SOME vaex)) st.bsst_environ)}
         else
           {birs_state_set_typeerror st}
     | NONE => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assert_def = Define `
    birs_exec_stmt_assert ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssertionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assume_def = Define `
    birs_exec_stmt_assume ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssumptionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_observe_def = Define `
    birs_exec_stmt_observe oid ec el obf st = {st}
`;

val birs_exec_stmtB_def = Define `
   (birs_exec_stmtB (BStmt_Assert ex) st =
     (birs_exec_stmt_assert ex st)) /\
   (birs_exec_stmtB (BStmt_Assume ex) st =
     (birs_exec_stmt_assume ex st)) /\
   (birs_exec_stmtB (BStmt_Assign v ex) st =
     (birs_exec_stmt_assign v ex st)) /\
   (birs_exec_stmtB (BStmt_Observe oid ec el obf) st =
     birs_exec_stmt_observe oid ec el obf st)
`;

(* ... *)

(* TODO: OHHHHHHHHHHHHHH NOOOOOOOOOOOOOOOOOOO *)
val birs_exec_stmt_halt_def = Define `
    birs_exec_stmt_halt ex (st : birs_state_t) = {st}
(*
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, _) => {st with bsst_status := BST_Halted ex}
     | NONE => {birs_state_set_typeerror st}
*)
`;

val birs_exec_stmt_jmp_to_label_def = Define `
    birs_exec_stmt_jmp_to_label p (st : birs_state_t) (l : bir_label_t) =
    if MEM l (bir_labels_of_program p) then
      st with bsst_pc := bir_block_pc l
    else st with bsst_status := (BST_JumpOutside l)
`;

val birs_eval_label_exp_def = Define `
   (birs_eval_label_exp (BLE_Label l) senv pcond = SOME {l}) /\
   (birs_eval_label_exp (BLE_Exp e)   senv pcond =
     case birs_eval_exp e senv of
      | SOME (vaex, BType_Imm _) => SOME {BL_Address iv | ?i. birs_interpret_fun i pcond = SOME bir_val_true /\ birs_interpret_fun i vaex = SOME (BVal_Imm iv)}
      | _ => NONE
   )
`;

val birs_exec_stmt_jmp_def = Define `
    birs_exec_stmt_jmp p le (st : birs_state_t) =
    case birs_eval_label_exp le st.bsst_environ st.bsst_pcond of
      | NONE => {birs_state_set_typeerror st}
      | SOME ls => IMAGE (birs_exec_stmt_jmp_to_label p st) ls
`;

val birs_exec_stmt_cjmp_def = Define `
    birs_exec_stmt_cjmp p ec l1 l2 (st : birs_state_t) =
      case birs_eval_exp ec st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        (birs_exec_stmt_jmp p l1 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex)) UNION
        (birs_exec_stmt_jmp p l2 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex)))
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmtE_def = Define `
   (birs_exec_stmtE p (BStmt_Jmp l) st =
     birs_exec_stmt_jmp p l st) /\
   (birs_exec_stmtE p (BStmt_CJmp e l1 l2) st =
     birs_exec_stmt_cjmp p e l1 l2 st) /\
   (birs_exec_stmtE p (BStmt_Halt ex) st =
     birs_exec_stmt_halt ex st)
`;

val birs_exec_stmt_def = Define `
   (birs_exec_stmt (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st =
     let (sts') = birs_exec_stmtB bst st in
     IMAGE (\st'.
     if (birs_state_is_terminated st') then
       (st')
     else
       (st' with bsst_pc updated_by bir_pc_next)) sts') /\
   (birs_exec_stmt p (BStmtE bst) st =
     (birs_exec_stmtE p bst st))
`;

val birs_exec_step_def = Define `
    birs_exec_step p state =
  if (birs_state_is_terminated state) then {state} else
  case (bir_get_current_statement p state.bsst_pc) of
    | NONE => {birs_state_set_failed state}
    | SOME stm => (birs_exec_stmt p stm state)
`;

(* now the symbolic execution record *)
val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir prog =
    <|
      sr_val_true        := bir_val_true;
      sr_mk_exp_symb_f   := BExp_Den;
      sr_mk_exp_conj_f   := BExp_BinExp BIExp_And;
      sr_mk_exp_eq_f     := \e1. if option_CASE (type_of_bir_exp e1) F bir_type_is_Mem then BExp_MemEq e1 else BExp_BinPred BIExp_Equal e1;

      sr_subst_f         := \(s,e). bir_exp_subst (FUPDATE FEMPTY (s,e));

      (* symbols of symbolic exepressions *)
      sr_symbols_f       := bir_vars_of_exp;

      (* type business *)
      sr_typeof_val      := type_of_bir_val;
      sr_typeof_symb     := bir_var_type;
      sr_typeof_exp      := type_of_bir_exp;
      sr_ARB_val         := bir_val_default;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     := birs_interpret_fun;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       := birs_symb_to_concst o SND o (bir_exec_step prog) o birs_symb_from_concst;

      sr_step_symb       := (IMAGE birs_symb_to_symbst) o (birs_exec_step prog) o birs_symb_from_symbst;
   |>
`;

(* TODO: single step example (with "prototypical" property transfer) *)

(* TODO: prove soundness of this instance here (several soundness properties) *)

(* TODO: multiple step example (and also propert property transfer), best to use the simple motor set function from the beginning. or something equally simple *)

(* TODO: want to have another simple instance language? *)

(* TODO: have to think how to add memory structure expressions on top of BIR expressions, possibly make another instance! *)

val _ = export_theory();
