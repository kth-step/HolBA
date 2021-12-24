open HolKernel Parse boolLib bossLib;

open bir_valuesTheory;
open bir_expTheory;
open bir_envTheory;
open bir_typing_expTheory;
open bir_exp_memTheory;
open bir_exp_substitutionsTheory;

open optionTheory;
open pred_setTheory;
open finite_mapTheory;

open pred_setSimps;

open HolBACoreSimps;

val _ = new_theory "bir_symb_support";



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

val bir_eval_exp_NONE_EQ_bir_exp_env_type_thm = store_thm(
   "bir_eval_exp_NONE_EQ_bir_exp_env_type_thm", ``
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

val bir_eval_exp_SOME_EQ_bir_exp_env_type_thm = store_thm(
   "bir_eval_exp_SOME_EQ_bir_exp_env_type_thm", ``
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

val bir_eval_exp_SOME_EQ_bir_exp_env_type_EMPTY_thm = store_thm(
   "bir_eval_exp_SOME_EQ_bir_exp_env_type_EMPTY_thm", ``
!env e ty.
(bir_vars_of_exp e = EMPTY) ==>
(
  (type_of_bir_exp e = SOME ty)
  <=>
  (?v. ((bir_eval_exp e env) = SOME v) /\ (type_of_bir_val v = ty))
)
``,
  METIS_TAC
    [bir_eval_exp_SOME_EQ_bir_exp_env_type_thm,
     bir_envty_includes_vs_def,
     NOT_IN_EMPTY]
);





val bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm = store_thm(
   "bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm", ``
!vs f e.
  (FINITE vs) ==>
  (bir_exp_subst (FUN_FMAP f (vs UNION bir_vars_of_exp e)) e) =
  (bir_exp_subst (FUN_FMAP f (bir_vars_of_exp e)) e)
``,
  Induct_on `e` >> (
    SIMP_TAC (std_ss++PRED_SET_ss) [bir_exp_subst_def, bir_vars_of_exp_def, bir_exp_subst_var_def, FLOOKUP_FUN_FMAP]
  ) >> (
    ASM_SIMP_TAC (std_ss++PRED_SET_ss) [bir_exp_t_11, UNION_ASSOC]
  ) >> (
    REPEAT STRIP_TAC >> (
    `FINITE (vs UNION (bir_vars_of_exp e')) /\ FINITE (bir_vars_of_exp e') /\
     FINITE (vs UNION (bir_vars_of_exp e)) /\ FINITE (bir_vars_of_exp e) /\

     FINITE (vs UNION (bir_vars_of_exp e) UNION (bir_vars_of_exp e')) /\ FINITE ((bir_vars_of_exp e) UNION (bir_vars_of_exp e')) /\
     FINITE (vs UNION (bir_vars_of_exp e') UNION (bir_vars_of_exp e'')) /\ FINITE ((bir_vars_of_exp e') UNION (bir_vars_of_exp e'')) /\
     FINITE (vs UNION (bir_vars_of_exp e) UNION (bir_vars_of_exp e'')) /\ FINITE ((bir_vars_of_exp e) UNION (bir_vars_of_exp e''))` by (
      METIS_TAC [FINITE_UNION, bir_vars_of_exp_FINITE]
    )) >> (
     METIS_TAC [UNION_COMM, UNION_ASSOC]
    )
  )
);

val bir_load_from_mem_IS_SOME_thm = store_thm(
   "bir_load_from_mem_IS_SOME_thm", ``
!vty sz aty mmap en anum.
  (if en = BEnd_NoEndian then vty = sz
        else bir_number_of_mem_splits vty sz aty ≠ NONE) ==>
  (?v. bir_load_from_mem vty sz aty mmap en anum = SOME v)
``,
  REPEAT STRIP_TAC >>
  `?abc. bir_number_of_mem_splits vty sz aty = SOME abc` by (
    Cases_on `en = BEnd_NoEndian` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_number_of_mem_splits_def]
    ) >>

    Q.ABBREV_TAC `abc = size_of_bir_immtype sz` >>
    `0 < abc` by (
      Q.UNABBREV_TAC `abc` >>
      Cases_on `sz` >> (
        FULL_SIMP_TAC (arith_ss++holBACore_ss) []
      )
    ) >>
    Cases_on `aty` >> (
      FULL_SIMP_TAC (arith_ss++holBACore_ss) []
    )
  ) >>

  Cases_on `en` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC [bir_load_from_mem_EQ_SOME, bir_number_of_mem_splits_ID]
  )
);

val bir_store_in_mem_IS_SOME_thm = store_thm(
   "bir_store_in_mem_IS_SOME_thm", ``
!sz vty aty v mmap en anum.
  (type_of_bir_imm v = sz) ==>
  (if en = BEnd_NoEndian then vty = sz
        else bir_number_of_mem_splits vty sz aty ≠ NONE) ==>
  (?vm. bir_store_in_mem vty aty v mmap en anum = SOME vm)
``,
  REPEAT STRIP_TAC >>
  `?abc. bir_number_of_mem_splits vty sz aty = SOME abc` by (
    Cases_on `en = BEnd_NoEndian` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_number_of_mem_splits_def]
    ) >>

    Q.ABBREV_TAC `abc = size_of_bir_immtype sz` >>
    `0 < abc` by (
      Q.UNABBREV_TAC `abc` >>
      Cases_on `sz` >> (
        FULL_SIMP_TAC (arith_ss++holBACore_ss) []
      )
    ) >>
    Cases_on `aty` >> (
      FULL_SIMP_TAC (arith_ss++holBACore_ss) []
    )
  ) >>

  Cases_on `en` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC [bir_store_in_mem_EQ_SOME, bir_number_of_mem_splits_ID]
  )
);



val _ = export_theory();
