open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory
open wordsLib pred_setTheory;

val _ = new_theory "bir_typing_exp";


(* ------------------------------------------------------------------------- *)
(*  Expressions                                                              *)
(* ------------------------------------------------------------------------- *)

val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_type_ss = rewrites (type_rws ``:bir_type_t``);


val type_of_bir_exp_def = Define `
  (type_of_bir_exp (BExp_Const i) = SOME (BType_Imm (type_of_bir_imm i))) /\

  (type_of_bir_exp (BExp_Den v) = SOME (bir_var_type v)) /\

  (type_of_bir_exp (BExp_Cast ct e rty) = (case (type_of_bir_exp e) of
      NONE => NONE
    | SOME ty => (if (bir_type_is_Imm ty) then SOME (BType_Imm rty) else NONE))) /\

  (type_of_bir_exp (BExp_UnaryExp et e) = (case (type_of_bir_exp e) of
      NONE => NONE
    | SOME ty => (if (bir_type_is_Imm ty) then
        SOME ty else NONE))) /\

  (type_of_bir_exp (BExp_BinExp et e1 e2) = (case (type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bir_type_is_Imm ty1) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _ => NONE)) /\

  (type_of_bir_exp (BExp_BinPred pt e1 e2) = (case (type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bir_type_is_Imm ty1) /\ (ty2 = ty1)) then SOME BType_Bool else NONE)
       | _, _ => NONE)) /\


  (type_of_bir_exp (BExp_IfThenElse ec e1 e2) = (case (type_of_bir_exp ec, type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ect, SOME ty1, SOME ty2) => (if ((ect = BType_Bool) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _, _ => NONE)) /\

  (type_of_bir_exp (BExp_Load me ae en rty) = (case (type_of_bir_exp me, type_of_bir_exp ae) of
       (SOME (BType_Mem aty vty), SOME (BType_Imm aty')) => (if (
            (aty = aty') /\ (if en = BEnd_NoEndian then (vty = rty) else (bir_number_of_mem_splits vty rty aty <> NONE))
           ) then SOME (BType_Imm rty) else NONE)
       | _, _ => NONE)) /\

  (type_of_bir_exp (BExp_Store me ae en v) = (case (type_of_bir_exp me, type_of_bir_exp ae, type_of_bir_exp v) of
       (SOME (BType_Mem aty vty), SOME (BType_Imm aty'), SOME (BType_Imm rty)) => (if (
            (aty = aty') /\ (if en = BEnd_NoEndian then (vty = rty) else (bir_number_of_mem_splits vty rty aty <> NONE))
           ) then SOME (BType_Mem aty vty) else NONE)
       | _, _, _ => NONE))`;



val type_of_bir_exp_THM = store_thm ("type_of_bir_exp_THM",
 ``!env. (bir_is_well_typed_env env) ==> !e ty. (type_of_bir_exp e = SOME ty) ==>
              ((bir_eval_exp e env = BVal_Unknown) \/ (type_of_bir_val (bir_eval_exp e env) = SOME ty))``,

GEN_TAC >> STRIP_TAC >>
Induct >> (
  SIMP_TAC (list_ss++bir_val_ss) [bir_eval_exp_def, type_of_bir_exp_def,
     type_of_bir_val_def] >>
  REPEAT CASE_TAC
) >- (
  METIS_TAC[bir_is_well_typed_env_read]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_cast_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_cast_REWRS,
    type_of_bir_gencast]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_unary_exp_REWRS,
    type_of_bir_unary_exp]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_bin_exp_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_bin_exp_REWRS,
    type_of_bir_bin_exp]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_bin_pred_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_bin_pred_REWRS,
    type_of_bir_val_def, BType_Bool_def, type_of_bool2b]
) >- (
  Cases_on `bir_eval_exp e env = BVal_Unknown` >- (
    ASM_SIMP_TAC std_ss [bir_eval_ifthenelse_REWRS]
  ) >>
  FULL_SIMP_TAC std_ss [bir_eval_ifthenelse_REWRS, bir_type_is_Imm_def] >> (
    FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_ifthenelse_REWRS,
      BType_Bool_def] >>
    CASE_TAC
  )
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_load_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS, bir_eval_load_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    METIS_TAC[type_of_bir_load_from_mem]
  )
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_store_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS, bir_eval_store_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC
));


val type_of_bir_exp_EQ_SOME_REWRS = store_thm ("type_of_bir_exp_EQ_SOME_REWRS",``
  (!i ty. (type_of_bir_exp (BExp_Const i) = SOME ty) <=> (ty = BType_Imm (type_of_bir_imm i))) /\

  (!v ty. (type_of_bir_exp (BExp_Den v) = SOME ty) <=> (ty = bir_var_type v)) /\

  (!ct e ty ty'. (type_of_bir_exp (BExp_Cast ct e ty') = SOME ty) <=> (
     (ty = BType_Imm ty') /\ (?it. (type_of_bir_exp e = SOME (BType_Imm it))))) /\

  (!et e ty. (type_of_bir_exp (BExp_UnaryExp et e) = SOME ty) <=> (
     (bir_type_is_Imm ty) /\ (type_of_bir_exp e = SOME ty))) /\

  (!et e1 e2 ty. (type_of_bir_exp (BExp_BinExp et e1 e2) = SOME ty) <=> (
     (bir_type_is_Imm ty) /\ (type_of_bir_exp e1 = SOME ty) /\ (type_of_bir_exp e2 = SOME ty))) /\

  (!pt e1 e2 ty. (type_of_bir_exp (BExp_BinPred pt e1 e2) = SOME ty) <=> (
     (ty = BType_Bool) /\ (?it. (type_of_bir_exp e1 = SOME (BType_Imm it)) /\
                              (type_of_bir_exp e2 = SOME (BType_Imm it))))) /\

  (!ce e1 e2 ty. (type_of_bir_exp (BExp_IfThenElse ce e1 e2) = SOME ty) <=> (
     (type_of_bir_exp ce = SOME BType_Bool) /\
     (type_of_bir_exp e1 = SOME ty) /\
     (type_of_bir_exp e2 = SOME ty))) /\

  (!rty ty ae en me. (type_of_bir_exp (BExp_Load me ae en rty) = SOME ty) <=> (
     (ty = BType_Imm rty) /\ (?at vt. (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
                            (type_of_bir_exp ae = SOME (BType_Imm at)) /\
                            (if en = BEnd_NoEndian then (vt = rty) else
                                  (bir_number_of_mem_splits vt rty at <> NONE))))) /\

  (!ty ae en me v. (type_of_bir_exp (BExp_Store me ae en v) = SOME ty) <=> (
     ?at vt rty. (ty = BType_Mem at vt) /\
             (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
             (type_of_bir_exp ae = SOME (BType_Imm at)) /\
             (type_of_bir_exp v = SOME (BType_Imm rty)) /\
             (if en = BEnd_NoEndian then (vt = rty) else
                                  (bir_number_of_mem_splits vt rty at <> NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bir_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >>
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
));




val type_of_bir_exp_EQ_NONE_REWRS = store_thm ("type_of_bir_exp_EQ_NONE_REWRS",``
  (!i. ~(type_of_bir_exp (BExp_Const i) = NONE)) /\

  (!v. ~(type_of_bir_exp (BExp_Den v) = NONE)) /\

  (!ct e ty ty'. (type_of_bir_exp (BExp_Cast ct e ty') = NONE) <=> (
     (!ity. (type_of_bir_exp e <> SOME (BType_Imm ity))))) /\

  (!et e. (type_of_bir_exp (BExp_UnaryExp et e) = NONE) <=> (
     (!ity. type_of_bir_exp e <> SOME (BType_Imm ity)))) /\

  (!et e1 e2. (type_of_bir_exp (BExp_BinExp et e1 e2) = NONE) <=> !ity.
     (type_of_bir_exp e1 <> SOME (BType_Imm ity)) \/
     (type_of_bir_exp e2 <> SOME (BType_Imm ity))) /\

  (!pt e1 e2. (type_of_bir_exp (BExp_BinPred pt e1 e2) = NONE) <=> !ity.
     (type_of_bir_exp e1 <> SOME (BType_Imm ity)) \/
     (type_of_bir_exp e2 <> SOME (BType_Imm ity))) /\

  (!ce e1 e2 ty. (type_of_bir_exp (BExp_IfThenElse ce e1 e2) = NONE) <=> (
     (type_of_bir_exp ce <> SOME BType_Bool) \/
     (type_of_bir_exp e1 = NONE) \/
     (type_of_bir_exp e2 <> type_of_bir_exp e1))) /\

  (!rty ty ae en me. (type_of_bir_exp (BExp_Load me ae en rty) = NONE) <=> (
     (!at vt. (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
              (type_of_bir_exp ae = SOME (BType_Imm at)) ==>
              (if en = BEnd_NoEndian then (vt <> rty) else
                   (bir_number_of_mem_splits vt rty at = NONE))))) /\

  (!ty ae en me v. (type_of_bir_exp (BExp_Store me ae en v) = NONE) <=> (
     !at vt rty.
             (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
             (type_of_bir_exp ae = SOME (BType_Imm at)) /\
             (type_of_bir_exp v = SOME (BType_Imm rty)) ==>
             (if en = BEnd_NoEndian then (vt <> rty) else
                                  (bir_number_of_mem_splits vt rty at = NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bir_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >>
    METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >>
    METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss) []
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
));



val bir_is_well_typed_exp_def = Define `bir_is_well_typed_exp e <=>  (type_of_bir_exp e <> NONE)`


(* ------------------------------------------------------------------------- *)
(*  Looking at  variables used somewhere in an expression                    *)
(* ------------------------------------------------------------------------- *)

val bir_vars_of_exp_def = Define `
  (bir_vars_of_exp (BExp_Const _) = {}) /\
  (bir_vars_of_exp (BExp_Den v) = {v}) /\
  (bir_vars_of_exp (BExp_Cast _ e _) = bir_vars_of_exp e) /\
  (bir_vars_of_exp (BExp_UnaryExp _ e) = bir_vars_of_exp e) /\
  (bir_vars_of_exp (BExp_BinExp _ e1 e2) = (bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_BinPred _ e1 e2) = (bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_IfThenElse ec e1 e2) = (bir_vars_of_exp ec UNION bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_Load me ae _ _) = (bir_vars_of_exp me UNION bir_vars_of_exp ae)) /\
  (bir_vars_of_exp (BExp_Store me ae _ ve) = (bir_vars_of_exp me UNION bir_vars_of_exp ae UNION bir_vars_of_exp ve))`;


val bir_vars_of_exp_THM = store_thm ("bir_vars_of_exp_THM",
``!env1 env2 e. (!v. v IN (bir_vars_of_exp e) ==>
                     (bir_env_read v env1 = bir_env_read v env2)) ==>
                (bir_eval_exp e env1 = bir_eval_exp e env2)``,

GEN_TAC >> GEN_TAC >> Induct >> REPEAT STRIP_TAC >> (
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pred_setTheory.IN_UNION,
    pred_setTheory.NOT_IN_EMPTY, pred_setTheory.IN_INSERT,
    bir_eval_exp_def]
));


val bir_eval_exp_FINITE = store_thm ("bir_eval_exp_FINITE",
``!e. FINITE (bir_vars_of_exp e)``,

Induct >> (
  ASM_SIMP_TAC std_ss [bir_vars_of_exp_def,
    pred_setTheory.FINITE_INSERT, pred_setTheory.FINITE_EMPTY,
    pred_setTheory.FINITE_UNION]
));


val type_of_bir_exp_THM_with_init_vars = store_thm ("type_of_bir_exp_THM_with_init_vars",
  ``!env e ty. (type_of_bir_exp e = SOME ty) ==>
               (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
               (type_of_bir_val (bir_eval_exp e env) = SOME ty)``,

GEN_TAC >> Induct >> (
  SIMP_TAC (std_ss++bir_val_ss) [bir_eval_exp_def, BType_Bool_def,
    type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def,
    bir_env_vars_are_initialised_UNION, bir_env_vars_are_initialised_INSERT,
    bir_env_vars_are_initialised_EMPTY, PULL_EXISTS, PULL_FORALL, bir_type_is_Imm_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_type_is_Imm_def]
) >- (
  rename1 `bir_env_read v env` >>
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [bir_env_read_def, bir_env_var_is_initialised_def, bir_var_name_def,
    bir_var_type_def, pairTheory.pair_case_thm]
) >- (
  SIMP_TAC (std_ss++bir_val_ss) [bir_eval_cast_REWRS, type_of_bir_gencast]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_unary_exp_REWRS, type_of_bir_unary_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_exp_REWRS, type_of_bir_bin_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_pred_REWRS, type_of_bir_val_def,
    type_of_bool2b, BType_Bool_def]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_ifthenelse_REWRS] >>
  METIS_TAC[]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_load_BASIC_REWR] >>
  rename1 `bir_load_from_mem vt ity at mmap en (b2n i)` >>
  Cases_on `bir_load_from_mem vt ity at mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_load_from_mem_EQ_NONE] >>
    Cases_on `en = BEnd_NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bir_val_ss) [] >>
  METIS_TAC [type_of_bir_load_from_mem]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_store_BASIC_REWR] >>
  rename1 `bir_store_in_mem vt at ity mmap en (b2n i)` >>
  Cases_on `bir_store_in_mem vt at ity mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_store_in_mem_EQ_NONE] >>
    Cases_on `en = BEnd_NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bir_val_ss) []
));


(* --------------------------- *)
(*  EXISTENCE OF SUITABLE ENVS *)
(* --------------------------- *)


val bir_default_value_of_type_def = Define `
  (bir_default_value_of_type (BType_Imm s) = BVal_Imm (n2bs 0 s)) /\
  (bir_default_value_of_type (BType_Mem a_s v_s) = BVal_Mem a_s v_s (K 0))`;

val bir_default_value_of_type_SPEC = store_thm ("bir_default_value_of_type_SPEC",
  ``!ty. type_of_bir_val (bir_default_value_of_type ty) = SOME ty``,

Cases >> (
  SIMP_TAC std_ss [bir_default_value_of_type_def, type_of_bir_val_def, type_of_n2bs]
));


val bir_immtype_t_LIST_def = Define `bir_immtype_t_LIST = ^(listSyntax.mk_list (bir_immSyntax.bir_immtype_t_list, bir_immSyntax.bir_immtype_t_ty))`;


val bir_immtype_t_LIST_THM = store_thm ("bir_immtype_t_LIST_THM",
  ``!s. MEM s bir_immtype_t_LIST``,
Cases >> SIMP_TAC list_ss [bir_immtype_t_LIST_def]);

val bir_immtype_t_UNIV_SPEC = store_thm ("bir_immtype_t_UNIV_SPEC",
  ``(UNIV:bir_immtype_t set) = set bir_immtype_t_LIST``,

SIMP_TAC list_ss [EXTENSION, bir_immtype_t_LIST_THM, IN_UNIV]);


val bir_immtype_t_FINITE_UNIV = store_thm ("bir_immtype_t_FINITE_UNIV",
  ``FINITE (UNIV : (bir_immtype_t set))``,
REWRITE_TAC[bir_immtype_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]);



val bir_type_t_LIST_def = (let
  open bir_valuesSyntax bir_immSyntax
  val imm_types = List.map mk_BType_Imm bir_immtype_t_list
  val mem_types = List.map mk_BType_Mem (flatten (
     List.map (fn v1 => List.map (fn v2 => (v1, v2)) bir_immtype_t_list) bir_immtype_t_list))
  val t = listSyntax.mk_list (imm_types @ mem_types, bir_type_t_ty)
in
  Define `bir_type_t_LIST = ^t`
end);


val bir_type_t_LIST_THM = store_thm ("bir_type_t_LIST_THM",
  ``!ty. MEM ty bir_type_t_LIST``,

SIMP_TAC list_ss [bir_type_t_LIST_def] >>
SIMP_TAC (list_ss++DatatypeSimps.expand_type_quants_ss[``:bir_immtype_t``, ``:bir_type_t``]) []);


val bir_type_t_UNIV_SPEC = store_thm ("bir_type_t_UNIV_SPEC",
  ``(UNIV:bir_type_t set) = set bir_type_t_LIST``,

SIMP_TAC list_ss [EXTENSION, bir_type_t_LIST_THM, IN_UNIV]);


val bir_type_t_FINITE_UNIV = store_thm ("bir_type_t_FINITE_UNIV",
  ``FINITE (UNIV : (bir_type_t set))``,
REWRITE_TAC[bir_type_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]);


val bir_env_vars_are_initialised_FINITE = store_thm ("bir_env_vars_are_initialised_FINITE",
  ``!vs env. bir_env_vars_are_initialised env vs ==> FINITE vs``,

REPEAT STRIP_TAC >>
Cases_on `env` >> rename1 `BEnv env` >>
`IMAGE bir_var_name vs SUBSET FDOM env` by (
  FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def, SUBSET_DEF, IN_IMAGE,
    PULL_EXISTS] >>
  REPEAT STRIP_TAC >>
  rename1 `v IN vs` >>
  Q.PAT_X_ASSUM `!v. _` (MP_TAC o Q.SPEC `v`) >>
  Cases_on `v` >> rename1 `BVar vn vty` >>
  ASM_SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_lookup_def,
    finite_mapTheory.flookup_thm, PULL_EXISTS, bir_var_name_def]
) >>

`FINITE (IMAGE bir_var_name vs)` by METIS_TAC[
  SUBSET_FINITE, finite_mapTheory.FDOM_FINITE] >>

Q.ABBREV_TAC `VS = BIGUNION (IMAGE (\vn. IMAGE (\ty. BVar vn ty) UNIV) (IMAGE bir_var_name vs))` >>
`vs SUBSET VS` by (
  Q.UNABBREV_TAC `VS` >>
  SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_UNIV] >>
  REPEAT STRIP_TAC >>
  rename1 `v IN vs` >>
  Q.EXISTS_TAC `v` >>
  Q.EXISTS_TAC `bir_var_type v` >>
  Cases_on `v` >>
  ASM_SIMP_TAC std_ss [bir_var_type_def, bir_var_name_def]
) >>

`FINITE VS` suffices_by METIS_TAC[SUBSET_FINITE] >>
Q.UNABBREV_TAC `VS` >>
SIMP_TAC std_ss [FINITE_BIGUNION_EQ, IN_IMAGE, PULL_EXISTS] >>
METIS_TAC[IMAGE_FINITE, bir_type_t_FINITE_UNIV]);



val bir_var_set_is_well_typed_def = Define `bir_var_set_is_well_typed vs <=>
  (!v1 v2. (v1 IN vs /\ v2 IN vs /\ (bir_var_name v1 = bir_var_name v2)) ==>
           (bir_var_type v1 = bir_var_type v2))`;

val bir_var_set_is_well_typed_INJ_DEF = store_thm ("bir_var_set_is_well_typed_INJ_DEF",
  ``bir_var_set_is_well_typed vs <=> INJ bir_var_name vs UNIV``,

SIMP_TAC std_ss [bir_var_set_is_well_typed_def, INJ_DEF, IN_UNIV,
  bir_var_eq_EXPAND] >>
METIS_TAC[]);


val bir_env_vars_are_initialised_WELL_TYPED = store_thm ("bir_env_vars_are_initialised_WELL_TYPED",
  ``!vs env. bir_env_vars_are_initialised env vs ==> bir_var_set_is_well_typed vs``,

  SIMP_TAC std_ss [bir_var_set_is_well_typed_def, bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `v1` >> Cases_on `v2` >>
  rename1 `bir_var_name (BVar vn1 vty1) = bir_var_name (BVar vn2 vty2)` >>
  FULL_SIMP_TAC std_ss [bir_var_name_def, bir_var_type_def] >>


  `bir_env_var_is_initialised env (BVar vn2 vty1)` by METIS_TAC[] >>
  `bir_env_var_is_initialised env (BVar vn2 vty2)` by METIS_TAC[] >>
  FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>
  FULL_SIMP_TAC std_ss []
);


val bir_env_vars_are_initialised_ENV_EXISTS = store_thm ("bir_env_vars_are_initialised_ENV_EXISTS",
  ``!vs. (?env. bir_env_vars_are_initialised env vs) <=> (FINITE vs /\ bir_var_set_is_well_typed vs)``,

GEN_TAC >> EQ_TAC >- (
  METIS_TAC[bir_env_vars_are_initialised_WELL_TYPED, bir_env_vars_are_initialised_FINITE]
) >>
REPEAT STRIP_TAC >>
Q.ABBREV_TAC `VF = (\v. (bir_var_type v, SOME (bir_default_value_of_type (bir_var_type v))))` >>
Q.ABBREV_TAC `M1 = FUN_FMAP VF vs` >>
EXISTS_TAC ``BEnv (MAP_KEYS bir_var_name M1)`` >>

`FDOM M1 = vs` by METIS_TAC[finite_mapTheory.FDOM_FMAP] >>
`INJ bir_var_name (FDOM M1) UNIV` by METIS_TAC [bir_var_set_is_well_typed_INJ_DEF] >>

SIMP_TAC std_ss [bir_env_vars_are_initialised_def]  >>
Cases >> rename1 `BVar vn vty` >>
ASM_SIMP_TAC std_ss [bir_env_var_is_initialised_def,
  bir_env_lookup_def, finite_mapTheory.FLOOKUP_MAP_KEYS] >>
REPEAT STRIP_TAC >>

`!v'. ((vn = bir_var_name v') ∧ v' IN vs) <=> (v' = BVar vn vty)` by (
  FULL_SIMP_TAC std_ss [INJ_DEF, IN_UNIV] >>
  METIS_TAC[bir_var_name_def]
) >>
ASM_SIMP_TAC std_ss [] >>

Q.UNABBREV_TAC `M1` >>
Q.UNABBREV_TAC `VF` >>
ASM_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_FUN_FMAP,
  bir_default_value_of_type_SPEC, bir_var_type_def]);

val _ = export_theory();
