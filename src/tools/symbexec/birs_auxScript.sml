open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open symb_interpretTheory;
open symb_recordTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "birs_aux";

val birs_symb_symbst_pc_thm = store_thm(
   "birs_symb_symbst_pc_thm", ``
!s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
);

val birs_symb_concst_pc_thm = store_thm(
   "birs_symb_concst_pc_thm", ``
!s.
  symb_concst_pc (birs_symb_to_concst s) = s.bst_pc
``,
  REWRITE_TAC [symb_recordTheory.symb_concst_pc_def, bir_symbTheory.birs_symb_to_concst_def]
);
(* ........................... *)

val symb_symbols_set_ALT_thm = store_thm(
   "symb_symbols_set_ALT_thm", ``
!sr Pi.
  symb_symbols_set sr Pi = (BIGUNION (IMAGE (symb_symbols sr) Pi))
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_def, IMAGE_DEF]
);

val birs_symb_symbols_set_EQ_thm = store_thm(
   "birs_symb_symbols_set_EQ_thm", ``
!prog Pi.
  symb_symbols_set (bir_symb_rec_sbir prog) (IMAGE birs_symb_to_symbst Pi) = BIGUNION (IMAGE birs_symb_symbols Pi)
``,
  FULL_SIMP_TAC (std_ss) [symb_symbols_set_ALT_thm, EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [IN_BIGUNION_IMAGE] >>
  FULL_SIMP_TAC (std_ss) [IN_IMAGE] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm]
  )
);
(* ........................... *)

val birs_exps_of_senv_def = Define `
    birs_exps_of_senv senv =
      {e | (?vn. senv vn = SOME e)}
`;

val birs_exps_of_senv_COMP_def = Define `
    birs_exps_of_senv_COMP excset senv =
      {e | (?vn. (~(vn IN excset)) /\ senv vn = SOME e)}
`;

val birs_exps_of_senv_thm = store_thm(
   "birs_exps_of_senv_thm", ``
!senv.
  birs_exps_of_senv senv
  =
  birs_exps_of_senv_COMP EMPTY senv
``,
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def, birs_exps_of_senv_def]
);

val birs_exps_of_senv_COMP_thm = store_thm(
   "birs_exps_of_senv_COMP_thm", ``
!sr Pi.
  (!excset. birs_exps_of_senv_COMP excset (K NONE) = EMPTY) /\
  (!excset senv vn sv. birs_exps_of_senv_COMP excset ((vn =+ (SOME sv)) senv) =
    if vn IN excset then
      birs_exps_of_senv_COMP (vn INSERT excset) senv
    else
      sv INSERT (birs_exps_of_senv_COMP (vn INSERT excset) senv)) /\
  (!excset senv vn. birs_exps_of_senv_COMP excset ((vn =+ NONE) senv) = (birs_exps_of_senv_COMP (vn INSERT excset) senv))
``,
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def]
  ) >>

  Cases_on `vn IN excset` >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [EXTENSION] >>
    REPEAT STRIP_TAC >> EQ_TAC >> (
      REPEAT STRIP_TAC >>
      METIS_TAC [combinTheory.APPLY_UPDATE_THM, optionTheory.option_CLAUSES]
    )
  )
);
(* ........................... *)

val birs_symb_symbols_thm = store_thm(
   "birs_symb_symbols_thm", ``
!sys.
  birs_symb_symbols sys = (BIGUNION (IMAGE bir_vars_of_exp (birs_exps_of_senv sys.bsst_environ))) UNION (bir_vars_of_exp sys.bsst_pcond)
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def, IMAGE_DEF, birs_exps_of_senv_def, IN_GSPEC_IFF]
);
(* ........................... *)



val BVarToPair_def = Define `
    BVarToPair (BVar bvn bty) = (bvn, bty)
`;
val PairToBVar_def = Define `
    PairToBVar (bvn, bty) = (BVar bvn bty)
`;
val bir_senv_GEN_bvar_def = Define `
    bir_senv_GEN_bvar (vn,ty) = BVar (CONCAT["sy_";vn]) ty
`;
val bir_senv_GEN_bvar_EQ_thm = store_thm(
   "bir_senv_GEN_bvar_EQ_thm", ``
!x y.
  bir_senv_GEN_bvar x = bir_senv_GEN_bvar y <=> x = y
``,
  Cases_on `x` >> Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_senv_GEN_bvar_def] >>

  ASSUME_TAC (INST_TYPE [Type.alpha |-> Type`:char`] (prove(
    ``!A B C. FLAT [A;B] = FLAT [A;C] <=> B = C``,
      SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.FLAT_compute, listTheory.FLAT]
  ))) >>

  METIS_TAC []
);
(* ........................... *)


val MEM_FST_IMP_MEM_thm = store_thm(
   "MEM_FST_IMP_MEM_thm", ``
!vn l.
  (MEM vn (MAP FST l)) ==>
  (?ty. MEM (vn,ty) l)
``,
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.MEM_MAP] >>
  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [] >>
  METIS_TAC []
);
val NOT_MEM_FST_IMP_thm = store_thm(
   "NOT_MEM_FST_IMP_thm", ``
!vn l.
  (~(MEM vn (MAP FST l))) ==>
  (!e. ~(MEM e l) \/ ~((\(vni,ty). vni = vn) e))
``,
  REPEAT STRIP_TAC >>
  Cases_on `e` >>
  Cases_on `q = vn` >- (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss []
);
(* ........................... *)


val bir_senv_GEN_list_def = Define `
    bir_senv_GEN_list l = FOLDR (\(vn,ty). \f. (vn =+ SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty)))) f) (K NONE) l
`;
(*
("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ))
*)
val bir_senv_GEN_list_NOT_MEM_thm = store_thm(
   "bir_senv_GEN_list_NOT_MEM_thm", ``
!vn l.
  (~(MEM vn (MAP FST l))) ==>
  (bir_senv_GEN_list l vn = NONE)
``,
  Induct_on `l` >- (
    SIMP_TAC std_ss [listTheory.MEM, bir_senv_GEN_list_def, listTheory.FOLDR]
  ) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.MEM] >>
  SIMP_TAC std_ss [bir_senv_GEN_list_def] >>
  FULL_SIMP_TAC std_ss [listTheory.FOLDR] >>
  SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def] >>

  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [pairTheory.FST, combinTheory.APPLY_UPDATE_THM]
);
val bir_senv_GEN_list_APPLY_thm = store_thm(
   "bir_senv_GEN_list_APPLY_thm", ``
!vn ty l.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_senv_GEN_list l vn = SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty))))
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_senv_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_senv_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  `q <> vn` by (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
  SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def] >>
  METIS_TAC []
);

val bir_senv_GEN_list_vars_thm = store_thm(
   "bir_senv_GEN_list_vars_thm", ``
!l.
  (ALL_DISTINCT (MAP FST l)) ==>
  (BIGUNION {bir_vars_of_exp e | (?vn. (bir_senv_GEN_list l) vn = SOME e)} = set (MAP bir_senv_GEN_bvar l))
``,
  Induct_on `l` >- (
    SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [listTheory.MAP, bir_senv_GEN_list_def, listTheory.FOLDR, EXTENSION, listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_senv_GEN_list_def, listTheory.MAP, listTheory.FOLDR] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION, listTheory.LIST_TO_SET_DEF, listTheory.MEM] >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def, listTheory.ALL_DISTINCT, listTheory.MAP] >>

  EQ_TAC >- (
    FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>
    REPEAT STRIP_TAC >>
    Cases_on `q = vn` >- (
      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING]
    ) >>

    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
    `x IN (BIGUNION {bir_vars_of_exp e | (?vn. bir_senv_GEN_list l vn = SOME e)})` by (
      SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      METIS_TAC []
    ) >>

    FULL_SIMP_TAC std_ss [EXTENSION] >>
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>
  REPEAT STRIP_TAC >- (
    Q.EXISTS_TAC `bir_vars_of_exp (BExp_Den (x))` >>
    FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING] >>
    Q.EXISTS_TAC `BExp_Den (x)` >>
    FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING] >>
    FULL_SIMP_TAC std_ss [] >>
    Q.EXISTS_TAC `q` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [EXTENSION] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `x`) >>
  REV_FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  `q <> vn` by (
    METIS_TAC [bir_senv_GEN_list_NOT_MEM_thm, optionTheory.option_CLAUSES]
  ) >>

  METIS_TAC [combinTheory.APPLY_UPDATE_THM]
);
(* ........................... *)


val bir_interpr_GEN_list_def = Define `
    bir_interpr_GEN_list l envf = FOLDR (\(vn,ty). \f. ((bir_senv_GEN_bvar (vn,ty)) =+ envf vn) f) (K NONE) l
`;
(*
  Q.EXISTS_TAC `SymbInterpret
    ((BVar "sy_R7" (BType_Imm Bit32) =+ SOME v_R7)
    ((BVar "sy_SP_process" (BType_Imm Bit32) =+ SOME v_SP_process)
    ((BVar "sy_countw" (BType_Imm Bit64) =+ SOME v_countw) (K NONE))))` >>
*)
val bir_interpr_GEN_list_NOT_MEM_thm = store_thm(
   "bir_interpr_GEN_list_NOT_MEM_thm", ``
!vn ty l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = NONE)
``,
  Induct_on `l` >- (
    SIMP_TAC std_ss [listTheory.MEM, bir_interpr_GEN_list_def, listTheory.FOLDR]
  ) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.MEM] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def] >>
  FULL_SIMP_TAC std_ss [listTheory.FOLDR] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>

  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [pairTheory.FST, combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm]
);
val bir_interpr_GEN_list_APPLY_thm = store_thm(
   "bir_interpr_GEN_list_APPLY_thm", ``
!vn ty l f.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  `q <> vn` by (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>
  METIS_TAC []
);
val bir_interpr_GEN_list_APPLY2_thm = store_thm(
   "bir_interpr_GEN_list_APPLY2_thm", ``
!vn l f.
  (MEM vn (MAP FST l)) ==>
  (?ty. bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM, listTheory.MAP]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  FULL_SIMP_TAC std_ss [] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`vn`, `f`]) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ty` >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>
  METIS_TAC []
);

val bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm = store_thm(
   "bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm", ``
!l f bv.
  (IS_SOME (bir_interpr_GEN_list l f bv)) ==>
  (?vn ty. bv = bir_senv_GEN_bvar (vn, ty) /\ (MEM (vn,ty) l))
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>

  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>

  Cases_on `bir_senv_GEN_bvar (q,r) = bv` >- (
    FULL_SIMP_TAC std_ss [listTheory.MEM] >>
    METIS_TAC [bir_senv_GEN_bvar_EQ_thm]
  ) >>


  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [listTheory.MEM]
);
(* ........................... *)


val bir_envty_list_inclusive_def = Define `
    bir_envty_list_inclusive l env = EVERY (\(vn,ty). ?v. env vn = SOME v /\ type_of_bir_val v = ty) l
`;
val bir_envty_list_exclusive_def = Define `
    bir_envty_list_exclusive l env = (!vn. (~(EXISTS (\(vni,ty). vni = vn) l)) ==> (env vn = NONE))
`;
val bir_envty_list_def = Define `
    bir_envty_list l env = (ALL_DISTINCT (MAP FST l) /\ bir_envty_list_inclusive l env /\ bir_envty_list_exclusive l env)
`;
val bir_envty_list_MEM_IMP_thm = store_thm(
   "bir_envty_list_MEM_IMP_thm", ``
!vn ty l f.
  (MEM (vn,ty) l) ==>
  (bir_envty_list l f) ==>
  (?v. f vn = SOME v /\ type_of_bir_val v = ty)
``,
  REWRITE_TAC [bir_envty_list_def, bir_envty_list_inclusive_def, listTheory.EVERY_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `(vn,ty)`) >>
  FULL_SIMP_TAC std_ss []
);
val bir_envty_list_NOT_MEM_IMP_thm = store_thm(
   "bir_envty_list_NOT_MEM_IMP_thm", ``
!vn l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_envty_list l f) ==>
  (f vn = NONE)
``,
  REWRITE_TAC [bir_envty_list_def, bir_envty_list_exclusive_def, listTheory.EXISTS_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `vn`) >>
  FULL_SIMP_TAC std_ss [boolTheory.NOT_EXISTS_THM, NOT_MEM_FST_IMP_thm]
);

val bir_envty_list_b_def = Define `
    bir_envty_list_b l (BEnv env) = bir_envty_list l env
`;
val bir_envty_list_b_thm = store_thm(
   "bir_envty_list_b_thm", ``
!l env.
  bir_envty_list_b l env = bir_envty_list l (\bvn. bir_env_lookup bvn env)
``,
  REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss) [bir_envty_list_b_def, bir_envTheory.bir_env_lookup_def] >>
  METIS_TAC []
);
(* ........................... *)


val birs_matchenv_bir_senv_GEN_thm = store_thm(
   "birs_matchenv_bir_senv_GEN_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (birs_matchenv (SymbInterpret (bir_interpr_GEN_list l f))
          (bir_senv_GEN_list l) (BEnv f))
``,
  SIMP_TAC std_ss [birs_matchenv_def] >>
  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
  FULL_SIMP_TAC std_ss [bir_envTheory.bir_env_lookup_def] >>

  Cases_on `MEM var (MAP FST l)` >- (
    IMP_RES_TAC MEM_FST_IMP_MEM_thm >>
    IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
    IMP_RES_TAC bir_senv_GEN_list_APPLY_thm >>
    FULL_SIMP_TAC std_ss [] >>

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_get_var_thm, bir_interpr_GEN_list_APPLY_thm]
  ) >>

  IMP_RES_TAC bir_envty_list_NOT_MEM_IMP_thm >>
  IMP_RES_TAC bir_senv_GEN_list_NOT_MEM_thm >>
  FULL_SIMP_TAC std_ss []
);


val symb_interpr_dom_bir_interpr_GEN_list_thm = store_thm(
   "symb_interpr_dom_bir_interpr_GEN_list_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (symb_interpr_dom (SymbInterpret (bir_interpr_GEN_list l f))
   =
   set (MAP bir_senv_GEN_bvar l))
``,
  SIMP_TAC std_ss [symb_interpr_dom_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>

  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC (pure_ss) [GSYM optionTheory.NOT_IS_SOME_EQ_NONE] >>
    FULL_SIMP_TAC (std_ss) [] >>

    METIS_TAC [bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `y` >>

  REV_FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>


  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) []
);

val birs_interpr_welltyped_bir_interpr_GEN_list_thm = store_thm(
   "birs_interpr_welltyped_bir_interpr_GEN_list_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (birs_interpr_welltyped (SymbInterpret (bir_interpr_GEN_list l f)))
``,
  SIMP_TAC std_ss [birs_interpr_welltyped_def, symb_interpr_dom_bir_interpr_GEN_list_thm, symb_interpr_get_def] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>
  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>

  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>

  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_var_type_def, bir_senv_GEN_bvar_def]
);

val symb_interpr_for_symbs_bir_interpr_GEN_list_thm = store_thm(
   "symb_interpr_for_symbs_bir_interpr_GEN_list_thm", ``
!l f lbl status bpre_sv.
  (bir_envty_list l f) ==>
  (bir_vars_of_exp bpre_sv SUBSET (set (MAP bir_senv_GEN_bvar l))) ==>
  (symb_interpr_for_symbs
          (birs_symb_symbols
             <|bsst_pc := lbl; bsst_environ := bir_senv_GEN_list l;
               bsst_status := status; bsst_pcond := bpre_sv|>)
          (SymbInterpret (bir_interpr_GEN_list l f)))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, symb_interpr_dom_bir_interpr_GEN_list_thm] >>
  FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) [birs_symb_symbols_def, UNION_EMPTY] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.SUBSET_DEF] >>

  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
  `MEM vn (MAP FST l)` by (
    CCONTR_TAC >>
    IMP_RES_TAC bir_senv_GEN_list_NOT_MEM_thm >>
    FULL_SIMP_TAC (std_ss) []
  ) >>

  IMP_RES_TAC MEM_FST_IMP_MEM_thm >>
  IMP_RES_TAC bir_senv_GEN_list_APPLY_thm >>
  FULL_SIMP_TAC (std_ss) [] >>

  `x = bir_senv_GEN_bvar (vn,ty)` by (
    PAT_X_ASSUM ``BExp_Den A = B`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss) [IN_SING, bir_typing_expTheory.bir_vars_of_exp_def]
  ) >>

  METIS_TAC [listTheory.MEM_MAP_f]
);

val bir_envty_list_IMP_birs_eval_exp_vars_thm = store_thm(
   "bir_envty_list_IMP_birs_eval_exp_vars_thm", ``
!l bpre bpre_sv ty.
  (ALL_DISTINCT (MAP FST l)) ==>
  (birs_eval_exp bpre (bir_senv_GEN_list l) = SOME (bpre_sv,ty)) ==>
  (bir_vars_of_exp bpre_sv SUBSET set (MAP bir_senv_GEN_bvar l))
``,
  METIS_TAC [bir_symb_soundTheory.birs_eval_exp_IMP_varset_thm, bir_senv_GEN_list_vars_thm]
);

val bir_envty_list_IMP_birs_eval_exp_interpret_thm = store_thm(
   "bir_envty_list_IMP_birs_eval_exp_interpret_thm", ``
!l f e v sv ty.
  (bir_envty_list l f) ==>
  (bir_eval_exp e (BEnv f) = SOME v (*bir_val_true*)) ==>
  (birs_eval_exp e (bir_senv_GEN_list l) = SOME (sv,ty)) ==>
  (birs_interpret_fun (SymbInterpret (bir_interpr_GEN_list l f)) sv = SOME v (*bir_val_true*))
``,
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `env = BEnv f` >>
  Q.ABBREV_TAC `senv = bir_senv_GEN_list l` >>
  Q.ABBREV_TAC `H = SymbInterpret (bir_interpr_GEN_list l f)` >>

  `birs_interpr_welltyped H` by (
    METIS_TAC [birs_interpr_welltyped_bir_interpr_GEN_list_thm]
  ) >>
  `birs_matchenv H senv env` by (
    METIS_TAC [birs_matchenv_bir_senv_GEN_thm]
  ) >>

  IMP_RES_TAC bir_symb_sound_coreTheory.birs_eval_exp_sound_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `e`) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [optionTheory.option_CLAUSES]
);
(* ........................... *)


val bprog_P_entails_gen_thm = store_thm(
   "bprog_P_entails_gen_thm", ``
!lbl status l f bpre bpre_sv ty.
  (bir_envty_list l f) ==>
  (bir_eval_exp bpre (BEnv f) = SOME bir_val_true) ==>
  (birs_eval_exp bpre (bir_senv_GEN_list l) = SOME (bpre_sv,ty)) ==>
  (?H. birs_symb_matchstate
              <|bsst_pc := lbl;
                bsst_environ := bir_senv_GEN_list l;
                bsst_status := status;
                bsst_pcond := bpre_sv |>
              H
              (bir_state_t
                 lbl
                 (BEnv f)
                 status)
  )
``,
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `SymbInterpret (bir_interpr_GEN_list l f)` >>

  `bir_vars_of_exp bpre_sv SUBSET set (MAP bir_senv_GEN_bvar l)` by (
    METIS_TAC [bir_envty_list_IMP_birs_eval_exp_vars_thm, bir_envty_list_def]
  ) >>

  FULL_SIMP_TAC (std_ss) [birs_symb_matchstate_def] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) []
  ) >> (
    ASM_REWRITE_TAC []
  ) >> (
    FULL_SIMP_TAC std_ss [
      birs_matchenv_bir_senv_GEN_thm,
      birs_interpr_welltyped_bir_interpr_GEN_list_thm,
      symb_interpr_for_symbs_bir_interpr_GEN_list_thm]
  ) >>

  METIS_TAC [bir_envty_list_IMP_birs_eval_exp_interpret_thm]
);
(* ........................... *)


val bir_BEnv_lookup_EQ_thm = store_thm(
   "bir_BEnv_lookup_EQ_thm", ``
!env.
  BEnv (λbvn. bir_env_lookup bvn env) = env
``,
  REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss) [bir_envty_list_b_def, bir_envTheory.bir_env_lookup_def] >>
  METIS_TAC []
);




val birs_gen_env_fun_def = Define `
    birs_gen_env_fun (n, sv) env = (n =+ (SOME sv)) env
`;
val birs_gen_env_def = Define `
    birs_gen_env l = FOLDR birs_gen_env_fun (K NONE) l
`;

val birs_gen_env_NULL_thm = store_thm(
   "birs_gen_env_NULL_thm", ``
!n sv l.
    birs_gen_env ([]) = (K NONE)
``,
  cheat
);
val birs_gen_env_thm = store_thm(
   "birs_gen_env_thm", ``
!n sv l.
    birs_gen_env ((n, sv)::l) = (n =+ (SOME sv)) (birs_gen_env l)
``,
  cheat
);

(*
EVAL ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))]``
(REWRITE_CONV [birs_gen_env_thm, birs_gen_env_NULL_thm]) ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))]``
*)

val birs_update_env_thm = store_thm(
   "birs_update_env_thm", ``
!n sv l.
    birs_update_env (n, sv) (birs_gen_env l) = birs_gen_env((n, sv)::(FILTER (\x. (FST x) <> n) l))
``,
  cheat
);

(*
(REWRITE_CONV [birs_update_env_thm] THENC RESTR_EVAL_CONV [``birs_gen_env``])
  ``birs_update_env ("R0", BExp_Const (Imm32 0w)) (birs_gen_env [("R2",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))])``
*)

val birs_gen_env_GET_NULL_thm = store_thm(
   "birs_gen_env_GET_NULL_thm", ``
!m.
    birs_gen_env [] m = NONE
``,
  cheat
);
val birs_gen_env_GET_thm = store_thm(
   "birs_gen_env_GET_thm", ``
!n sv l m.
    birs_gen_env ((n, sv)::l) m = if n = m then SOME sv else birs_gen_env l m
``,
  cheat
);

(*
(REWRITE_CONV [birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm] THENC EVAL) ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))] "R0"``
*)


val _ = export_theory();
