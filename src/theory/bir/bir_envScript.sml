open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open combinTheory pred_setTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;

val _ = new_theory "bir_env";

val _ = Datatype `bir_var_t = BVar string bir_type_t`;

val bir_var_name_def = Define `bir_var_name (BVar n _) = n`;
val bir_var_type_def = Define `bir_var_type (BVar _ ty) = ty`;
val bir_var_t_11 = DB.fetch "-" "bir_var_t_11";

val bir_var_eq_EXPAND = store_thm ("bir_var_eq_EXPAND",
  ``!v1 (v2:bir_var_t). (v1 = v2) <=>
                        (bir_var_name v1 = bir_var_name v2) /\
                        (bir_var_type v1 = bir_var_type v2)``,

Cases >> Cases >>
SIMP_TAC std_ss [bir_var_type_def, bir_var_name_def, bir_var_t_11])


val _ = Datatype `bir_var_environment_t = BEnv (string -> (bir_val_t option))`;
val bir_var_environment_t_11 = DB.fetch "-" "bir_var_environment_t_11";

val bir_env_lookup_def = Define `
  (bir_env_lookup varname (BEnv env) = env varname)`;

val bir_env_update_def = Define `
  (bir_env_update varname v (BEnv env) = BEnv ((varname =+ SOME v) env))`;

val bir_env_lookup_UPDATE = store_thm ("bir_env_lookup_UPDATE",
``bir_env_lookup vn (BEnv ((vn' =+ vo) env)) =
   (if (vn' = vn) then vo else bir_env_lookup vn (BEnv env))``,
SIMP_TAC std_ss [bir_env_lookup_def, APPLY_UPDATE_THM]);

val bir_env_lookup_type_def = Define `
  bir_env_lookup_type var_name env = OPTION_MAP type_of_bir_val (bir_env_lookup var_name env)`;


val bir_env_check_type_def = Define `
  bir_env_check_type var env =
    (bir_env_lookup_type (bir_var_name var) env = SOME (bir_var_type var))`;


val bir_env_read_def = Define `bir_env_read var env =
  if (bir_env_check_type var env) then
    (bir_env_lookup (bir_var_name var) env)
  else
    NONE`;


val bir_env_read_UPDATE = store_thm ("bir_env_read_UPDATE",
``bir_env_read var (BEnv ((vn =+ vo) env)) =
   (if (bir_var_name var = vn) then
      (if (OPTION_MAP type_of_bir_val vo) = SOME (bir_var_type var) then
         vo
       else
         NONE)
    else bir_env_read var (BEnv env))``,

SIMP_TAC std_ss [bir_env_read_def, bir_env_lookup_UPDATE,
      bir_env_check_type_def, bir_env_lookup_type_def] >>
Cases_on `bir_var_name var = vn` >> ASM_SIMP_TAC std_ss []);

val bir_env_write_def = Define `bir_env_write var va env =
	 if (bir_env_check_type var env) /\ ((bir_var_type var) = (type_of_bir_val va)) then
	   SOME (bir_env_update (bir_var_name var) va env)
	 else
	   NONE
`;

(* ===================== *)

val bir_env_write_different_type = store_thm ("bir_env_write_different_type",
  ``!v va env. (type_of_bir_val va <> bir_var_type v) ==>
               (bir_env_write v va env = NONE)``,

REPEAT GEN_TAC >> Cases_on `env` >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def]
);

val bir_env_write_types = store_thm ("bir_env_write_types",
``!env env' v va.
    (bir_env_write v va env = SOME env') ==>
    (bir_env_lookup_type (bir_var_name v) env = bir_env_lookup_type (bir_var_name v) env')``,

SIMP_TAC std_ss [bir_env_write_def, bir_env_check_type_def] >>
Cases_on `env` >>
REWRITE_TAC [bir_env_update_def, bir_env_lookup_type_def, bir_env_lookup_type_def, bir_env_lookup_UPDATE] >>
SIMP_TAC std_ss []
);

val bir_env_read_types = store_thm ("bir_env_read_types",
  ``!env v ty r. (bir_env_read v env = r) ==>
                 (r <> NONE) ==>
                 (?va. (r = SOME va) /\ (type_of_bir_val va = bir_var_type v))``,

SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT GEN_TAC >>
Cases_on `env` >>
SIMP_TAC std_ss [bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def] >>
METIS_TAC[bir_env_check_type_def, bir_env_lookup_type_def]
);

(* ===================== *)


val bir_env_read_EQ_lookup_IMPL = store_thm ("bir_env_read_EQ_lookup_IMPL",
``!env1 env2 v.
   (bir_env_lookup (bir_var_name v) env1 = bir_env_lookup (bir_var_name v) env2) ==>
   (bir_env_read v env1 = bir_env_read v env2)``,
SIMP_TAC std_ss [bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def]);


(* ===================== *)

val _ = Datatype `bir_var_environment_typing_t = BEnvTy (string -> (bir_type_t option))`;

val bir_envty_of_env_def = Define `bir_envty_of_env (BEnv env) =
  BEnvTy ((OPTION_MAP type_of_bir_val) o env)
`;

val bir_env_satisfies_envty_def = Define `bir_env_satisfies_envty (BEnv env) (BEnvTy envty) =
  !vn t. (envty vn = SOME t) ==> (?v. (env vn = SOME v) /\ (type_of_bir_val v = t))
`;

val bir_env_satisfies_envty_of_env = store_thm("bir_env_satisfies_envty_of_env", ``
  !env. bir_env_satisfies_envty env (bir_envty_of_env env)
``,
  Cases_on `env` >>
  SIMP_TAC std_ss [bir_env_satisfies_envty_def, bir_envty_of_env_def] >>
  METIS_TAC[]
);

val bir_envty_includes_v_def = Define `bir_envty_includes_v (BEnvTy envty) v =
  (envty (bir_var_name v) = SOME (bir_var_type v))
`;

val bir_envty_includes_vs_def = Define `bir_envty_includes_vs envty vs =
  (!v. (v IN vs) ==> (bir_envty_includes_v envty v))
`;

val bir_v_in_envty_env_IMP = store_thm("bir_v_in_envty_env_IMP", ``
  !envty env v. (bir_envty_includes_v envty v) ==>
             (bir_env_satisfies_envty env envty) ==>
             (?va. (bir_env_read v env = SOME va) /\ (type_of_bir_val va = bir_var_type v))
``,
  Cases_on `envty` >> Cases_on `env` >>
  FULL_SIMP_TAC std_ss [bir_envty_includes_v_def, bir_env_satisfies_envty_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def] >>
  METIS_TAC []
);

val bir_vs_in_envty_env_IMP = store_thm("bir_vs_in_envty_env_IMP", ``
  !envty env vs. (bir_envty_includes_vs envty vs) ==>
             (bir_env_satisfies_envty env envty) ==>
             !v. (v IN vs) ==>
                 (?va. (bir_env_read v env = SOME va) /\ (type_of_bir_val va = bir_var_type v))
``,
  METIS_TAC [bir_envty_includes_vs_def, bir_v_in_envty_env_IMP]
);


val bir_vs_consistent_def = Define `bir_vs_consistent vs =
  !v1 v2. (v1 IN vs) ==> (v2 IN vs) ==> ((bir_var_name v1) = (bir_var_name v2)) ==> (v1 = v2)
`;

val bir_envty_includes_vs_IMP_vs_consistent = store_thm("bir_envty_includes_vs_IMP_vs_consistent", ``
  !envty vs. (bir_envty_includes_vs envty vs) ==>
             (bir_vs_consistent vs)
``,
  Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, bir_envty_includes_v_def, bir_vs_consistent_def] >>
  REPEAT STRIP_TAC >>
  PAT_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `v1`)) >>
  PAT_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `v2`)) >>
  Cases_on `v1` >> Cases_on `v2` >>
  SIMP_TAC std_ss [bir_var_eq_EXPAND, bir_var_name_def, bir_var_type_def] >>
  Cases_on `s <> s'` >- (
    METIS_TAC[bir_var_name_def]
  ) >>
  FULL_SIMP_TAC std_ss [bir_var_name_def, bir_var_type_def] >>
  REV_FULL_SIMP_TAC std_ss []
);

val bir_envty_includes_vs_EMPTY = store_thm("bir_envty_includes_vs_EMPTY", ``
  !envty. (bir_envty_includes_vs envty EMPTY)
``,
  Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, bir_envty_includes_v_def, NOT_IN_EMPTY]
);

val bir_envty_includes_vs_INSERT = store_thm("bir_envty_includes_vs_INSERT", ``
  !envty v vs. (bir_envty_includes_vs envty (v INSERT vs)) <=>
               ((bir_envty_includes_v envty v) /\ (bir_envty_includes_vs envty vs))
``,
  Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, IN_INSERT] >>
  METIS_TAC[]
);

val bir_envty_includes_vs_UNION = store_thm("bir_envty_includes_vs_UNION", ``
  !envty vs1 vs2. (bir_envty_includes_vs envty (vs1 UNION vs2)) <=>
                  ((bir_envty_includes_vs envty vs1) /\ (bir_envty_includes_vs envty vs2))
``,
  Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, IN_UNION] >>
  METIS_TAC[]
);

val bir_envty_includes_vs_SUBSET = store_thm("bir_envty_includes_vs_SUBSET", ``
  !envty vs1 vs2. (bir_envty_includes_vs envty vs1) ==>
                  (vs2 SUBSET vs1) ==>
                  (bir_envty_includes_vs envty vs2)
``,
  Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, SUBSET_DEF] >>
  METIS_TAC[]
);





(* ===================== *)
(*
bir_vs_consistent!!!

val bir_var_set_is_well_typed_def = Define `bir_var_set_is_well_typed vs <=>
  (!v1 v2. (v1 IN vs /\ v2 IN vs /\ (bir_var_name v1 = bir_var_name v2)) ==>
           (bir_var_type v1 = bir_var_type v2))`;

val bir_var_set_is_well_typed_INJ_DEF = store_thm ("bir_var_set_is_well_typed_INJ_DEF",
  ``bir_var_set_is_well_typed vs <=> INJ bir_var_name vs UNIV``,

SIMP_TAC std_ss [bir_var_set_is_well_typed_def, INJ_DEF, IN_UNIV,
  bir_var_eq_EXPAND] >>
METIS_TAC[]);

val bir_var_set_is_well_typed_EMPTY = store_thm ("bir_var_set_is_well_typed_EMPTY",
  ``bir_var_set_is_well_typed {}``,
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, NOT_IN_EMPTY]);

val bir_var_set_is_well_typed_INSERT = store_thm ("bir_var_set_is_well_typed_INSERT",
  ``!v vs. bir_var_set_is_well_typed (v INSERT vs) <=>
           bir_var_set_is_well_typed vs /\
           (!v'. v' IN vs ==>
                 (bir_var_name v = bir_var_name v') ==>
                 (bir_var_type v = bir_var_type v'))``,

SIMP_TAC std_ss [bir_var_set_is_well_typed_def, IN_INSERT] >>
METIS_TAC[]);


val bir_var_set_is_well_typed_UNION = store_thm ("bir_var_set_is_well_typed_UNION",
``!vs1 vs2. bir_var_set_is_well_typed (vs1 UNION vs2) <=>
            bir_var_set_is_well_typed vs1 /\
            bir_var_set_is_well_typed vs2 /\
            (!v1 v2. v1 IN vs1 ==> v2 IN vs2 ==>
                 (bir_var_name v1 = bir_var_name v2) ==>
                 (bir_var_type v1 = bir_var_type v2))``,

SIMP_TAC std_ss [bir_var_set_is_well_typed_def, IN_UNION] >>
METIS_TAC[]);


val bir_var_set_is_well_typed_SUBSET = store_thm ("bir_var_set_is_well_typed_SUBSET",
  ``!vs1 vs2. vs1 SUBSET vs2 ==> bir_var_set_is_well_typed vs2 ==> bir_var_set_is_well_typed vs1``,
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, SUBSET_DEF] >>
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
  FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_var_type_def, bir_var_name_def] >>
  FULL_SIMP_TAC std_ss []
);


val bir_env_vars_are_initialised_SUBSET_DOMAIN = store_thm ("bir_env_vars_are_initialised_SUBSET_DOMAIN",
  ``!vs env. bir_env_vars_are_initialised env vs ==>
             (IMAGE bir_var_name vs) SUBSET (bir_env_domain env)``,

REPEAT STRIP_TAC >>
Cases_on `env` >> rename1 `BEnv env` >>
FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def, SUBSET_DEF, IN_IMAGE,
  PULL_EXISTS, bir_env_domain_def] >>
REPEAT STRIP_TAC >>
rename1 `v IN vs` >>
Q.PAT_X_ASSUM `!v. _` (MP_TAC o Q.SPEC `v`) >>
Cases_on `v` >> rename1 `BVar vn vty` >>
ASM_SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_lookup_def,
    flookup_thm, PULL_EXISTS, bir_var_name_def]);


val VAR_SET_FINITE_IFF_NAME_SET_FINITE = store_thm ("VAR_SET_FINITE_IFF_NAME_SET_FINITE",
``!vs. FINITE vs <=> FINITE (IMAGE bir_var_name vs)``,

GEN_TAC >> EQ_TAC >- (
  METIS_TAC[IMAGE_FINITE]
) >>
STRIP_TAC >>
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


val bir_env_vars_are_initialised_FINITE = store_thm ("bir_env_vars_are_initialised_FINITE",
  ``!vs env. bir_env_vars_are_initialised env vs ==> FINITE vs``,

METIS_TAC[bir_env_vars_are_initialised_SUBSET_DOMAIN, bir_env_domain_FINITE,
          VAR_SET_FINITE_IFF_NAME_SET_FINITE, SUBSET_FINITE]);



val bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION = store_thm ("bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION",
  ``!vs1 vs2 env1.
      (FINITE vs2 /\ vs1 SUBSET vs2 /\ bir_var_set_is_well_typed vs2) ==>
      bir_env_vars_are_initialised env1 vs1 ==>
      (?env2. bir_env_EQ_FOR_VARS vs1 env1 env2 /\
              bir_env_vars_are_initialised env2 vs2)``,

REPEAT STRIP_TAC >>
Cases_on `env1` >> rename1 `BEnv env` >>
Q.ABBREV_TAC `VF = (\v. (bir_var_type v, SOME (bir_default_value_of_type (bir_var_type v))))` >>
Q.ABBREV_TAC `M1 = FUN_FMAP VF (vs2 DIFF vs1)` >>
EXISTS_TAC ``BEnv (FUNION (MAP_KEYS bir_var_name M1) env)`` >>

`FDOM M1 = vs2 DIFF vs1` by METIS_TAC[FDOM_FMAP, FINITE_DIFF] >>
`INJ bir_var_name (FDOM M1) UNIV` by METIS_TAC [bir_var_set_is_well_typed_INJ_DEF,
  INJ_SUBSET, SUBSET_REFL, DIFF_SUBSET] >>

`!v v'. v IN vs2 ==> (
    ((bir_var_name v = bir_var_name v') /\ v' IN (vs2 DIFF vs1)) <=>
    (~(v IN vs1) /\ (v' = v)))` by (

  SIMP_TAC std_ss [IN_DIFF] >> REPEAT STRIP_TAC >>
  METIS_TAC[bir_var_set_is_well_typed_def, SUBSET_DEF, bir_var_eq_EXPAND]
) >>

REPEAT STRIP_TAC >- (
  SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >>
  REPEAT STRIP_TAC >>
  `v IN vs2` by METIS_TAC[SUBSET_DEF] >>
  ASM_SIMP_TAC std_ss [bir_env_lookup_def, FLOOKUP_FUNION, FLOOKUP_MAP_KEYS]
) >>

FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def]  >>
Cases >> rename1 `BVar vn vty` >>
STRIP_TAC >>
REPEAT (Q.PAT_X_ASSUM `!v. _` (MP_TAC o Q.SPEC `BVar vn vty`)) >>
FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def,
  bir_env_lookup_def, FLOOKUP_MAP_KEYS,
  FLOOKUP_FUNION, bir_var_name_def] >>
Cases_on `BVar vn vty IN vs1` >- (
  ASM_SIMP_TAC std_ss []
) >>
Q.UNABBREV_TAC `M1` >>
Q.UNABBREV_TAC `VF` >>
ASM_SIMP_TAC std_ss [FLOOKUP_FUN_FMAP, FINITE_DIFF,
  bir_default_value_of_type_SPEC, bir_var_type_def, IN_DIFF]);



val bir_env_vars_are_initialised_ENV_EXISTS_IFF = store_thm ("bir_env_vars_are_initialised_ENV_EXISTS_IFF",
  ``!vs. (?env. bir_env_vars_are_initialised env vs) <=> (FINITE vs /\ bir_var_set_is_well_typed vs)``,

GEN_TAC >> EQ_TAC >- (
  METIS_TAC[bir_env_vars_are_initialised_WELL_TYPED, bir_env_vars_are_initialised_FINITE]
) >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`{}`, `vs`, `bir_empty_env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [EMPTY_SUBSET, bir_env_vars_are_initialised_EMPTY, NOT_IN_EMPTY,
  bir_env_EQ_FOR_VARS_EMPTY]);

*)


(* ===================== *)


(* Equivalence for sets of vars *)
val bir_env_EQ_FOR_VARS_def = Define `
  bir_env_EQ_FOR_VARS vs env1 env2 <=>
  (!v. v IN vs ==> (bir_env_lookup (bir_var_name v) env1 = bir_env_lookup (bir_var_name v) env2))`

val bir_env_EQ_FOR_VARS_EQUIV_EQ = store_thm ("bir_env_EQ_FOR_VARS_EQUIV_EQ",
  ``!vs env1 env2. (bir_env_EQ_FOR_VARS vs env1 env2) <=>
                   (bir_env_EQ_FOR_VARS vs env1 = bir_env_EQ_FOR_VARS vs env2)``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, FUN_EQ_THM] >>
METIS_TAC[]);


val bir_env_EQ_FOR_VARS_EQUIV = store_thm ("bir_env_EQ_FOR_VARS_EQUIV",
 ``(!vs env. bir_env_EQ_FOR_VARS vs env env) /\
   (!vs env1 env2. (bir_env_EQ_FOR_VARS vs env1 env2 <=> (bir_env_EQ_FOR_VARS vs env2 env1))) /\
   (!vs env1 env2 env3. bir_env_EQ_FOR_VARS vs env1 env2 ==>
                        bir_env_EQ_FOR_VARS vs env2 env3 ==>
                        bir_env_EQ_FOR_VARS vs env1 env3)``,
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >> METIS_TAC[]);



val bir_env_EQ_FOR_VARS_EMPTY = store_thm ("bir_env_EQ_FOR_VARS_EMPTY",
  ``!env1 env2. bir_env_EQ_FOR_VARS EMPTY env1 env2``,
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, NOT_IN_EMPTY, bir_env_EQ_FOR_VARS_def]);


val bir_env_EQ_FOR_VARS_UNIV = store_thm ("bir_env_EQ_FOR_VARS_UNIV",
  ``!env1 env2. bir_env_EQ_FOR_VARS UNIV env1 env2 <=> (env1 = env2)``,
REPEAT Cases >>
SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_var_t``]) [
  bir_env_EQ_FOR_VARS_def, IN_UNIV,
  bir_var_environment_t_11, bir_env_lookup_def, bir_var_name_def, FUN_EQ_THM]);


val bir_env_EQ_FOR_VARS_SUBSET = store_thm ("bir_env_EQ_FOR_VARS_SUBSET",
  ``!vs1 vs2 env1 env2. vs2 SUBSET vs1 ==> bir_env_EQ_FOR_VARS vs1 env1 env2 ==> bir_env_EQ_FOR_VARS vs2 env1 env2``,
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, SUBSET_DEF] >>
METIS_TAC[]);


val bir_env_EQ_FOR_VARS_read_IMPL = store_thm ("bir_env_EQ_FOR_VARS_read_IMPL",
``!vs env1 env2. bir_env_EQ_FOR_VARS vs env1 env2 ==>
  (!v. v IN vs ==> (bir_env_read v env1 = bir_env_read v env2))``,
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >>
METIS_TAC[bir_env_read_EQ_lookup_IMPL]);


val _ = export_theory();
