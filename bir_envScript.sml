open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;

val _ = new_theory "bir_env";

val _ = Datatype `bir_var_t = BVar string bir_type_t`;

val bir_var_name_def = Define `bir_var_name (BVar n _) = n`;
val bir_var_type_def = Define `bir_var_type (BVar _ ty) = ty`;

val _ = Datatype `bir_var_environment_t =
    BEnv_Irregular
  | BEnv_Regular (string |-> (bir_type_t # (bir_val_t option)))`;


(* Empty environment *)
val bir_empty_env_def = Define `bir_empty_env = BEnv_Regular FEMPTY`

val bir_is_regular_env_def = Define `
  (bir_is_regular_env BEnv_Irregular = F) /\
  (bir_is_regular_env (BEnv_Regular _) = T)`;

val bir_is_well_typed_env_def = Define `(bir_is_well_typed_env BEnv_Irregular = F) /\
  (bir_is_well_typed_env (BEnv_Regular m) <=> FEVERY (\ (_, (ty, vo)).
     (case vo of NONE => T | SOME v => (SOME ty = type_of_bir_val v))) m)`;

val bir_is_well_typed_env_empty = store_thm ("bir_is_well_typed_env_empty",
  ``bir_is_well_typed_env bir_empty_env``,
SIMP_TAC std_ss [bir_is_well_typed_env_def, bir_empty_env_def, finite_mapTheory.FEVERY_FEMPTY]);

val bir_is_regular_env_REWRS = store_thm ("bir_is_regular_env_REWRS",
``!env. bir_is_regular_env env <=> (env <> BEnv_Irregular)``,
Cases >> SIMP_TAC (srw_ss()) [bir_is_regular_env_def]);

val bir_env_lookup_def = Define `
  (bir_env_lookup varname BEnv_Irregular = NONE) /\
  (bir_env_lookup varname (BEnv_Regular env) = FLOOKUP env varname)`;

val bir_env_update_def = Define `
  (bir_env_update varname vo ty BEnv_Irregular = BEnv_Irregular) /\
  (bir_env_update varname vo ty (BEnv_Regular env) =
    if (?v. (vo = SOME v) /\ (SOME ty <> type_of_bir_val v)) then BEnv_Irregular else
    (BEnv_Regular (env |+ (varname, (ty, vo)))))`;


val bir_env_lookup_type_def = Define `
  bir_env_lookup_type var_name env = OPTION_MAP FST (bir_env_lookup var_name env)`;

val bir_env_check_type_def = Define `
  bir_env_check_type var env =
    (bir_env_lookup_type (bir_var_name var) env = SOME (bir_var_type var))`;


val bir_env_read_def = Define `bir_env_read v env =
  case (bir_env_lookup (bir_var_name v) env) of
     NONE => BVal_Unknown
   | SOME (_, NONE) => BVal_Unknown
   | SOME (ty, SOME r) => if (ty = bir_var_type v) then r else BVal_Unknown`;


val bir_env_write_def = Define `bir_env_write v va env =
  if (bir_env_check_type v env) then bir_env_update (bir_var_name v) (SOME va) (bir_var_type v) env else BEnv_Irregular`;


val bir_env_write_Irregular = store_thm ("bir_env_write_Irregular",
  ``!v va. (bir_env_write v va BEnv_Irregular) = BEnv_Irregular``,
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def]);


val bir_env_write_Irregular_WrongVal = store_thm ("bir_env_write_Irregular_WrongVal",
  ``!v va env. (type_of_bir_val va <> SOME (bir_var_type v)) ==>
               (bir_env_write v va env = BEnv_Irregular)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_check_type_def] >>
COND_CASES_TAC >> REWRITE_TAC[] >>
Cases_on `env` >> SIMP_TAC std_ss [bir_env_update_def])


val bir_is_well_typed_env_lookup = store_thm ("bir_is_well_typed_env_lookup",
  ``!env vn ty v. bir_is_well_typed_env env ==>
                  (bir_env_lookup vn env = SOME (ty, SOME v)) ==>
                  (type_of_bir_val v = SOME ty)``,

Cases >> SIMP_TAC std_ss [bir_is_well_typed_env_def] >>
rename1 `BEnv_Regular f` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_lookup_def, finite_mapTheory.FEVERY_ALL_FLOOKUP] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!k. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss []);


val bir_is_well_typed_env_read = store_thm ("bir_is_well_typed_env_read",
  ``!env v ty r. bir_is_well_typed_env env ==>
                 (bir_env_read v env = r) ==>
                 (r <> BVal_Unknown) ==>
                 (type_of_bir_val r = SOME (bir_var_type v))``,

SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT GEN_TAC >>
REPEAT CASE_TAC >> FULL_SIMP_TAC std_ss [type_of_bir_val_def, pairTheory.pair_case_thm] >>
METIS_TAC[bir_is_well_typed_env_lookup]);


val bir_env_read_EQ_Unknown = store_thm ("bir_env_read_EQ_Unknown",
  ``!v env. bir_is_well_typed_env env ==> (
       (bir_env_read v env = BVal_Unknown) <=> (!r. (bir_env_lookup (bir_var_name v) env <> (SOME (bir_var_type v, SOME r)))))``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT CASE_TAC >>
STRIP_TAC >>
rename1 `r = BVal_Unknown` >>
`type_of_bir_val r = SOME (bir_var_type v)` by METIS_TAC[bir_is_well_typed_env_lookup] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [type_of_bir_val_def]);




val bir_env_varname_is_bound_def = Define `
  (bir_env_varname_is_bound BEnv_Irregular var = F) /\
  (bir_env_varname_is_bound (BEnv_Regular env) var = (var IN FDOM env))`;

val bir_env_varname_is_bound_ALT_DEF = store_thm ("bir_env_varname_is_bound_ALT_DEF",
  ``!var env. bir_env_varname_is_bound env var <=> IS_SOME (bir_env_lookup_type var env)``,

Cases_on `env` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_varname_is_bound_def,
    bir_env_lookup_type_def, bir_env_lookup_def, FLOOKUP_DEF]
));

val bir_env_varname_is_bound_ALT2_DEF = store_thm ("bir_env_varname_is_bound_ALT2_DEF",
  ``!var env. bir_env_varname_is_bound env var <=> IS_SOME (bir_env_lookup var env)``,

SIMP_TAC std_ss [bir_env_varname_is_bound_ALT_DEF, bir_env_lookup_type_def,
  optionTheory.IS_SOME_MAP]);


val bir_env_var_is_declared_def = Define `
  (bir_env_var_is_declared env (BVar vn ty) <=>
  (bir_env_lookup_type vn env = SOME ty))`;

val bir_env_var_is_initialised_def = Define `
  (bir_env_var_is_initialised env (BVar vn ty) <=>
  (?v. bir_env_lookup vn env = SOME (ty, SOME v)))`;


val bir_env_var_is_initialised_weaken = store_thm ("bir_env_var_is_initialised_weaken",
  ``!v env. bir_env_var_is_initialised env v ==> bir_env_var_is_declared env v``,
Cases >> SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_lookup_type_def]);


val bir_env_var_is_declared_weaken = store_thm ("bir_env_var_is_declared_weaken",
  ``!v env. bir_env_var_is_declared env v ==> bir_env_varname_is_bound env (bir_var_name v)``,
Cases >> SIMP_TAC std_ss [bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_varname_is_bound_ALT_DEF,
  bir_var_name_def]);


val _ = Datatype `bir_env_cond_t =
  | BEnvCond_varname_bound string
  | BEnvCond_var_declared bir_var_t
  | BEnvCond_var_initialised bir_var_t`;

val bir_env_cond_eval_def = Define `
  (bir_env_cond_eval env (BEnvCond_varname_bound vn)  <=> bir_env_varname_is_bound   env vn) /\
  (bir_env_cond_eval env (BEnvCond_var_initialised v) <=> bir_env_var_is_initialised env v) /\
  (bir_env_cond_eval env (BEnvCond_var_declared v)    <=> bir_env_var_is_declared    env v)`;


val bir_env_order_def = Define `
  ((bir_env_order env1 env2) <=>
     !vn ty vo. (bir_env_lookup vn env1 = SOME (ty, vo)) ==>
                (?vo'. (bir_env_lookup vn env2 = SOME (ty, vo')) /\
                       (IS_SOME vo ==> IS_SOME vo')))`;

val bir_env_order_REFL = store_thm ("bir_env_order_REFL",
  ``!env. bir_env_order env env``,
SIMP_TAC std_ss [bir_env_order_def]);

val bir_env_order_TRANS = store_thm ("bir_env_order_TRANS",
  ``!env1 env2 env3.
       bir_env_order env1 env2 ==> bir_env_order env2 env3 ==>
       bir_env_order env1 env3``,
SIMP_TAC std_ss [bir_env_order_def] >>
METIS_TAC[]);


val bir_env_varname_is_bound_ORDER = store_thm ("bir_env_varname_is_bound_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_varname_is_bound env1 v ==>
                  bir_env_varname_is_bound env2 v``,
SIMP_TAC (std_ss++QI_ss) [bir_env_varname_is_bound_ALT_DEF, bir_env_order_def,
  bir_env_lookup_type_def, optionTheory.IS_SOME_EXISTS] >>
METIS_TAC[]);


val bir_env_var_is_declared_ORDER = store_thm ("bir_env_var_is_declared_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_declared env1 v ==>
                  bir_env_var_is_declared env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_var_is_declared_def, bir_env_order_def,
  bir_env_lookup_type_def] >>
METIS_TAC[]);


val bir_env_var_is_initialised_ORDER = store_thm ("bir_env_var_is_initialised_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_initialised env1 v ==>
                  bir_env_var_is_initialised env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss) [bir_env_var_is_initialised_def, bir_env_order_def,
  optionTheory.IS_SOME_EXISTS] >>
METIS_TAC[]);


val bir_env_cond_eval_ORDER = store_thm ("bir_env_cond_eval_ORDER",
  ``!env1 env2 c. bir_env_order env1 env2 ==>
                  bir_env_cond_eval env1 c ==>
                  bir_env_cond_eval env2 c``,

Cases_on `c` >> (
  SIMP_TAC std_ss [bir_env_cond_eval_def] >>
  METIS_TAC[bir_env_varname_is_bound_ORDER,
            bir_env_var_is_declared_ORDER,
            bir_env_var_is_initialised_ORDER]
));


val bir_env_vars_are_initialised_def = Define `
  bir_env_vars_are_initialised env vs <=>
  (!v. v IN vs ==> bir_env_var_is_initialised env v)`;

val bir_env_vars_are_initialised_EMPTY = store_thm ("bir_env_vars_are_initialised_EMPTY",
  ``!env. bir_env_vars_are_initialised env {}``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, pred_setTheory.NOT_IN_EMPTY]);

val bir_env_vars_are_initialised_INSERT = store_thm ("bir_env_vars_are_initialised_INSERT",
  ``!env v vs. bir_env_vars_are_initialised env (v INSERT vs) <=>
               (bir_env_var_is_initialised env v /\ bir_env_vars_are_initialised env vs)``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, pred_setTheory.IN_INSERT] >>
METIS_TAC[]);

val bir_env_vars_are_initialised_UNION = store_thm ("bir_env_vars_are_initialised_UNION",
  ``!env vs1 vs2. bir_env_vars_are_initialised env (vs1 UNION vs2) <=>
                  (bir_env_vars_are_initialised env vs1 /\
                   bir_env_vars_are_initialised env vs2) ``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, pred_setTheory.IN_UNION] >>
METIS_TAC[]);

val bir_env_vars_are_initialised_SUBSET = store_thm ("bir_env_vars_are_initialised_SUBSET",
  ``!env vs1 vs2. bir_env_vars_are_initialised env vs1 ==>
                  (vs2 SUBSET vs1) ==>
                   bir_env_vars_are_initialised env vs2``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, pred_setTheory.SUBSET_DEF] >>
METIS_TAC[]);


val bir_env_vars_are_initialised_ORDER = store_thm ("bir_env_vars_are_initialised_ORDER",
  ``!env1 env2 vs. bir_env_order env1 env2 ==>
                   bir_env_vars_are_initialised env1 vs ==>
                   bir_env_vars_are_initialised env2 vs``,

SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
METIS_TAC[bir_env_var_is_initialised_ORDER]);


val bir_env_order_update = store_thm ("bir_env_order_update",
``!env vn vo ty.
    ~(bir_env_varname_is_bound env vn) /\
    (!v. (vo = SOME v) ==> (type_of_bir_val v = SOME ty)) ==>
    bir_env_order env (bir_env_update vn vo ty env)``,

Cases_on `env` >> (
  SIMP_TAC std_ss [bir_env_update_def, bir_env_order_REFL,
    bir_env_varname_is_bound_ALT_DEF]
) >>
REPEAT STRIP_TAC >>
Cases_on `vo` >> (
  FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [
    bir_env_lookup_type_def,
    bir_env_lookup_def, bir_env_order_def,
    finite_mapTheory.FLOOKUP_UPDATE]
));


val bir_env_order_write = store_thm ("bir_env_order_write",
``!env v va.
    bir_is_regular_env (bir_env_write v va env) ==>
    bir_env_order env (bir_env_write v va env)``,

SIMP_TAC std_ss [bir_env_write_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> FULL_SIMP_TAC std_ss [bir_is_regular_env_def] >>
Cases_on `env` >> (
  FULL_SIMP_TAC std_ss [bir_env_update_def, bir_env_order_REFL]
) >>
FULL_SIMP_TAC std_ss [bir_env_check_type_def, bir_env_lookup_type_def] >>
rename1 `SOME (FST xx)` >> Cases_on `xx` >> rename1 `FST (ty, vo)` >>
Cases_on `SOME ty = type_of_bir_val va` >> FULL_SIMP_TAC std_ss [bir_is_regular_env_def] >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [
    bir_env_order_def, bir_env_lookup_def,
    finite_mapTheory.FLOOKUP_UPDATE]
);



val _ = export_theory();
