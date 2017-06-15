(* ========================================================================= *)
(* FILE          : bil_mem_expScript.sml                                     *)
(* DESCRIPTION   : A model of bil variable invironments                      *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open finite_mapTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;

val _ = new_theory "bil_env";

val _ = Datatype `bil_var_t = Var string bil_type_t`;

val bil_var_name_def = Define `bil_var_name (Var n _) = n`;
val bil_var_type_def = Define `bil_var_type (Var _ ty) = ty`;

val _ = Datatype `bil_var_environment_t =
    IrregularEnv
  | RegularEnv (string |-> (bil_type_t # (bil_val_t option)))`;


(* Empty environment *)
val empty_env_def = Define `empty_env = RegularEnv FEMPTY`

val is_env_regular_def = Define `
  (is_env_regular IrregularEnv = F) /\
  (is_env_regular (RegularEnv _) = T)`;

val is_valid_env_def = Define `(is_valid_env IrregularEnv = F) /\
  (is_valid_env (RegularEnv m) <=> FEVERY (\ (_, (ty, vo)).
     (case vo of NONE => T | SOME v => (SOME ty = type_of_bil_val v))) m)`;

val is_valid_env_empty = store_thm ("is_valid_env_empty",
  ``is_valid_env empty_env``,
SIMP_TAC std_ss [is_valid_env_def, empty_env_def, finite_mapTheory.FEVERY_FEMPTY]);

val is_env_regular_REWRS = store_thm ("is_env_regular_REWRS",
``!env. is_env_regular env <=> (env <> IrregularEnv)``,
Cases >> SIMP_TAC (srw_ss()) [is_env_regular_def]);

val bil_env_lookup_def = Define `
  (bil_env_lookup varname IrregularEnv = NONE) /\
  (bil_env_lookup varname (RegularEnv env) = FLOOKUP env varname)`;

val bil_env_update_def = Define `
  (bil_env_update varname vo ty IrregularEnv = IrregularEnv) /\
  (bil_env_update varname vo ty (RegularEnv env) =
    if (?v. (vo = SOME v) /\ (SOME ty <> type_of_bil_val v)) then IrregularEnv else
    (RegularEnv (env |+ (varname, (ty, vo)))))`;


val bil_env_lookup_type_def = Define `
  bil_env_lookup_type var_name env = OPTION_MAP FST (bil_env_lookup var_name env)`;

val bil_env_check_type_def = Define `
  bil_env_check_type var env =
    (bil_env_lookup_type (bil_var_name var) env = SOME (bil_var_type var))`


val bil_env_read_def = Define `bil_env_read v env =
  case (bil_env_lookup (bil_var_name v) env) of
     NONE => Unknown
   | SOME (_, NONE) => Unknown
   | SOME (ty, SOME r) => if (ty = bil_var_type v) then r else Unknown`;


val bil_env_write_def = Define `bil_env_write v va env =
  if (bil_env_check_type v env) then bil_env_update (bil_var_name v) (SOME va) (bil_var_type v) env else IrregularEnv`;


val bil_env_write_Irregular = store_thm ("bil_env_write_Irregular",
  ``!v va. (bil_env_write v va IrregularEnv) = IrregularEnv``,
SIMP_TAC std_ss [bil_env_write_def, bil_env_update_def]);


val bil_env_write_Irregular_WrongVal = store_thm ("bil_env_write_Irregular_WrongVal",
  ``!v va env. (type_of_bil_val va <> SOME (bil_var_type v)) ==>
               (bil_env_write v va env = IrregularEnv)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bil_env_write_def, bil_env_check_type_def] >>
COND_CASES_TAC >> REWRITE_TAC[] >>
Cases_on `env` >> SIMP_TAC std_ss [bil_env_update_def])


val is_valid_env_lookup = store_thm ("is_valid_env_lookup",
  ``!env vn ty v. is_valid_env env ==>
                  (bil_env_lookup vn env = SOME (ty, SOME v)) ==>
                  (type_of_bil_val v = SOME ty)``,

Cases >> SIMP_TAC std_ss [is_valid_env_def] >>
rename1 `RegularEnv f` >>
SIMP_TAC (std_ss++QI_ss) [bil_env_lookup_def, finite_mapTheory.FEVERY_ALL_FLOOKUP] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!k. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss []);


val is_valid_env_read = store_thm ("is_valid_env_read",
  ``!env v ty r. is_valid_env env ==>
                 (bil_env_read v env = r) ==>
                 (r <> Unknown) ==>
                 (type_of_bil_val r = SOME (bil_var_type v))``,

SIMP_TAC std_ss [bil_env_read_def] >>
REPEAT GEN_TAC >>
REPEAT CASE_TAC >> FULL_SIMP_TAC std_ss [type_of_bil_val_def, pairTheory.pair_case_thm] >>
METIS_TAC[is_valid_env_lookup]);

val bil_env_read_EQ_Unknown = store_thm ("bil_env_read_EQ_Unknown",
  ``!v env. is_valid_env env ==> (
       (bil_env_read v env = Unknown) <=> (!r. (bil_env_lookup (bil_var_name v) env <> (SOME (bil_var_type v, SOME r)))))``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bil_env_read_def] >>
REPEAT CASE_TAC >>
STRIP_TAC >>
rename1 `r = Unknown` >>
`type_of_bil_val r = SOME (bil_var_type v)` by METIS_TAC[is_valid_env_lookup] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [type_of_bil_val_def]);




val bil_env_varname_is_bound_def = Define `
  (bil_env_varname_is_bound IrregularEnv var = F) /\
  (bil_env_varname_is_bound (RegularEnv env) var = (var IN FDOM env))`;

val bil_env_varname_is_bound_ALT_DEF = store_thm ("bil_env_varname_is_bound_ALT_DEF",
  ``!var env. bil_env_varname_is_bound env var <=> IS_SOME (bil_env_lookup_type var env)``,

Cases_on `env` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bil_env_varname_is_bound_def,
    bil_env_lookup_type_def, bil_env_lookup_def, FLOOKUP_DEF]
));

val bil_env_varname_is_bound_ALT2_DEF = store_thm ("bil_env_varname_is_bound_ALT2_DEF",
  ``!var env. bil_env_varname_is_bound env var <=> IS_SOME (bil_env_lookup var env)``,

SIMP_TAC std_ss [bil_env_varname_is_bound_ALT_DEF, bil_env_lookup_type_def,
  optionTheory.IS_SOME_MAP]);


val bil_env_var_is_declared_def = Define `
  (bil_env_var_is_declared env (Var vn ty) <=>
  (bil_env_lookup_type vn env = SOME ty))`;

val bil_env_var_is_initialised_def = Define `
  (bil_env_var_is_initialised env (Var vn ty) <=>
  (?v. bil_env_lookup vn env = SOME (ty, SOME v)))`;


val bil_env_var_is_initialised_weaken = store_thm ("bil_env_var_is_initialised_weaken",
  ``!v env. bil_env_var_is_initialised env v ==> bil_env_var_is_declared env v``,
Cases >> SIMP_TAC std_ss [bil_env_var_is_initialised_def, bil_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bil_env_lookup_type_def]);


val bil_env_var_is_declared_weaken = store_thm ("bil_env_var_is_declared_weaken",
  ``!v env. bil_env_var_is_declared env v ==> bil_env_varname_is_bound env (bil_var_name v)``,
Cases >> SIMP_TAC std_ss [bil_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bil_env_varname_is_bound_ALT_DEF,
  bil_var_name_def]);


val _ = Datatype `bil_env_cond_t =
  | EnvCond_varname_bound string
  | EnvCond_var_declared bil_var_t
  | EnvCond_var_initialised bil_var_t`;

val bil_env_cond_eval_def = Define `
  (bil_env_cond_eval env (EnvCond_varname_bound vn)  <=> bil_env_varname_is_bound   env vn) /\
  (bil_env_cond_eval env (EnvCond_var_initialised v) <=> bil_env_var_is_initialised env v) /\
  (bil_env_cond_eval env (EnvCond_var_declared v)    <=> bil_env_var_is_declared    env v)`;


val bil_env_order_def = Define `
  ((bil_env_order env1 env2) <=>
     !vn ty vo. (bil_env_lookup vn env1 = SOME (ty, vo)) ==>
                (?vo'. (bil_env_lookup vn env2 = SOME (ty, vo')) /\
                       (IS_SOME vo ==> IS_SOME vo')))`;

val bil_env_order_REFL = store_thm ("bil_env_order_REFL",
  ``!env. bil_env_order env env``,
SIMP_TAC std_ss [bil_env_order_def]);

val bil_env_order_TRANS = store_thm ("bil_env_order_TRANS",
  ``!env1 env2 env3.
       bil_env_order env1 env2 ==> bil_env_order env2 env3 ==>
       bil_env_order env1 env3``,
SIMP_TAC std_ss [bil_env_order_def] >>
METIS_TAC[]);


val bil_env_varname_is_bound_ORDER = store_thm ("bil_env_varname_is_bound_ORDER",
  ``!env1 env2 v. bil_env_order env1 env2 ==>
                  bil_env_varname_is_bound env1 v ==>
                  bil_env_varname_is_bound env2 v``,
SIMP_TAC (std_ss++QI_ss) [bil_env_varname_is_bound_ALT_DEF, bil_env_order_def,
  bil_env_lookup_type_def, optionTheory.IS_SOME_EXISTS] >>
METIS_TAC[]);


val bil_env_var_is_declared_ORDER = store_thm ("bil_env_var_is_declared_ORDER",
  ``!env1 env2 v. bil_env_order env1 env2 ==>
                  bil_env_var_is_declared env1 v ==>
                  bil_env_var_is_declared env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss++QI_ss) [bil_env_var_is_declared_def, bil_env_order_def,
  bil_env_lookup_type_def] >>
METIS_TAC[]);


val bil_env_var_is_initialised_ORDER = store_thm ("bil_env_var_is_initialised_ORDER",
  ``!env1 env2 v. bil_env_order env1 env2 ==>
                  bil_env_var_is_initialised env1 v ==>
                  bil_env_var_is_initialised env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss) [bil_env_var_is_initialised_def, bil_env_order_def,
  optionTheory.IS_SOME_EXISTS] >>
METIS_TAC[]);


val bil_env_cond_eval_ORDER = store_thm ("bil_env_cond_eval_ORDER",
  ``!env1 env2 c. bil_env_order env1 env2 ==>
                  bil_env_cond_eval env1 c ==>
                  bil_env_cond_eval env2 c``,

Cases_on `c` >> (
  SIMP_TAC std_ss [bil_env_cond_eval_def] >>
  METIS_TAC[bil_env_varname_is_bound_ORDER,
            bil_env_var_is_declared_ORDER,
            bil_env_var_is_initialised_ORDER]
));


val bil_env_vars_are_initialised_def = Define `
  bil_env_vars_are_initialised env vs <=>
  (!v. v IN vs ==> bil_env_var_is_initialised env v)`;

val bil_env_vars_are_initialised_EMPTY = store_thm ("bil_env_vars_are_initialised_EMPTY",
  ``!env. bil_env_vars_are_initialised env {}``,
SIMP_TAC std_ss [bil_env_vars_are_initialised_def, pred_setTheory.NOT_IN_EMPTY]);

val bil_env_vars_are_initialised_INSERT = store_thm ("bil_env_vars_are_initialised_INSERT",
  ``!env v vs. bil_env_vars_are_initialised env (v INSERT vs) <=>
               (bil_env_var_is_initialised env v /\ bil_env_vars_are_initialised env vs)``,
SIMP_TAC std_ss [bil_env_vars_are_initialised_def, pred_setTheory.IN_INSERT] >>
METIS_TAC[]);

val bil_env_vars_are_initialised_UNION = store_thm ("bil_env_vars_are_initialised_UNION",
  ``!env vs1 vs2. bil_env_vars_are_initialised env (vs1 UNION vs2) <=>
                  (bil_env_vars_are_initialised env vs1 /\
                   bil_env_vars_are_initialised env vs2) ``,
SIMP_TAC std_ss [bil_env_vars_are_initialised_def, pred_setTheory.IN_UNION] >>
METIS_TAC[]);

val bil_env_vars_are_initialised_SUBSET = store_thm ("bil_env_vars_are_initialised_SUBSET",
  ``!env vs1 vs2. bil_env_vars_are_initialised env vs1 ==>
                  (vs2 SUBSET vs1) ==>
                   bil_env_vars_are_initialised env vs2``,
SIMP_TAC std_ss [bil_env_vars_are_initialised_def, pred_setTheory.SUBSET_DEF] >>
METIS_TAC[]);


val bil_env_vars_are_initialised_ORDER = store_thm ("bil_env_vars_are_initialised_ORDER",
  ``!env1 env2 vs. bil_env_order env1 env2 ==>
                   bil_env_vars_are_initialised env1 vs ==>
                   bil_env_vars_are_initialised env2 vs``,

SIMP_TAC std_ss [bil_env_vars_are_initialised_def] >>
METIS_TAC[bil_env_var_is_initialised_ORDER]);


val bil_env_order_update = store_thm ("bil_env_order_update",
``!env vn vo ty.
    ~(bil_env_varname_is_bound env vn) /\
    (!v. (vo = SOME v) ==> (type_of_bil_val v = SOME ty)) ==>
    bil_env_order env (bil_env_update vn vo ty env)``,

Cases_on `env` >> (
  SIMP_TAC std_ss [bil_env_update_def, bil_env_order_REFL,
    bil_env_varname_is_bound_ALT_DEF]
) >>
REPEAT STRIP_TAC >>
Cases_on `vo` >> (
  FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [
    bil_env_lookup_type_def,
    bil_env_lookup_def, bil_env_order_def,
    finite_mapTheory.FLOOKUP_UPDATE]
));


val bil_env_order_write = store_thm ("bil_env_order_write",
``!env v va.
    is_env_regular (bil_env_write v va env) ==>
    bil_env_order env (bil_env_write v va env)``,

SIMP_TAC std_ss [bil_env_write_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> FULL_SIMP_TAC std_ss [is_env_regular_def] >>
Cases_on `env` >> (
  FULL_SIMP_TAC std_ss [bil_env_update_def, bil_env_order_REFL]
) >>
FULL_SIMP_TAC std_ss [bil_env_check_type_def, bil_env_lookup_type_def] >>
rename1 `SOME (FST xx)` >> Cases_on `xx` >> rename1 `FST (ty, vo)` >>
Cases_on `SOME ty = type_of_bil_val va` >> FULL_SIMP_TAC std_ss [is_env_regular_def] >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [
    bil_env_order_def, bil_env_lookup_def,
    finite_mapTheory.FLOOKUP_UPDATE]
);



val _ = export_theory();
