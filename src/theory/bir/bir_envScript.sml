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
SIMP_TAC std_ss [bir_var_type_def, bir_var_name_def, bir_var_t_11]
);


val _ = Datatype `bir_var_environment_t =
   BEnv (string -> (bir_val_k_t))`;
val bir_var_environment_t_11 = DB.fetch "-" "bir_var_environment_t_11";

(* Empty environment *)
(* TODO: What now? *)
(*
val bir_empty_env_def = Define `bir_empty_env = BEnv FEMPTY`
*)
(* Deprecated
val bir_is_well_typed_env_def = Define `
  (bir_is_well_typed_env (BEnv m) <=> FEVERY (\ (_, (ty, vo)).
     (case vo of NONE => T | SOME v => (SOME ty = type_of_bir_val v))) m)`;
*)
(* Deprecated
val bir_is_well_typed_env_empty = store_thm ("bir_is_well_typed_env_empty",
  ``bir_is_well_typed_env bir_empty_env``,
SIMP_TAC std_ss [bir_is_well_typed_env_def, bir_empty_env_def, FEVERY_FEMPTY]);
*)

val bir_env_lookup_def = Define `
  (bir_env_lookup varname (BEnv env) = env varname)`;

val bir_env_update_def = Define `
  (bir_env_update varname vo ty (BEnv env) =
    if (ty <> type_of_bir_kval vo)
    then NONE
    else SOME (BEnv ((varname =+ vo) env))
  )`;

val bir_env_lookup_UPDATE = store_thm ("bir_env_lookup_UPDATE",
``!vn vn' vo env.
  bir_env_lookup vn (BEnv ((vn' =+ vo) env)) =
   (if (vn' = vn)
    then vo
    else bir_env_lookup vn (BEnv env))``,

SIMP_TAC std_ss [bir_env_lookup_def, UPDATE_def]
);

(* Note: After introduction of the total map, this now checks the
 *       type of the value stored using type_of_bir_kval, instead of
 *       checking the type stored in the tuple.
 *       An alternative could be to do no checking at all. *)
val bir_env_lookup_type_def = Define `
  bir_env_lookup_type var_name env =
    type_of_bir_kval (bir_env_lookup var_name env)`;


val bir_env_check_type_def = Define `
  bir_env_check_type var env =
    (bir_env_lookup_type (bir_var_name var) env =
      bir_var_type var
    )`;


val bir_env_read_def = Define `bir_env_read v env =
  bir_env_lookup (bir_var_name v) env`;

(* TODO: This checks the type of the stored value - if types do
 *       not agree, then keep on checking. *)
val bir_env_read_UPDATE = store_thm ("bir_env_read_UPDATE",
``!v vn vo env.
  bir_env_read v (BEnv ((vn =+ vo) env)) =
   (if (bir_var_name v = vn) then (
      if (type_of_bir_kval vo = bir_var_type v) then
         vo
      else bir_env_read v (BEnv env))
 else bir_env_read v (BEnv env))``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_env_read_def, bir_env_lookup_UPDATE] >>
Cases_on `bir_var_name v = vn` >> ASM_SIMP_TAC std_ss [] >>
Cases_on `vo` >> SIMP_TAC std_ss [pairTheory.pair_case_thm]
);

val bir_env_read_NEQ_UNKNOWN = store_thm ("bir_env_read_NEQ_UNKNOWN",
``!var env v.
(v <> BVal_Unknown) ==>
((bir_env_read var env = v) <=> (bir_env_lookup (bir_var_name var) env = SOME (bir_var_type var, SOME v)))``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT CASE_TAC);

val bir_env_write_def = Define `bir_env_write v va env =
  if (bir_env_check_type v env)
  then bir_env_update (bir_var_name v) va (bir_var_type v) env
  else NONE`;


val bir_env_write_WrongVal = store_thm ("bir_env_write_WrongVal",
  ``!v va env. (type_of_bir_kval va <> SOME (bir_var_type v)) ==>
               (bir_env_write v va env = NONE)``,

REPEAT GEN_TAC >> Cases_on `env` >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_check_type_def,
  bir_env_update_def]);

val bir_env_update_is_well_typed_env = store_thm ("bir_env_update_is_well_typed_env",
``!env env' varname vo ty.
    (bir_is_well_typed_env env /\
    (bir_env_update varname vo ty env = SOME env')) ==>
    bir_is_well_typed_env env'``,

Cases >>
SIMP_TAC std_ss [bir_env_update_def, bir_is_well_typed_env_def] >>
REPEAT STRIP_TAC >>
ConseqConv.CONSEQ_REWRITE_TAC ([FEVERY_STRENGTHEN_THM], [], []) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `vo` >> (
  FULL_SIMP_TAC std_ss []
));

val bir_env_write_is_well_typed_env = store_thm ("bir_env_write_is_well_typed_env",
``!env env' v va.
    (bir_is_well_typed_env env /\
    (bir_env_write v va env = SOME env')) ==>
    bir_is_well_typed_env env'``,

SIMP_TAC std_ss [bir_env_write_def] >>
METIS_TAC[bir_env_update_is_well_typed_env]);


val bir_is_well_typed_env_lookup = store_thm ("bir_is_well_typed_env_lookup",
  ``!env vn ty v. bir_is_well_typed_env env ==>
                  (bir_env_lookup vn env = SOME (ty, SOME v)) ==>
                  (type_of_bir_val v = SOME ty)``,

Cases >> SIMP_TAC std_ss [bir_is_well_typed_env_def] >>
rename1 `BEnv f` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_lookup_def, FEVERY_ALL_FLOOKUP] >>
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
  (bir_env_varname_is_bound (BEnv env) var = (var IN FDOM env))`;

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
  (bir_env_var_is_declared env v <=>
  (bir_env_lookup_type (bir_var_name v) env = SOME (bir_var_type v)))`;

(* This duplication is kept deliberately, because despite the same semantics, the intentention
   of what you want to express is different *)
val bir_env_var_is_declared_DEF_bir_env_check_type = store_thm ("bir_env_var_is_declared_ALT_DEF",
  ``bir_env_var_is_declared env v = bir_env_check_type v env``,
SIMP_TAC std_ss [bir_env_check_type_def, bir_env_var_is_declared_def]);


val bir_env_var_is_initialised_def = Define `
  (bir_env_var_is_initialised env var <=>
  (?v. (bir_env_lookup (bir_var_name var) env = SOME (bir_var_type var, SOME v)) /\
       (type_of_bir_val v = SOME (bir_var_type var))))`;

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
  (bir_env_order env1 env2) <=> !vn. (
     (* new vars can be added and initialised, but only of the correct type *)
     (!ty v. (bir_env_lookup vn env1 = NONE) ==>
             (bir_env_lookup vn env2 = SOME (ty, SOME v)) ==>
             (type_of_bir_val v = SOME ty)) /\

     (* existing vars can be initialised with the right type *)
     (!ty. (bir_env_lookup vn env1 = SOME (ty, NONE)) ==>
           (?vo. (bir_env_lookup vn env2 = SOME (ty, vo)) /\
                 (!v. (vo = SOME v) ==> (type_of_bir_val v = SOME ty)))) /\

     (* The value of existing, already initialised vars can change, but if
        their type was OK, it stays OK. *)
     (!ty v. (bir_env_lookup vn env1 = SOME (ty, SOME v)) ==>
             (?v'. (bir_env_lookup vn env2 = SOME (ty, SOME v')) /\
                   ((type_of_bir_val v = SOME ty) ==>
                    (type_of_bir_val v' = SOME ty)))))`;


val bir_env_order_REFL = store_thm ("bir_env_order_REFL",
  ``!env. bir_env_order env env``,
SIMP_TAC std_ss [bir_env_order_def]);


val bir_env_order_TRANS = store_thm ("bir_env_order_TRANS",
  ``!env1 env2 env3.
       bir_env_order env1 env2 ==> bir_env_order env2 env3 ==>
       bir_env_order env1 env3``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_order_def] >>
GEN_TAC >>
REPEAT (Q.PAT_X_ASSUM `!vn. P vn` (MP_TAC o Q.SPEC `vn`)) >>
REPEAT STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> REV_FULL_SIMP_TAC std_ss [] >- (
  Cases_on `bir_env_lookup vn env2` >> FULL_SIMP_TAC std_ss [] >>
  rename1 `bir_env_lookup _ _ = SOME xx` >>
  Cases_on `xx` >> FULL_SIMP_TAC std_ss [] >>
  rename1 `bir_env_lookup _ _ = SOME (ty', vo')` >>
  Cases_on `vo'` >> FULL_SIMP_TAC std_ss []
) >- (
  Cases_on `vo` >> FULL_SIMP_TAC std_ss []
));


val bir_env_varname_is_bound_ORDER = store_thm ("bir_env_varname_is_bound_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_varname_is_bound env1 v ==>
                  bir_env_varname_is_bound env2 v``,
SIMP_TAC (std_ss++QI_ss) [bir_env_varname_is_bound_ALT_DEF, bir_env_order_def,
  bir_env_lookup_type_def, optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME (ty, vo)` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `vo` >> (
  SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM]
));


val bir_env_var_is_declared_ORDER = store_thm ("bir_env_var_is_declared_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_declared env1 v ==>
                  bir_env_var_is_declared env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_var_is_declared_def, bir_env_order_def,
  bir_env_lookup_type_def] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME (ty, vo)` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `vo` >> (
  SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM]
));


val bir_env_var_is_initialised_ORDER = store_thm ("bir_env_var_is_initialised_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_initialised env1 v ==>
                  bir_env_var_is_initialised env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss) [bir_env_var_is_initialised_def, bir_env_order_def,
  optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME (ty, SOME v)` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
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
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, NOT_IN_EMPTY]);

val bir_env_vars_are_initialised_INSERT = store_thm ("bir_env_vars_are_initialised_INSERT",
  ``!env v vs. bir_env_vars_are_initialised env (v INSERT vs) <=>
               (bir_env_var_is_initialised env v /\ bir_env_vars_are_initialised env vs)``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, IN_INSERT] >>
METIS_TAC[]);

val bir_env_vars_are_initialised_UNION = store_thm ("bir_env_vars_are_initialised_UNION",
  ``!env vs1 vs2. bir_env_vars_are_initialised env (vs1 UNION vs2) <=>
                  (bir_env_vars_are_initialised env vs1 /\
                   bir_env_vars_are_initialised env vs2) ``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, IN_UNION] >>
METIS_TAC[]);

val bir_env_vars_are_initialised_SUBSET = store_thm ("bir_env_vars_are_initialised_SUBSET",
  ``!env vs1 vs2. bir_env_vars_are_initialised env vs1 ==>
                  (vs2 SUBSET vs1) ==>
                   bir_env_vars_are_initialised env vs2``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_def, SUBSET_DEF] >>
METIS_TAC[]);


val bir_env_vars_are_initialised_ORDER = store_thm ("bir_env_vars_are_initialised_ORDER",
  ``!env1 env2 vs. bir_env_order env1 env2 ==>
                   bir_env_vars_are_initialised env1 vs ==>
                   bir_env_vars_are_initialised env2 vs``,

SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
METIS_TAC[bir_env_var_is_initialised_ORDER]);


val bir_env_order_update = store_thm ("bir_env_order_update",
``!env env' vn vo ty.
    ~(bir_env_varname_is_bound env vn) /\
    (bir_env_update vn vo ty env = SOME env') ==>
    bir_env_order env env'``,

Cases_on `env` >>
SIMP_TAC std_ss [bir_env_update_def, bir_env_varname_is_bound_ALT_DEF] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++QI_ss) [
  bir_env_lookup_type_def,
  bir_env_lookup_def, bir_env_order_def,
  FLOOKUP_UPDATE] >>
METIS_TAC[]);


val bir_env_order_write = store_thm ("bir_env_order_write",
``!env env' v va.
    (bir_env_write v va env = SOME env') ==>
    bir_env_order env env'``,

Cases >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_write_def, bir_env_update_def,
  bir_env_order_def, FLOOKUP_UPDATE, bir_env_lookup_def,
  bir_env_check_type_def, bir_env_lookup_type_def,
  PULL_EXISTS] >>
SIMP_TAC (std_ss++QI_ss) []);


val bir_env_order_well_typed = store_thm ("bir_env_order_well_typed",
``!env env'. bir_is_well_typed_env env ==>
             bir_env_order env env' ==>
             bir_is_well_typed_env env'``,

Cases >> Cases >>
rename1 `bir_env_order (BEnv env_f) (BEnv env_f')` >>
SIMP_TAC (std_ss++QI_ss) [bir_is_well_typed_env_def,
  bir_env_order_def, bir_env_lookup_def, PULL_FORALL, PULL_EXISTS,
  FEVERY_ALL_FLOOKUP] >>
REPEAT STRIP_TAC >>
rename1 `FLOOKUP env_f' vn = SOME (ty, vo)` >>
REPEAT (Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`)) >>
Cases_on `vo` >> SIMP_TAC std_ss [] >>
rename1 `FLOOKUP env_f' vn = SOME (ty, SOME v')` >>
ASM_SIMP_TAC std_ss [FORALL_AND_THM] >>
Cases_on `FLOOKUP env_f vn` >- (
  SIMP_TAC std_ss []
) >>
rename1 `FLOOKUP env_f vn = SOME (XXX)` >> Cases_on `XXX` >>
rename1 `FLOOKUP env_f vn = SOME (ty', vo)` >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `vo` >> SIMP_TAC std_ss []);



(* domains *)

val bir_env_domain_def = Define `bir_env_domain (BEnv env) = FDOM env`;

val bir_env_domain_FINITE = store_thm ("bir_env_domain_FINITE",
``!env. FINITE (bir_env_domain env)``,
Cases >>
SIMP_TAC std_ss [bir_env_domain_def, FDOM_FINITE])


val bir_env_domain_LOOKUP = store_thm ("bir_env_domain_LOOKUP",
``!env vn. (vn IN (bir_env_domain env)) <=> IS_SOME (bir_env_lookup vn env)``,

Cases >> GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_domain_def, bir_env_lookup_def, FLOOKUP_DEF]);



(* subenvironments *)
val bir_is_subenv_def = Define `bir_is_subenv (BEnv env1) (BEnv env2) <=> (env1 SUBMAP env2)`;

val bir_is_subenv_EMPTY = store_thm ("bir_is_subenv_EMPTY",
``!env. bir_is_subenv bir_empty_env env``,
Cases >> SIMP_TAC std_ss [bir_is_subenv_def, bir_empty_env_def, SUBMAP_FEMPTY]);


val bir_is_subenv_REFL = store_thm ("bir_is_subenv_REFL",
  ``!env. bir_is_subenv env env``,
Cases >> SIMP_TAC std_ss [bir_is_subenv_def, SUBMAP_REFL]);

val bir_is_subenv_TRANS = store_thm ("bir_is_subenv_TRANS",
  ``!env1 env2 env3. bir_is_subenv env1 env2 ==> bir_is_subenv env2 env3 ==> bir_is_subenv env1 env3``,
REPEAT Cases >>
SIMP_TAC std_ss [bir_is_subenv_def] >>
METIS_TAC[SUBMAP_TRANS]);


val bir_is_subenv_ANTISYM = store_thm ("bir_is_subenv_ANTISYM",
  ``!env1 env2. (bir_is_subenv env1 env2 /\ bir_is_subenv env2 env1) <=> (env1 = env2)``,

REPEAT Cases >>
SIMP_TAC std_ss [bir_is_subenv_def, bir_var_environment_t_11] >>
METIS_TAC[SUBMAP_ANTISYM]);


val bir_is_subenv_domains = store_thm ("bir_is_subenv_domains",
``!env1 env2. bir_is_subenv env1 env2 ==> (bir_env_domain env1 SUBSET bir_env_domain env2)``,
REPEAT Cases >>
SIMP_TAC std_ss [bir_is_subenv_def, bir_env_domain_def, SUBMAP_DEF, SUBSET_DEF]);



val bir_is_subenv_LOOKUP = store_thm ("bir_is_subenv_LOOKUP",
  ``!env1 env2 vn.
       bir_is_subenv env1 env2 ==>
       vn IN bir_env_domain env1 ==>
       (bir_env_lookup vn env1 = bir_env_lookup vn env2)``,

Cases >> Cases >> GEN_TAC >>
SIMP_TAC std_ss [bir_is_subenv_def, bir_env_domain_def, bir_env_lookup_def,
  SUBMAP_DEF, FLOOKUP_DEF])

val bir_env_read_EQ_lookup_IMPL = store_thm ("bir_env_read_EQ_lookup_IMPL",
``!env1 env2 v.
   (bir_env_lookup (bir_var_name v) env1 = bir_env_lookup (bir_var_name v) env2) ==>
   (bir_env_read v env1 = bir_env_read v env2)``,
SIMP_TAC std_ss [bir_env_read_def]);


val bir_is_subenv_READ = store_thm ("bir_is_subenv_READ",
  ``!env1 env2 v.
       bir_is_subenv env1 env2 ==>
       (bir_var_name v) IN bir_env_domain env1 ==>
       (bir_env_read v env1 = bir_env_read v env2)``,

SIMP_TAC std_ss [bir_env_read_def] >>
METIS_TAC[bir_is_subenv_LOOKUP]);



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
  bir_env_EQ_FOR_VARS_def, IN_UNIV, FLOOKUP_EXT,
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
