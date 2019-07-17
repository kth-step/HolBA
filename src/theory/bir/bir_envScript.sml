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
val bir_var_environment_t_11 =
  DB.fetch "-" "bir_var_environment_t_11";

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
  (bir_env_update varname vo vartype (BEnv env) =
    if (vartype <> type_of_bir_kval vo)
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


val bir_env_lookup_type_def = Define `
  bir_env_lookup_type var_name env =
    type_of_bir_kval (bir_env_lookup var_name env)`;


val bir_env_check_type_def = Define `
  bir_env_check_type var env =
    (bir_env_lookup_type (bir_var_name var) env =
      bir_var_type var
    )`;

(* Note design choice: BVal_Unknown is returned upon explicit type
 * disagreement between stored and looked-up variable. *)
val bir_env_read_def = Define `bir_env_read v env =
  if (bir_env_check_type v env)
  then BVal_Known (bir_env_lookup (bir_var_name v) env)
  else BVal_Unknown`;


val bir_env_read_UPDATE = store_thm ("bir_env_read_UPDATE",
  ``!v vn vo env.
    bir_env_read v (BEnv ((vn =+ vo) env)) =
      (if (bir_var_name v = vn)
       then (if (type_of_bir_kval vo = bir_var_type v)
             then BVal_Known vo
             else BVal_Unknown
            )
       else bir_env_read v (BEnv env)
      )``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_env_read_def, bir_env_lookup_UPDATE] >>
Cases_on `bir_var_name v = vn` >> (
  FULL_SIMP_TAC std_ss [type_of_bir_kval_def,
			bir_env_check_type_def,
			bir_env_lookup_type_def,
                        bir_env_lookup_def,
			combinTheory.UPDATE_APPLY]
)
);

(* Note: Gains a new antecedent from no longer having type in the
 * returning tuple. *)
val bir_env_read_NEQ_UNKNOWN =
  store_thm ("bir_env_read_NEQ_UNKNOWN",
  ``!var env v.
    (type_of_bir_kval v = bir_var_type var) ==>
    ((bir_env_read var env = BVal_Known v) <=>
     (bir_env_lookup (bir_var_name var) env =
        v
     )
    )``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_env_read_def,
                 bir_env_check_type_def,
                 bir_env_lookup_type_def] >>
REPEAT CASE_TAC >>
METIS_TAC []
);

val bir_env_write_def = Define `bir_env_write v va env =
  if (bir_env_check_type v env)
  then bir_env_update (bir_var_name v) va (bir_var_type v) env
  else NONE`;


val bir_env_write_WrongVal = store_thm ("bir_env_write_WrongVal",
  ``!v va env.
    (type_of_bir_kval va <> bir_var_type v) ==>
    (bir_env_write v va env = NONE)``,

REPEAT GEN_TAC >> Cases_on `env` >>
SIMP_TAC std_ss [bir_env_write_def,
                 bir_env_check_type_def,
                 bir_env_lookup_type_def, 
                 bir_env_update_def]
);

(* Deprecated...
val bir_env_update_is_well_typed_env =
  store_thm ("bir_env_update_is_well_typed_env",
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
)
);
*)

(* Deprecated...
val bir_env_write_is_well_typed_env = store_thm ("bir_env_write_is_well_typed_env",
``!env env' v va.
    (bir_is_well_typed_env env /\
    (bir_env_write v va env = SOME env')) ==>
    bir_is_well_typed_env env'``,

SIMP_TAC std_ss [bir_env_write_def] >>
METIS_TAC[bir_env_update_is_well_typed_env]
);
*)

(* Deprecated...
val bir_is_well_typed_env_lookup =
  store_thm ("bir_is_well_typed_env_lookup",
  ``!env vn ty v. bir_is_well_typed_env env ==>
                  (bir_env_lookup vn env = SOME (ty, SOME v)) ==>
                  (type_of_bir_val v = SOME ty)``,

Cases >> SIMP_TAC std_ss [bir_is_well_typed_env_def] >>
rename1 `BEnv f` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_lookup_def, FEVERY_ALL_FLOOKUP] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!k. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss []
);
*)

(* Old name: bir_is_well_typed_env_read *)

val bir_env_read_type =
  store_thm ("bir_env_read_type",
  ``!env v ty r.
      (bir_env_read v env = r) ==>
      (r <> BVal_Unknown) ==>
      (type_of_bir_val r = SOME (bir_var_type v))``,

SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT GEN_TAC >>
REPEAT CASE_TAC >>
FULL_SIMP_TAC std_ss [type_of_bir_val_def,
                      bir_env_check_type_def,
                      bir_env_lookup_type_def]
);


val bir_env_read_EQ_Unknown = store_thm ("bir_env_read_EQ_Unknown",
  ``!v env.
        (bir_env_read v env = BVal_Unknown) <=>
          (!kv.
            (type_of_bir_kval kv = bir_var_type v) ==>
            (bir_env_lookup (bir_var_name v) env <>
              kv
            )
          )``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC std_ss [bir_env_lookup_type_def,
			bir_env_check_type_def]
)
);
(*
(* All varnames are bound in a total map, so... *)
val bir_env_varname_is_bound_def = Define `
  (bir_env_varname_is_bound (BEnv env) var = (var IN FDOM env))`;

val bir_env_varname_is_bound_ALT_DEF =
  store_thm ("bir_env_varname_is_bound_ALT_DEF",
  ``!var env.
      bir_env_varname_is_bound env var <=>
        IS_SOME (bir_env_lookup_type var env)``,

Cases_on `env` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss)
           [bir_env_varname_is_bound_def,
            bir_env_lookup_type_def, bir_env_lookup_def,
            FLOOKUP_DEF]
)
);

val bir_env_varname_is_bound_ALT2_DEF =
  store_thm ("bir_env_varname_is_bound_ALT2_DEF",
  ``!var env.
      bir_env_varname_is_bound env var <=>
        IS_SOME (bir_env_lookup var env)``,

SIMP_TAC std_ss [bir_env_varname_is_bound_ALT_DEF,
                 bir_env_lookup_type_def,
                 optionTheory.IS_SOME_MAP]
);


val bir_env_var_is_declared_def = Define `
  (bir_env_var_is_declared env v <=>
  (bir_env_lookup_type (bir_var_name v) env = SOME (bir_var_type v)))`;

(* This duplication is kept deliberately, because despite the same
 * semantics, the intention of what you want to express is
 * different *)
val bir_env_var_is_declared_DEF_bir_env_check_type =
  store_thm ("bir_env_var_is_declared_ALT_DEF",
  ``bir_env_var_is_declared env v = bir_env_check_type v env``,
SIMP_TAC std_ss [bir_env_check_type_def,
                 bir_env_var_is_declared_def]
);
*)

(* Old name: bir_env_var_is_initialised *)
val bir_env_var_is_well_typed_def = Define `
  (bir_env_var_is_well_typed env var <=>
    (?kv.
      (bir_env_lookup (bir_var_name var) env = kv) /\
      (type_of_bir_kval kv = bir_var_type var)
    )
  )`;
(* No more declaration...
val bir_env_var_is_initialised_weaken =
  store_thm ("bir_env_var_is_initialised_weaken",
  ``!v env.
      bir_env_var_is_initialised env v ==>
      bir_env_var_is_declared env v``,

Cases >> SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_lookup_type_def]);
*)
(* No more declaration...
val bir_env_var_is_declared_weaken =
  store_thm ("bir_env_var_is_declared_weaken",
  ``!v env.
      bir_env_var_is_declared env v ==>
      bir_env_varname_is_bound env (bir_var_name v)``,

Cases >> SIMP_TAC std_ss [bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_varname_is_bound_ALT_DEF,
  bir_var_name_def]);
*)
(* TODO: Remove now? *)
val _ = Datatype `bir_env_cond_t =
  | BEnvCond_var_well_typed bir_var_t`;

val bir_env_cond_eval_def = Define `
  (bir_env_cond_eval env (BEnvCond_var_well_typed v) <=>
    bir_env_var_is_well_typed env v)`;


val bir_env_order_def = Define `
  (bir_env_order env1 env2) <=>
    !vn. (
(*
     (* new vars can be added and initialised, but only of the
      * correct type *)
     (!ty v. (bir_env_lookup vn env1 = NONE) ==>
             (bir_env_lookup vn env2 = SOME (ty, SOME v)) ==>
             (type_of_bir_val v = SOME ty)
     ) /\

     (* existing vars can be initialised with the right type *)
     (!ty. (bir_env_lookup vn env1 = SOME (ty, NONE)) ==>
           (?vo. (bir_env_lookup vn env2 = SOME (ty, vo)) /\
                 (!v. (vo = SOME v) ==>
                      (type_of_bir_val v = SOME ty)
                 )
           )
     ) /\
*)
     (* The value of existing vars can change, but their type
      * cannot. *)
     (!kv ty.
       ((bir_env_lookup vn env1 = kv) /\
        (type_of_bir_kval kv = ty)
       )==>
       (?kv'.
         ((bir_env_lookup vn env2 = kv') /\
          (type_of_bir_kval kv' = ty)
         )
       )
     )
   )`;


val bir_env_order_REFL = store_thm ("bir_env_order_REFL",
  ``!env. bir_env_order env env``,

SIMP_TAC std_ss [bir_env_order_def]
);


val bir_env_order_TRANS = store_thm ("bir_env_order_TRANS",
  ``!env1 env2 env3.
      bir_env_order env1 env2 ==>
      bir_env_order env2 env3 ==>
      bir_env_order env1 env3``,

METIS_TAC [bir_env_order_def]
);

(* All varnames are bound...
val bir_env_varname_is_bound_ORDER =
  store_thm ("bir_env_varname_is_bound_ORDER",
  ``!env1 env2 v.
      bir_env_order env1 env2 ==>
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
*)
(* No more declare...
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
*)

val bir_env_var_is_well_typed_ORDER =
  store_thm ("bir_env_var_is_well_typed_ORDER",
  ``!env1 env2 v.
      bir_env_order env1 env2 ==>
      bir_env_var_is_well_typed env1 v ==>
      bir_env_var_is_well_typed env2 v``,

SIMP_TAC std_ss [bir_env_var_is_well_typed_def,
                 bir_env_order_def]
);


val bir_env_cond_eval_ORDER = store_thm ("bir_env_cond_eval_ORDER",
  ``!env1 env2 c.
      bir_env_order env1 env2 ==>
      bir_env_cond_eval env1 c ==>
      bir_env_cond_eval env2 c``,

Cases_on `c` >> (
  SIMP_TAC std_ss [bir_env_cond_eval_def] >>
  METIS_TAC[bir_env_var_is_well_typed_ORDER]
)
);


val bir_env_vars_are_well_typed_def = Define `
  bir_env_vars_are_well_typed env vs <=>
    (!v. v IN vs ==> bir_env_var_is_well_typed env v)`;

val bir_env_vars_are_well_typed_EMPTY =
  store_thm ("bir_env_vars_are_well_typed_EMPTY",
  ``!env. bir_env_vars_are_well_typed env {}``,

SIMP_TAC std_ss [bir_env_vars_are_well_typed_def, NOT_IN_EMPTY]
);

val bir_env_vars_are_well_typed_INSERT =
  store_thm ("bir_env_vars_are_well_typed_INSERT",
  ``!env v vs.
      bir_env_vars_are_well_typed env (v INSERT vs) <=>
        (bir_env_var_is_well_typed env v /\
         bir_env_vars_are_well_typed env vs
        )``,

SIMP_TAC std_ss [bir_env_vars_are_well_typed_def, IN_INSERT] >>
METIS_TAC []
);

val bir_env_vars_are_well_typed_UNION =
  store_thm ("bir_env_vars_are_well_typed_UNION",
  ``!env vs1 vs2.
      bir_env_vars_are_well_typed env (vs1 UNION vs2) <=>
        (bir_env_vars_are_well_typed env vs1 /\
         bir_env_vars_are_well_typed env vs2) ``,

SIMP_TAC std_ss [bir_env_vars_are_well_typed_def, IN_UNION] >>
METIS_TAC []
);

val bir_env_vars_are_well_typed_SUBSET =
  store_thm ("bir_env_vars_are_well_typed_SUBSET",
  ``!env vs1 vs2.
      bir_env_vars_are_well_typed env vs1 ==>
      (vs2 SUBSET vs1) ==>
      bir_env_vars_are_well_typed env vs2``,

SIMP_TAC std_ss [bir_env_vars_are_well_typed_def, SUBSET_DEF] >>
METIS_TAC []
);


val bir_env_vars_are_well_typed_ORDER =
  store_thm ("bir_env_vars_are_well_typed_ORDER",
  ``!env1 env2 vs.
      bir_env_order env1 env2 ==>
      bir_env_vars_are_well_typed env1 vs ==>
      bir_env_vars_are_well_typed env2 vs``,

SIMP_TAC std_ss [bir_env_vars_are_well_typed_def] >>
METIS_TAC [bir_env_var_is_well_typed_ORDER]
);

(* Nonsensical with new changes?
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
*)

val bir_env_order_write = store_thm ("bir_env_order_write",
``!env env' v va.
    (bir_env_write v va env = SOME env') ==>
    bir_env_order env env'``,

Cases >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss)
         [bir_env_write_def, bir_env_update_def,
          bir_env_order_def, bir_env_lookup_def,
          bir_env_check_type_def, bir_env_lookup_type_def,
          PULL_EXISTS] >>

REPEAT STRIP_TAC >>
Cases_on `bir_var_name v = vn` >> (
  FULL_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
)
);

(* Deprecated...
val bir_env_order_well_typed =
  store_thm ("bir_env_order_well_typed",
  ``!env env'.
      bir_is_well_typed_env env ==>
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
Cases_on `vo` >> SIMP_TAC std_ss []
);
*)

(* Domains and subenvironment don't really makes sense with total
 * maps... *)
(* Domains *)
(*
val bir_env_domain_def = Define `
  bir_env_domain (BEnv env) = FDOM env`;

val bir_env_domain_FINITE = store_thm ("bir_env_domain_FINITE",
  ``!env. FINITE (bir_env_domain env)``,

Cases >>
SIMP_TAC std_ss [bir_env_domain_def, FDOM_FINITE]
);


val bir_env_domain_LOOKUP = store_thm ("bir_env_domain_LOOKUP",
``!env vn. (vn IN (bir_env_domain env)) <=> IS_SOME (bir_env_lookup vn env)``,

Cases >> GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_domain_def, bir_env_lookup_def, FLOOKUP_DEF]);
*)


(* Subenvironments *)
(*
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
*)
val bir_env_read_EQ_lookup_IMPL =
  store_thm ("bir_env_read_EQ_lookup_IMPL",
  ``!env1 env2 v.
      (bir_env_lookup (bir_var_name v) env1 =
        bir_env_lookup (bir_var_name v) env2) ==>
      (bir_env_read v env1 = bir_env_read v env2)``,

SIMP_TAC std_ss [bir_env_read_def,
                 bir_env_check_type_def,
                 bir_env_lookup_type_def]
);

(*
val bir_is_subenv_READ = store_thm ("bir_is_subenv_READ",
  ``!env1 env2 v.
       bir_is_subenv env1 env2 ==>
       (bir_var_name v) IN bir_env_domain env1 ==>
       (bir_env_read v env1 = bir_env_read v env2)``,

SIMP_TAC std_ss [bir_env_read_def] >>
METIS_TAC [bir_is_subenv_LOOKUP]);
*)


(* Equivalence for sets of vars *)
val bir_env_EQ_FOR_VARS_def = Define `
  bir_env_EQ_FOR_VARS vs env1 env2 <=>
    (!v.
      v IN vs ==>
      (bir_env_lookup (bir_var_name v) env1 =
        bir_env_lookup (bir_var_name v) env2
      )
    )`

val bir_env_EQ_FOR_VARS_EQUIV_EQ =
  store_thm ("bir_env_EQ_FOR_VARS_EQUIV_EQ",
  ``!vs env1 env2.
      (bir_env_EQ_FOR_VARS vs env1 env2) <=>
        (bir_env_EQ_FOR_VARS vs env1 =
          bir_env_EQ_FOR_VARS vs env2
        )``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, FUN_EQ_THM] >>
METIS_TAC []
);


val bir_env_EQ_FOR_VARS_EQUIV =
  store_thm ("bir_env_EQ_FOR_VARS_EQUIV",
 ``(!vs env. bir_env_EQ_FOR_VARS vs env env) /\
   (!vs env1 env2.
     (bir_env_EQ_FOR_VARS vs env1 env2 <=>
       (bir_env_EQ_FOR_VARS vs env2 env1)
     )
   ) /\
   (!vs env1 env2 env3.
     bir_env_EQ_FOR_VARS vs env1 env2 ==>
     bir_env_EQ_FOR_VARS vs env2 env3 ==>
     bir_env_EQ_FOR_VARS vs env1 env3
   )``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >>
METIS_TAC []
);



val bir_env_EQ_FOR_VARS_EMPTY =
  store_thm ("bir_env_EQ_FOR_VARS_EMPTY",
  ``!env1 env2. bir_env_EQ_FOR_VARS EMPTY env1 env2``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, NOT_IN_EMPTY,
                 bir_env_EQ_FOR_VARS_def]
);


val bir_env_EQ_FOR_VARS_UNIV =
  store_thm ("bir_env_EQ_FOR_VARS_UNIV",
  ``!env1 env2.
      bir_env_EQ_FOR_VARS UNIV env1 env2 <=> (env1 = env2)``,

REPEAT Cases >>
SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_var_t``]) [bir_env_EQ_FOR_VARS_def, IN_UNIV,
    bir_var_environment_t_11, bir_env_lookup_def, bir_var_name_def,
    FUN_EQ_THM]
);


val bir_env_EQ_FOR_VARS_SUBSET =
  store_thm ("bir_env_EQ_FOR_VARS_SUBSET",
  ``!vs1 vs2 env1 env2.
      vs2 SUBSET vs1 ==>
      bir_env_EQ_FOR_VARS vs1 env1 env2 ==>
      bir_env_EQ_FOR_VARS vs2 env1 env2``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, SUBSET_DEF] >>
METIS_TAC []
);


val bir_env_EQ_FOR_VARS_read_IMPL =
  store_thm ("bir_env_EQ_FOR_VARS_read_IMPL",
  ``!vs env1 env2.
      bir_env_EQ_FOR_VARS vs env1 env2 ==>
      (!v.
        v IN vs ==>
        (bir_env_read v env1 = bir_env_read v env2)
      )``,

SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >>
METIS_TAC [bir_env_read_EQ_lookup_IMPL]
);


val _ = export_theory();
