open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open combinTheory pred_setTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_envTheory;


val _ = new_theory "bir_env_old";


val bir_env_varname_is_bound_def = Define `
  (bir_env_varname_is_bound (BEnv env) vn = ?v. (env vn = SOME v))`;

val bir_env_varname_is_bound_ALT_DEF = store_thm ("bir_env_varname_is_bound_ALT_DEF",
  ``!var env. bir_env_varname_is_bound env var <=> IS_SOME (bir_env_lookup_type var env)``,

Cases_on `env` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_varname_is_bound_def,
    bir_env_lookup_type_def, bir_env_lookup_def] >>
  cheat
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





(* ===================== *)




(* bir_env_satisfies_envty + types not contained in envty don't matter *)
val bir_is_well_typed_env_def = Define `
  (bir_is_well_typed_env env <=> 
     bir_env_satisfies_envty env (bir_envty_of_env env))`;

val bir_is_well_typed_env_THM = store_thm("bir_is_well_typed_env_THM", ``
  !env. bir_is_well_typed_env env
``,
  REWRITE_TAC [bir_is_well_typed_env_def, bir_env_satisfies_envty_of_env]
);



val bir_env_var_is_initialised_def = Define `
  (bir_env_var_is_initialised env var <=>
  (?v. (bir_env_lookup (bir_var_name var) env = SOME v) /\
       (type_of_bir_val v = bir_var_type var)))`;

val bir_env_var_is_initialised_EQ_envty = store_thm("bir_env_var_is_initialised_EQ_envty", ``
  !env var. bir_env_var_is_initialised env var <=> bir_envty_includes_v (bir_envty_of_env env) var
``,
  Cases_on `env` >>
  REWRITE_TAC [bir_envty_of_env_def, bir_env_var_is_initialised_def, bir_envty_includes_v_def, bir_env_lookup_def] >>
  cheat
);


val bir_env_vars_are_initialised_def = Define `
  bir_env_vars_are_initialised env vs <=>
  (!v. v IN vs ==> bir_env_var_is_initialised env v)`;


val bir_env_vars_are_initialised_EQ_envty = store_thm("bir_env_vars_are_initialised_EQ_envty", ``
  !env vs. bir_env_vars_are_initialised env vs <=> bir_envty_includes_vs (bir_envty_of_env env) vs
``,
  REWRITE_TAC [bir_env_vars_are_initialised_def, bir_envty_includes_vs_def, bir_env_var_is_initialised_EQ_envty]
);


(* ===================== *)






val bir_env_var_is_initialised_weaken = store_thm ("bir_env_var_is_initialised_weaken",
  ``!v env. bir_env_var_is_initialised env v ==> bir_env_var_is_declared env v``,
Cases >> SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_lookup_type_def]);


val bir_env_var_is_declared_weaken = store_thm ("bir_env_var_is_declared_weaken",
  ``!v env. bir_env_var_is_declared env v ==> bir_env_varname_is_bound env (bir_var_name v)``,
Cases >> SIMP_TAC std_ss [bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_varname_is_bound_ALT_DEF,
  bir_var_name_def]);


val bir_env_order_def = Define `
  (bir_env_order env1 env2) <=> !vn. (
     (* no new vars can be added *)
     ((bir_env_lookup vn env1 = NONE) ==>
      (bir_env_lookup vn env2 = NONE)) /\

     (* existing vars can be overwritten with the right type only *)
     (!va1. (bir_env_lookup vn env1 = SOME va1) ==>
            (?va2. (bir_env_lookup vn env2 = SOME va2) /\
                   (type_of_bir_val va1 = type_of_bir_val va2)))
   )`;


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
REPEAT STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> REV_FULL_SIMP_TAC std_ss []
);


val bir_env_varname_is_bound_ORDER = store_thm ("bir_env_varname_is_bound_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_varname_is_bound env1 v ==>
                  bir_env_varname_is_bound env2 v``,
SIMP_TAC (std_ss++QI_ss) [bir_env_varname_is_bound_ALT_DEF, bir_env_order_def,
  bir_env_lookup_type_def, optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM]
);


val bir_env_var_is_declared_ORDER = store_thm ("bir_env_var_is_declared_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_declared env1 v ==>
                  bir_env_var_is_declared env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_var_is_declared_def, bir_env_order_def,
  bir_env_lookup_type_def] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss []
);


val bir_env_var_is_initialised_ORDER = store_thm ("bir_env_var_is_initialised_ORDER",
  ``!env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_initialised env1 v ==>
                  bir_env_var_is_initialised env2 v``,
Cases_on `v` >>
SIMP_TAC (std_ss) [bir_env_var_is_initialised_def, bir_env_order_def,
  optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
METIS_TAC[]);

val bir_env_vars_are_initialised_EMPTY = store_thm ("bir_env_vars_are_initialised_EMPTY",
  ``!env. bir_env_vars_are_initialised env {}``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_envty_includes_vs_EMPTY]);

val bir_env_vars_are_initialised_INSERT = store_thm ("bir_env_vars_are_initialised_INSERT",
  ``!env v vs. bir_env_vars_are_initialised env (v INSERT vs) <=>
               (bir_env_var_is_initialised env v /\ bir_env_vars_are_initialised env vs)``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty, bir_envty_includes_vs_INSERT]);

val bir_env_vars_are_initialised_UNION = store_thm ("bir_env_vars_are_initialised_UNION",
  ``!env vs1 vs2. bir_env_vars_are_initialised env (vs1 UNION vs2) <=>
                  (bir_env_vars_are_initialised env vs1 /\
                   bir_env_vars_are_initialised env vs2) ``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty, bir_envty_includes_vs_UNION]);

val bir_env_vars_are_initialised_SUBSET = store_thm ("bir_env_vars_are_initialised_SUBSET",
  ``!env vs1 vs2. bir_env_vars_are_initialised env vs1 ==>
                  (vs2 SUBSET vs1) ==>
                   bir_env_vars_are_initialised env vs2``,
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty] >>
METIS_TAC [bir_envty_includes_vs_SUBSET]);


val bir_env_vars_are_initialised_ORDER = store_thm ("bir_env_vars_are_initialised_ORDER",
  ``!env1 env2 vs. bir_env_order env1 env2 ==>
                   bir_env_vars_are_initialised env1 vs ==>
                   bir_env_vars_are_initialised env2 vs``,

SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
METIS_TAC[bir_env_var_is_initialised_ORDER]);


val bir_env_order_update = store_thm ("bir_env_order_update",
``!env env' vn va ty.
    ~(bir_env_varname_is_bound env vn) /\
    (bir_env_update vn va ty env = SOME env') ==>
    bir_env_order env env'``,

Cases_on `env` >>
SIMP_TAC std_ss [bir_env_update_def, bir_env_varname_is_bound_ALT_DEF] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++QI_ss) [
  bir_env_lookup_type_def,
  bir_env_lookup_def, bir_env_order_def] >>
METIS_TAC[]);


val bir_env_order_write = store_thm ("bir_env_order_write",
``!env env' v va.
    (bir_env_write v va env = SOME env') ==>
    bir_env_order env env'``,

Cases >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def, bir_env_check_type_def,
                 bir_env_lookup_type_def, bir_env_lookup_def, bir_env_order_def] >>
REPEAT STRIP_TAC >> (
  Cases_on `vn = bir_var_name v` >> FULL_SIMP_TAC std_ss [UPDATE_APPLY]
));


val bir_env_order_well_typed = store_thm ("bir_env_order_well_typed",
``!env env'. bir_is_well_typed_env env ==>
             bir_env_order env env' ==>
             bir_is_well_typed_env env'``,

REWRITE_TAC [bir_is_well_typed_env_THM]
);



(* ===================== *)
val bir_var_set_is_well_typed_def = Define `bir_var_set_is_well_typed vs <=>
  (!v1 v2. (v1 IN vs /\ v2 IN vs /\ (bir_var_name v1 = bir_var_name v2)) ==>
           (bir_var_type v1 = bir_var_type v2))`;

val bir_var_set_is_well_typed_EQ_bir_vs_consistent = store_thm ("bir_var_set_is_well_typed_EQ_bir_vs_consistent", ``
  !vs.  bir_var_set_is_well_typed vs = bir_vs_consistent vs
``,
  SIMP_TAC std_ss [bir_var_set_is_well_typed_def, bir_vs_consistent_def, bir_var_eq_EXPAND] >>
  METIS_TAC []
);

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
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC []
);


val bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION = store_thm ("bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION",
  ``!vs1 vs2 env1.
      (vs1 SUBSET vs2 /\ bir_var_set_is_well_typed vs2) ==>
      bir_env_vars_are_initialised env1 vs1 ==>
      (?env2. bir_env_EQ_FOR_VARS vs1 env1 env2 /\
              bir_env_vars_are_initialised env2 vs2)``,

cheat);


(*
val bir_env_vars_are_initialised_ENV_EXISTS_IFF = store_thm ("bir_env_vars_are_initialised_ENV_EXISTS_IFF",
  ``!vs. (?env. bir_env_vars_are_initialised env vs) <=> (bir_var_set_is_well_typed vs)``,

GEN_TAC >> EQ_TAC >- (
  METIS_TAC[bir_env_vars_are_initialised_WELL_TYPED, bir_env_vars_are_initialised_FINITE]
) >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`{}`, `vs`, `bir_empty_env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [EMPTY_SUBSET, bir_env_vars_are_initialised_EMPTY, NOT_IN_EMPTY,
  bir_env_EQ_FOR_VARS_EMPTY]);

*)


(* ===================== *)


val _ = export_theory();
