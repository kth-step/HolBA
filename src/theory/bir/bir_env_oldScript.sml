open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open combinTheory pred_setTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_envTheory;


val _ = new_theory "bir_env_old";


Definition bir_env_varname_is_bound_def:
  (bir_env_varname_is_bound (BEnv env) vn = ?v. (env vn = SOME v))
End

Theorem bir_env_varname_is_bound_ALT_DEF:
  !var env. bir_env_varname_is_bound env var <=> IS_SOME (bir_env_lookup_type var env)
Proof
Cases_on `env` >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_env_varname_is_bound_def,
  bir_env_lookup_type_def, bir_env_lookup_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem bir_env_varname_is_bound_ALT2_DEF:
  !var env. bir_env_varname_is_bound env var <=> IS_SOME (bir_env_lookup var env)
Proof
SIMP_TAC std_ss [bir_env_varname_is_bound_ALT_DEF, bir_env_lookup_type_def,
  optionTheory.IS_SOME_MAP]
QED


Definition bir_env_var_is_declared_def:
  (bir_env_var_is_declared env v <=>
  (bir_env_lookup_type (bir_var_name v) env = SOME (bir_var_type v)))
End

(* This duplication is kept deliberately, because despite the same semantics, the intentention
   of what you want to express is different *)
val bir_env_var_is_declared_DEF_bir_env_check_type = store_thm ("bir_env_var_is_declared_ALT_DEF",
  ``bir_env_var_is_declared env v = bir_env_check_type v env``,
SIMP_TAC std_ss [bir_env_check_type_def, bir_env_var_is_declared_def]);





(* ===================== *)




(* bir_env_satisfies_envty + types not contained in envty don't matter *)
Definition bir_is_well_typed_env_def:
  (bir_is_well_typed_env env <=> 
     bir_env_satisfies_envty env (bir_envty_of_env env))
End

Theorem bir_is_well_typed_env_THM:
  !env. bir_is_well_typed_env env
Proof
REWRITE_TAC [bir_is_well_typed_env_def, bir_env_satisfies_envty_of_env]
QED



Definition bir_env_var_is_initialised_def:
  (bir_env_var_is_initialised env var <=>
  (?v. (bir_env_lookup (bir_var_name var) env = SOME v) /\
       (type_of_bir_val v = bir_var_type var)))
End

Theorem bir_env_var_is_initialised_EQ_envty:
  !env var. bir_env_var_is_initialised env var <=> bir_envty_includes_v (bir_envty_of_env env) var
Proof
Cases_on `env` >>
  REWRITE_TAC [bir_envty_of_env_def, bir_env_var_is_initialised_def, bir_envty_includes_v_def, bir_env_lookup_def] >>
  SIMP_TAC std_ss [] >>
  METIS_TAC []
QED


Definition bir_env_vars_are_initialised_def:
  bir_env_vars_are_initialised env vs <=>
  (!v. v IN vs ==> bir_env_var_is_initialised env v)
End


Theorem bir_env_vars_are_initialised_EQ_envty:
  !env vs. bir_env_vars_are_initialised env vs <=> bir_envty_includes_vs (bir_envty_of_env env) vs
Proof
REWRITE_TAC [bir_env_vars_are_initialised_def, bir_envty_includes_vs_def, bir_env_var_is_initialised_EQ_envty]
QED


Definition bir_env_restrict_vars_def:
 bir_env_restrict_vars vs (BEnv f) =
  (BEnv (\x. if x IN (IMAGE bir_var_name vs) then f x else NONE))
End

Theorem bir_env_restrict_vars_IN_THM:
  !vs env v.
    v IN vs ==>
    bir_env_lookup (bir_var_name v) (bir_env_restrict_vars vs env) = bir_env_lookup (bir_var_name v) env
Proof
  REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC std_ss [bir_env_lookup_def, bir_env_restrict_vars_def] >>
  `bir_var_name v IN (IMAGE bir_var_name vs)` by (
    Cases_on `v` >>
    ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
    METIS_TAC [bir_var_name_def]
  ) >>
  ASM_REWRITE_TAC []
QED


Theorem bir_env_restrict_vars_NOTIN_IMAGE_THM:
  !vs env bvn.
    bvn NOTIN (IMAGE bir_var_name vs) ==>
    bir_env_lookup bvn (bir_env_restrict_vars vs env) = NONE
Proof
  REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC std_ss [bir_env_lookup_def, bir_env_restrict_vars_def]
QED

Theorem bir_env_restrict_vars_IMP_var_is_initialised_THM:
  !v vs env.
    (v IN vs) ==>
    (bir_env_var_is_initialised env v) ==>
    (bir_env_var_is_initialised (bir_env_restrict_vars vs env) v)
Proof
  SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [bir_env_restrict_vars_IN_THM]
QED

Theorem bir_env_restrict_vars_IMP_vars_are_initialised_THM:
  !vs env.
    (bir_env_vars_are_initialised env vs) ==>
    (bir_env_vars_are_initialised (bir_env_restrict_vars vs env) vs)
Proof
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [bir_env_restrict_vars_IMP_var_is_initialised_THM]
QED


(* ===================== *)






Theorem bir_env_var_is_initialised_weaken:
  !v env. bir_env_var_is_initialised env v ==> bir_env_var_is_declared env v
Proof
Cases >> SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_lookup_type_def]
QED


Theorem bir_env_var_is_declared_weaken:
  !v env. bir_env_var_is_declared env v ==> bir_env_varname_is_bound env (bir_var_name v)
Proof
Cases >> SIMP_TAC std_ss [bir_env_var_is_declared_def,
  GSYM LEFT_FORALL_IMP_THM, bir_env_varname_is_bound_ALT_DEF,
  bir_var_name_def]
QED


Definition bir_env_order_def:
  (bir_env_order env1 env2) <=> !vn. (
     (* no new vars can be added *)
     ((bir_env_lookup vn env1 = NONE) ==>
      (bir_env_lookup vn env2 = NONE)) /\

     (* existing vars can be overwritten with the right type only *)
     (!va1. (bir_env_lookup vn env1 = SOME va1) ==>
            (?va2. (bir_env_lookup vn env2 = SOME va2) /\
                   (type_of_bir_val va1 = type_of_bir_val va2)))
   )
End


Theorem bir_env_order_REFL:
  !env. bir_env_order env env
Proof
SIMP_TAC std_ss [bir_env_order_def]
QED


Theorem bir_env_order_TRANS:
  !env1 env2 env3.
       bir_env_order env1 env2 ==> bir_env_order env2 env3 ==>
       bir_env_order env1 env3
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_order_def] >>
GEN_TAC >>
REPEAT (Q.PAT_X_ASSUM `!vn. P vn` (MP_TAC o Q.SPEC `vn`)) >>
REPEAT STRIP_TAC >> FULL_SIMP_TAC std_ss [] >> REV_FULL_SIMP_TAC std_ss []
QED


Theorem bir_env_varname_is_bound_ORDER:
  !env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_varname_is_bound env1 v ==>
                  bir_env_varname_is_bound env2 v
Proof
SIMP_TAC (std_ss++QI_ss) [bir_env_varname_is_bound_ALT_DEF, bir_env_order_def,
  bir_env_lookup_type_def, optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM]
QED


Theorem bir_env_var_is_declared_ORDER:
  !env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_declared env1 v ==>
                  bir_env_var_is_declared env2 v
Proof
Cases_on `v` >>
SIMP_TAC (std_ss++QI_ss) [bir_env_var_is_declared_def, bir_env_order_def,
  bir_env_lookup_type_def] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss []
QED


Theorem bir_env_var_is_initialised_ORDER:
  !env1 env2 v. bir_env_order env1 env2 ==>
                  bir_env_var_is_initialised env1 v ==>
                  bir_env_var_is_initialised env2 v
Proof
Cases_on `v` >>
SIMP_TAC (std_ss) [bir_env_var_is_initialised_def, bir_env_order_def,
  optionTheory.IS_SOME_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `bir_env_lookup vn env1 = SOME va1` >>
Q.PAT_X_ASSUM `!vn. _` (MP_TAC o Q.SPEC `vn`) >>
ASM_SIMP_TAC std_ss [] >>
METIS_TAC[]
QED

Theorem bir_env_vars_are_initialised_EMPTY:
  !env. bir_env_vars_are_initialised env {}
Proof
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_envty_includes_vs_EMPTY]
QED

Theorem bir_env_vars_are_initialised_INSERT:
  !env v vs. bir_env_vars_are_initialised env (v INSERT vs) <=>
               (bir_env_var_is_initialised env v /\ bir_env_vars_are_initialised env vs)
Proof
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty, bir_envty_includes_vs_INSERT]
QED

Theorem bir_env_vars_are_initialised_UNION:
  !env vs1 vs2. bir_env_vars_are_initialised env (vs1 UNION vs2) <=>
                  (bir_env_vars_are_initialised env vs1 /\
                   bir_env_vars_are_initialised env vs2)
Proof
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty, bir_envty_includes_vs_UNION]
QED

Theorem bir_env_vars_are_initialised_SUBSET:
  !env vs1 vs2. bir_env_vars_are_initialised env vs1 ==>
                  (vs2 SUBSET vs1) ==>
                   bir_env_vars_are_initialised env vs2
Proof
SIMP_TAC std_ss [bir_env_vars_are_initialised_EQ_envty, bir_env_var_is_initialised_EQ_envty] >>
METIS_TAC [bir_envty_includes_vs_SUBSET]
QED


Theorem bir_env_vars_are_initialised_ORDER:
  !env1 env2 vs. bir_env_order env1 env2 ==>
                   bir_env_vars_are_initialised env1 vs ==>
                   bir_env_vars_are_initialised env2 vs
Proof
SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
METIS_TAC[bir_env_var_is_initialised_ORDER]
QED


Theorem bir_env_order_update:
  !env env' vn va ty.
    ~(bir_env_varname_is_bound env vn) /\
    (bir_env_update vn va ty env = SOME env') ==>
    bir_env_order env env'
Proof
Cases_on `env` >>
SIMP_TAC std_ss [bir_env_update_def, bir_env_varname_is_bound_ALT_DEF] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++QI_ss) [
  bir_env_lookup_type_def,
  bir_env_lookup_def, bir_env_order_def] >>
METIS_TAC[]
QED


Theorem bir_env_order_write:
  !env env' v va.
    (bir_env_write v va env = SOME env') ==>
    bir_env_order env env'
Proof
Cases >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def, bir_env_check_type_def,
                 bir_env_lookup_type_def, bir_env_lookup_def, bir_env_order_def] >>
REPEAT STRIP_TAC >> (
  Cases_on `vn = bir_var_name v` >> FULL_SIMP_TAC std_ss [UPDATE_APPLY]
)
QED


Theorem bir_env_order_well_typed:
  !env env'. bir_is_well_typed_env env ==>
             bir_env_order env env' ==>
             bir_is_well_typed_env env'
Proof
REWRITE_TAC [bir_is_well_typed_env_THM]
QED



(* ===================== *)
Definition bir_var_set_is_well_typed_def:
  bir_var_set_is_well_typed vs <=>
  (!v1 v2. (v1 IN vs /\ v2 IN vs /\ (bir_var_name v1 = bir_var_name v2)) ==>
           (bir_var_type v1 = bir_var_type v2))
End

Theorem bir_var_set_is_well_typed_EQ_bir_vs_consistent:
  !vs.  bir_var_set_is_well_typed vs = bir_vs_consistent vs
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, bir_vs_consistent_def, bir_var_eq_EXPAND] >>
  METIS_TAC []
QED

Theorem bir_var_set_is_well_typed_INJ_DEF:
  bir_var_set_is_well_typed vs <=> INJ bir_var_name vs UNIV
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, INJ_DEF, IN_UNIV,
  bir_var_eq_EXPAND] >>
METIS_TAC[]
QED

Theorem bir_var_set_is_well_typed_EMPTY:
  bir_var_set_is_well_typed {}
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, NOT_IN_EMPTY]
QED

Theorem bir_var_set_is_well_typed_INSERT:
  !v vs. bir_var_set_is_well_typed (v INSERT vs) <=>
           bir_var_set_is_well_typed vs /\
           (!v'. v' IN vs ==>
                 (bir_var_name v = bir_var_name v') ==>
                 (bir_var_type v = bir_var_type v'))
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, IN_INSERT] >>
METIS_TAC[]
QED


Theorem bir_var_set_is_well_typed_UNION:
  !vs1 vs2. bir_var_set_is_well_typed (vs1 UNION vs2) <=>
            bir_var_set_is_well_typed vs1 /\
            bir_var_set_is_well_typed vs2 /\
            (!v1 v2. v1 IN vs1 ==> v2 IN vs2 ==>
                 (bir_var_name v1 = bir_var_name v2) ==>
                 (bir_var_type v1 = bir_var_type v2))
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, IN_UNION] >>
METIS_TAC[]
QED


Theorem bir_var_set_is_well_typed_SUBSET:
  !vs1 vs2. vs1 SUBSET vs2 ==> bir_var_set_is_well_typed vs2 ==> bir_var_set_is_well_typed vs1
Proof
SIMP_TAC std_ss [bir_var_set_is_well_typed_def, SUBSET_DEF] >>
METIS_TAC[]
QED


Theorem bir_var_set_is_well_typed_REWRS:
  (bir_var_set_is_well_typed (set [])) /\
    (!v vs. bir_var_set_is_well_typed (set (v::vs)) =
       (EVERY (\v'. (bir_var_name v = bir_var_name v') ==>
		   (bir_var_type v = bir_var_type v')
	     ) vs /\
       bir_var_set_is_well_typed (set vs))
    )
Proof
REPEAT STRIP_TAC >- (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [listTheory.LIST_TO_SET,
			  bir_var_set_is_well_typed_def]
) >>
FULL_SIMP_TAC std_ss [listTheory.LIST_TO_SET,
	  bir_var_set_is_well_typed_INSERT, listTheory.EVERY_MEM] >>
METIS_TAC []
QED


Theorem bir_env_vars_are_initialised_WELL_TYPED:
  !vs env. bir_env_vars_are_initialised env vs ==> bir_var_set_is_well_typed vs
Proof
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
QED

(* actually, we require only vs1 UNION vs2 to be consistent *)
Theorem bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION:
  !vs1 vs2 env1.
      (vs1 SUBSET vs2 /\ bir_var_set_is_well_typed vs2) ==>
      bir_env_vars_are_initialised env1 vs1 ==>
      (?env2. bir_env_EQ_FOR_VARS vs1 env1 env2 /\
              bir_env_vars_are_initialised env2 vs2)
Proof
REWRITE_TAC [bir_var_set_is_well_typed_EQ_bir_vs_consistent, bir_env_vars_are_initialised_EQ_envty] >>

REPEAT STRIP_TAC >>
Cases_on `env1` >> rename1 `BEnv env` >>

Q.ABBREV_TAC `ENV2_ = bir_env_default (bir_envty_of_vs vs2)` >>
Cases_on `ENV2_` >>

EXISTS_TAC ``BEnv (\vn. if (?vt. BVar vn vt IN vs1) then env vn else f vn)`` >>

CONJ_TAC >- (
  ASM_SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, bir_env_lookup_def] >>
  GEN_TAC >> STRIP_TAC >>
  COND_CASES_TAC >> SIMP_TAC std_ss [] >>
  Cases_on `v` >> METIS_TAC [bir_var_name_def]
) >>

ASM_SIMP_TAC std_ss [bir_envty_of_env_def, bir_envty_includes_vs_def, bir_envty_includes_v_def] >>
REPEAT STRIP_TAC >>
Cases_on `v` >>
ASM_SIMP_TAC std_ss [bir_var_name_def, bir_var_type_def] >>
`bir_vs_consistent vs1` by METIS_TAC [bir_envty_includes_vs_IMP_vs_consistent] >>
Cases_on `BVar s b IN vs1` >- (
  COND_CASES_TAC >> SIMP_TAC std_ss [] >- (
    METIS_TAC [bir_env_satisfies_envty_of_env, bir_vs_in_envty_env_IMP2, bir_var_name_def, bir_var_type_def]
  ) >>
  METIS_TAC []
) >>

COND_CASES_TAC >> SIMP_TAC std_ss [] >- (
  METIS_TAC [bir_vs_consistent_def, bir_var_name_def, bir_var_eq_EXPAND, SUBSET_THM]
) >>

`bir_env_satisfies_envty (BEnv f) (bir_envty_of_vs vs2)` by
  METIS_TAC [bir_env_default_satisfies_envty] >>
Cases_on `bir_envty_of_vs vs2` >>
`bir_envty_includes_vs (bir_envty_of_vs vs2) vs2` by
  METIS_TAC [bir_vs_consistent_IMP_includes_envty_of_vs] >>
REV_FULL_SIMP_TAC std_ss [bir_envty_includes_vs_def, bir_envty_includes_v_def] >>
FULL_SIMP_TAC std_ss [bir_env_satisfies_envty_def] >>
METIS_TAC [bir_var_name_def, bir_var_type_def]
QED


(*
Theorem bir_env_vars_are_initialised_ENV_EXISTS_IFF:
  !vs. (?env. bir_env_vars_are_initialised env vs) <=> (bir_var_set_is_well_typed vs)
Proof
GEN_TAC >> EQ_TAC >- (
  METIS_TAC[bir_env_vars_are_initialised_WELL_TYPED, bir_env_vars_are_initialised_FINITE]
) >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`{}`, `vs`, `bir_empty_env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [EMPTY_SUBSET, bir_env_vars_are_initialised_EMPTY, NOT_IN_EMPTY,
  bir_env_EQ_FOR_VARS_EMPTY]
QED

*)


(* ===================== *)


val _ = export_theory();
