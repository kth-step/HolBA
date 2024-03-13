open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open combinTheory pred_setTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;

val _ = new_theory "bir_env";

Datatype:
  bir_var_t = BVar string bir_type_t
End

Definition bir_var_name_def:
  bir_var_name (BVar n _) = n
End
Definition bir_var_type_def:
  bir_var_type (BVar _ ty) = ty
End
val bir_var_t_11 = DB.fetch "-" "bir_var_t_11";

Theorem bir_var_eq_EXPAND:
  !v1 (v2:bir_var_t). (v1 = v2) <=>
                        (bir_var_name v1 = bir_var_name v2) /\
                        (bir_var_type v1 = bir_var_type v2)
Proof
Cases >> Cases >>
SIMP_TAC std_ss [bir_var_type_def, bir_var_name_def, bir_var_t_11]
QED


Datatype:
  bir_var_environment_t = BEnv (string -> (bir_val_t option))
End
val bir_var_environment_t_11 = DB.fetch "-" "bir_var_environment_t_11";

Definition bir_env_map_empty_def:
  bir_env_map_empty = (\(s:string). (NONE:bir_val_t option))
End

Definition bir_env_empty_def:
  bir_env_empty = BEnv (bir_env_map_empty)
End

Definition bir_env_lookup_def:
  (bir_env_lookup varname (BEnv env) = env varname)
End

Definition bir_env_update_def:
  bir_env_update varname v ty (BEnv env) =
      if (ty = (type_of_bir_val v)) /\ (env varname <> NONE) then
        SOME (BEnv ((varname =+ SOME v) env))
      else
        NONE
End

Theorem bir_env_lookup_UPDATE:
  bir_env_lookup vn (BEnv ((vn' =+ vo) env)) =
   (if (vn' = vn) then vo else bir_env_lookup vn (BEnv env))
Proof
SIMP_TAC std_ss [bir_env_lookup_def, APPLY_UPDATE_THM]
QED

Definition bir_env_lookup_type_def:
  bir_env_lookup_type var_name env = OPTION_MAP type_of_bir_val (bir_env_lookup var_name env)
End


Definition bir_env_check_type_def:
  bir_env_check_type var env =
    (bir_env_lookup_type (bir_var_name var) env = SOME (bir_var_type var))
End


Definition bir_env_read_def:
  bir_env_read var env =
  if (bir_env_check_type var env) then
    (bir_env_lookup (bir_var_name var) env)
  else
    NONE
End


Theorem bir_env_read_UPDATE:
  bir_env_read var (BEnv ((vn =+ vo) env)) =
   (if (bir_var_name var = vn) then
      (if (OPTION_MAP type_of_bir_val vo) = SOME (bir_var_type var) then
         vo
       else
         NONE)
    else bir_env_read var (BEnv env))
Proof
SIMP_TAC std_ss [bir_env_read_def, bir_env_lookup_UPDATE,
      bir_env_check_type_def, bir_env_lookup_type_def] >>
Cases_on `bir_var_name var = vn` >> ASM_SIMP_TAC std_ss []
QED

Theorem bir_env_read_NEQ_NONE:
  !var env v.
(v <> NONE) ==>
((bir_env_read var env = v) <=> (?va. (v = SOME va) /\
                                      (bir_env_lookup (bir_var_name var) env = v) /\
                                      (bir_var_type var = type_of_bir_val va)))
Proof
REPEAT GEN_TAC >>
Cases_on `env` >> Cases_on `v` >> (
  SIMP_TAC std_ss [bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def]
) >>
EQ_TAC >> SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss []
QED

Definition bir_env_write_def:
  bir_env_write var va env =
	 if (bir_env_check_type var env) then
	   bir_env_update (bir_var_name var) va (bir_var_type var) env
	 else
	   NONE
End

(* ===================== *)

Theorem bir_env_write_different_type:
  !v va env. (type_of_bir_val va <> bir_var_type v) ==>
               (bir_env_write v va env = NONE)
Proof
REPEAT GEN_TAC >> Cases_on `env` >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def]
QED

Theorem bir_env_write_types:
  !env env' v va.
    (bir_env_write v va env = SOME env') ==>
    (bir_env_lookup_type (bir_var_name v) env = bir_env_lookup_type (bir_var_name v) env')
Proof
Cases_on `env` >>
SIMP_TAC std_ss [bir_env_write_def, bir_env_update_def, bir_env_check_type_def] >>
REWRITE_TAC [bir_env_update_def, bir_env_lookup_type_def, bir_env_lookup_type_def, bir_env_lookup_UPDATE] >>
SIMP_TAC std_ss []
QED

Theorem bir_env_read_types:
  !env v ty r. (bir_env_read v env = r) ==>
                 (r <> NONE) ==>
                 (?va. (r = SOME va) /\ (type_of_bir_val va = bir_var_type v))
Proof
SIMP_TAC std_ss [bir_env_read_def] >>
REPEAT GEN_TAC >>
Cases_on `env` >>
SIMP_TAC std_ss [bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def] >>
METIS_TAC[bir_env_check_type_def, bir_env_lookup_type_def]
QED

(* ===================== *)


Theorem bir_env_read_EQ_lookup_IMPL:
  !env1 env2 v.
   (bir_env_lookup (bir_var_name v) env1 = bir_env_lookup (bir_var_name v) env2) ==>
   (bir_env_read v env1 = bir_env_read v env2)
Proof
SIMP_TAC std_ss [bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def]
QED


(* ===================== *)

Datatype:
  bir_var_environment_typing_t = BEnvTy (string -> (bir_type_t option))
End

Definition bir_envty_of_env_def:
  bir_envty_of_env (BEnv env) =
  BEnvTy ((OPTION_MAP type_of_bir_val) o env)
End

Definition bir_env_default_def:
  bir_env_default (BEnvTy envty) =
           BEnv ((OPTION_MAP bir_default_value_of_type) o envty)
End

Definition bir_env_satisfies_envty_def:
  bir_env_satisfies_envty (BEnv env) (BEnvTy envty) =
  !vn t. (envty vn = SOME t) ==> (?v. (env vn = SOME v) /\ (type_of_bir_val v = t))
End

Theorem bir_env_satisfies_envty_of_env:
  !env. bir_env_satisfies_envty env (bir_envty_of_env env)
Proof
Cases_on `env` >>
  SIMP_TAC std_ss [bir_env_satisfies_envty_def, bir_envty_of_env_def] >>
  METIS_TAC[]
QED

Theorem bir_env_default_satisfies_envty:
  !envty. bir_env_satisfies_envty (bir_env_default envty) envty
Proof
Cases_on `envty` >>
  SIMP_TAC std_ss [bir_env_satisfies_envty_def, bir_env_default_def] >>
  METIS_TAC[bir_default_value_of_type_SPEC]
QED

(*
TODO: typing is preserved by write
"bir_env_update_is_well_typed_env"
(bir_is_well_typed_env env /\
    (bir_env_update varname vo ty env = SOME env')) ==>
    bir_is_well_typed_env env'
*)

Definition bir_envty_includes_v_def:
  bir_envty_includes_v (BEnvTy envty) v =
  (envty (bir_var_name v) = SOME (bir_var_type v))
End

Definition bir_envty_includes_vs_def:
  bir_envty_includes_vs envty vs =
  (!v. (v IN vs) ==> (bir_envty_includes_v envty v))
End

Theorem bir_v_in_envty_env_IMP:
  !envty env v. (bir_envty_includes_v envty v) ==>
             (bir_env_satisfies_envty env envty) ==>
             (?va. (bir_env_read v env = SOME va) /\ (type_of_bir_val va = bir_var_type v))
Proof
Cases_on `envty` >> Cases_on `env` >>
  FULL_SIMP_TAC std_ss [bir_envty_includes_v_def, bir_env_satisfies_envty_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def] >>
  METIS_TAC []
QED

Theorem bir_v_in_envty_env_IMP2:
  !envty env v. (bir_envty_includes_v envty v) ==>
             (bir_env_satisfies_envty (BEnv env) envty) ==>
             (?va. (env (bir_var_name v) = SOME va) /\ (type_of_bir_val va = bir_var_type v))
Proof
Cases_on `envty` >>
  FULL_SIMP_TAC std_ss [bir_envty_includes_v_def, bir_env_satisfies_envty_def, bir_env_read_def, bir_env_check_type_def, bir_env_lookup_type_def, bir_env_lookup_def]
QED

Theorem bir_vs_in_envty_env_IMP:
  !envty env vs. (bir_envty_includes_vs envty vs) ==>
             (bir_env_satisfies_envty env envty) ==>
             !v. (v IN vs) ==>
                 (?va. (bir_env_read v env = SOME va) /\ (type_of_bir_val va = bir_var_type v))
Proof
METIS_TAC [bir_envty_includes_vs_def, bir_v_in_envty_env_IMP]
QED

Theorem bir_vs_in_envty_env_IMP2:
  !envty env vs. (bir_envty_includes_vs envty vs) ==>
             (bir_env_satisfies_envty (BEnv env) envty) ==>
             !v. (v IN vs) ==>
                 (?va. (env (bir_var_name v) = SOME va) /\ (type_of_bir_val va = bir_var_type v))
Proof
METIS_TAC [bir_envty_includes_vs_def, bir_v_in_envty_env_IMP2]
QED

Definition bir_envty_of_vs_def:
  bir_envty_of_vs (vs:bir_var_t -> bool) =
  BEnvTy (\vn. if vn IN (IMAGE bir_var_name vs) then
                 SOME (bir_var_type (CHOICE (vs DIFF { BVar vn' vt' | ?vt. (vt = vt') /\ (vn <> vn')})))
               else
                 NONE)
End

Definition bir_vs_consistent_def:
  bir_vs_consistent vs =
  !v1 v2. (v1 IN vs) ==> (v2 IN vs) ==> ((bir_var_name v1) = (bir_var_name v2)) ==> (v1 = v2)
End

Theorem bir_envty_includes_vs_IMP_vs_consistent:
  !envty vs. (bir_envty_includes_vs envty vs) ==>
             (bir_vs_consistent vs)
Proof
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
QED

Theorem bir_vs_consistent_IMP_includes_envty_of_vs:
  !envty vs. (bir_vs_consistent vs) ==>
             (bir_envty_includes_vs (bir_envty_of_vs vs) vs)
Proof
SIMP_TAC std_ss [bir_vs_consistent_def, bir_envty_of_vs_def, bir_envty_includes_vs_def, bir_envty_includes_v_def] >>
  REPEAT STRIP_TAC >>
  RW_TAC std_ss [] >>

  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  `vs DIFF {BVar vn' vt' | (vn',vt') | bir_var_name v <> vn'} = {v}` by (
    SIMP_TAC std_ss [GSPEC_IMAGE, o_DEF, EXTENSION, IMAGE_applied, IN_DIFF, IN_APP, SING_applied] >>
    GEN_TAC >> Cases_on `x = v` >- (
      ASM_SIMP_TAC (std_ss) [] >>
      POP_ASSUM (K ALL_TAC) >>
      `vs v` by METIS_TAC [IN_APP] >>
      ASM_SIMP_TAC (std_ss) [] >>
      POP_ASSUM (K ALL_TAC) >>

      GEN_TAC >>
      Cases_on `x'` >> Cases_on `v` >>
      ASM_SIMP_TAC (std_ss) [bir_var_eq_EXPAND, bir_var_name_def, bir_var_type_def] >>
      METIS_TAC []
    ) >>
    ASM_SIMP_TAC (std_ss) [] >>
    Cases_on `x IN vs` >- (
      `vs x` by METIS_TAC [IN_APP] >>
      ASM_SIMP_TAC (std_ss) [] >>

      Cases_on `x` >> Cases_on `v` >>
      Q.EXISTS_TAC `(s,b)` >>
      ASM_SIMP_TAC (std_ss) [] >>
      METIS_TAC [bir_var_name_def, bir_var_type_def]
    ) >>
    `~(vs x)` by METIS_TAC [IN_APP] >>
    ASM_SIMP_TAC (std_ss) []
  ) >|
  [
    Q.EXISTS_TAC `v` >>
    fs[]
  ,
    ASM_SIMP_TAC std_ss [CHOICE_SING]
  ]
QED

Theorem bir_envty_includes_vs_EMPTY:
  !envty. (bir_envty_includes_vs envty EMPTY)
Proof
Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, bir_envty_includes_v_def, NOT_IN_EMPTY]
QED

Theorem bir_envty_includes_vs_INSERT:
  !envty v vs. (bir_envty_includes_vs envty (v INSERT vs)) <=>
               ((bir_envty_includes_v envty v) /\ (bir_envty_includes_vs envty vs))
Proof
Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, IN_INSERT] >>
  METIS_TAC[]
QED

Theorem bir_envty_includes_vs_UNION:
  !envty vs1 vs2. (bir_envty_includes_vs envty (vs1 UNION vs2)) <=>
                  ((bir_envty_includes_vs envty vs1) /\ (bir_envty_includes_vs envty vs2))
Proof
Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, IN_UNION] >>
  METIS_TAC[]
QED

Theorem bir_envty_includes_vs_SUBSET:
  !envty vs1 vs2. (bir_envty_includes_vs envty vs1) ==>
                  (vs2 SUBSET vs1) ==>
                  (bir_envty_includes_vs envty vs2)
Proof
Cases_on `envty` >>
  SIMP_TAC std_ss [bir_envty_includes_vs_def, SUBSET_DEF] >>
  METIS_TAC[]
QED


(* ===================== *)


(* Equivalence for sets of vars *)
Definition bir_env_EQ_FOR_VARS_def:
  bir_env_EQ_FOR_VARS vs env1 env2 <=>
  (!v. v IN vs ==> (bir_env_lookup (bir_var_name v) env1 = bir_env_lookup (bir_var_name v) env2))
End

Theorem bir_env_EQ_FOR_VARS_EQUIV_EQ:
  !vs env1 env2. (bir_env_EQ_FOR_VARS vs env1 env2) <=>
                   (bir_env_EQ_FOR_VARS vs env1 = bir_env_EQ_FOR_VARS vs env2)
Proof
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, FUN_EQ_THM] >>
METIS_TAC[]
QED


Theorem bir_env_EQ_FOR_VARS_EQUIV:
  (!vs env. bir_env_EQ_FOR_VARS vs env env) /\
   (!vs env1 env2. (bir_env_EQ_FOR_VARS vs env1 env2 <=> (bir_env_EQ_FOR_VARS vs env2 env1))) /\
   (!vs env1 env2 env3. bir_env_EQ_FOR_VARS vs env1 env2 ==>
                        bir_env_EQ_FOR_VARS vs env2 env3 ==>
                        bir_env_EQ_FOR_VARS vs env1 env3)
Proof
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >> METIS_TAC[]
QED



Theorem bir_env_EQ_FOR_VARS_EMPTY:
  !env1 env2. bir_env_EQ_FOR_VARS EMPTY env1 env2
Proof
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, NOT_IN_EMPTY, bir_env_EQ_FOR_VARS_def]
QED


Theorem bir_env_EQ_FOR_VARS_UNIV:
  !env1 env2. bir_env_EQ_FOR_VARS UNIV env1 env2 <=> (env1 = env2)
Proof
REPEAT Cases >>
SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_var_t``]) [
  bir_env_EQ_FOR_VARS_def, IN_UNIV,
  bir_var_environment_t_11, bir_env_lookup_def, bir_var_name_def, FUN_EQ_THM]
QED


Theorem bir_env_EQ_FOR_VARS_SUBSET:
  !vs1 vs2 env1 env2. vs2 SUBSET vs1 ==> bir_env_EQ_FOR_VARS vs1 env1 env2 ==> bir_env_EQ_FOR_VARS vs2 env1 env2
Proof
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def, SUBSET_DEF] >>
METIS_TAC[]
QED


Theorem bir_env_EQ_FOR_VARS_read_IMPL:
  !vs env1 env2. bir_env_EQ_FOR_VARS vs env1 env2 ==>
  (!v. v IN vs ==> (bir_env_read v env1 = bir_env_read v env2))
Proof
SIMP_TAC std_ss [bir_env_EQ_FOR_VARS_def] >>
METIS_TAC[bir_env_read_EQ_lookup_IMPL]
QED


val _ = export_theory();
