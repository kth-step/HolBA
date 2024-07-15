(* ------------------------------------------------------------------------- *)
(*  Definition of variable environments                                      *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory ;


val _ = new_theory "bir_env" ;


(* Environment for evaluation *)
Datatype:
  bir_var_environment_t = BEnv (ident -> (bir_val_t option))
End

(* Lookup function *)
Definition bir_env_lookup_def:
  bir_env_lookup (BEnv env) (BVar id) = env id
End

(* Lookup relation *)
Definition bir_env_lookup_rel_def:
  bir_env_lookup_rel (BEnv env) (BVar id) a = (env id = (SOME a)) 
End

(* Empty environment *)
Definition bir_empty_env_def:
  bir_empty_env = BEnv (\x. NONE)
End

(* Update environment *)
(* Slightly differs from original as we don’t check for existence here *)
Definition bir_env_update_def:
  bir_env_update ((BEnv env):bir_var_environment_t) (BVar id) v = BEnv ((id =+ SOME v) env)
End

(* ****************************************** *)
(* **************** THEOREMS **************** *)
(* ****************************************** *)


(* Some theorems about bir_env functions *)
Theorem bir_env_lookup_empty:
  !var v. ~(bir_env_lookup_rel bir_empty_env var v)
Proof
  Cases_on `var` >>
  rw [bir_empty_env_def, bir_env_lookup_rel_def]
QED

Theorem bir_env_lookup_rel_update:
  !env var v. bir_env_lookup_rel (bir_env_update env var v) var v 
Proof
  Cases_on `var` >> Cases_on `env` >>
  rw [bir_env_update_def, bir_env_lookup_rel_def]
QED

Theorem bir_env_lookup_update:
  !env var v. bir_env_lookup (bir_env_update env var v) var = SOME v 
Proof
  rpt GEN_TAC >>
  Cases_on `var` >> Cases_on `env` >>
  rw [bir_env_update_def, bir_env_lookup_def]
QED

Theorem bir_env_lookup_update_neq:
  !env var1 var2 v. 
    var1 <> var2 ==>
      bir_env_lookup (bir_env_update env var1 v) var2 = bir_env_lookup env var2
Proof
  Cases_on `var1` >> Cases_on `var2` >>
  rw [bir_var_t_11] >>
  Cases_on `env` >>
  simp [bir_env_update_def] >>
  rw [bir_env_lookup_def] >>
  EVAL_TAC >>
  METIS_TAC []
QED

(* Lookup and relation are the same *)
Theorem bir_env_lookup_eq_rel:
  !env var v. bir_env_lookup_rel env var v <=> bir_env_lookup env var = SOME v
Proof
  rpt STRIP_TAC >>
  Cases_on `env` >>
  Cases_on `var` >>
    rw [bir_env_lookup_def, bir_env_lookup_rel_def]
QED


(* Injective *)
Theorem bir_env_lookup_rel_inj:
  !env var v1 v2.
    bir_env_lookup_rel env var v1 ==>
    bir_env_lookup_rel env var v2 ==>
    v1 = v2
Proof
  Cases_on `env` >> Cases_on `var` >>
    simp [bir_env_lookup_rel_def]
QED



val _ = export_theory () ;
