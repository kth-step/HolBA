open HolKernel Parse bossLib boolLib
open bir_basicTheory


val _ = new_theory "bir_env"


(* Environment for evaluation *)
Datatype:
    bir_var_environment_t = BEnv (string -> (bir_val_t option))
End

(** Lookup function *)
Definition bir_env_lookup_def:
    bir_env_lookup (BEnv env) id = env id
End

(** Lookup relation *)
Inductive bir_env_lookup_rel:
    !env id. (env id = (SOME a)) ==> bir_env_lookup_rel (BEnv env) id a
End

(** Empty environment *)
Definition bir_empty_env_def:
    bir_empty_env = BEnv (\x. NONE)
End

(** Update environment 
*   Slightly differs from original as we don’t check for existence here *)
Definition bir_env_update_def:
    bir_env_update env id v = BEnv ((id =+ SOME v) env)
End


(** Some theorems about bir_env functions *)
Theorem bir_env_lookup_empty:
    !id v. ~(bir_env_lookup_rel bir_empty_env id v)
Proof
    rw [bir_empty_env_def, bir_env_lookup_rel_cases]
QED

Theorem bir_env_lookup_update:
    !env id v. bir_env_lookup_rel (bir_env_update env id v) id v 
Proof
    rw [bir_env_update_def, bir_env_lookup_rel_cases]
QED

Theorem bir_env_lookup_eq_rel:
    !env id v. bir_env_lookup_rel env id v <=> bir_env_lookup env id = SOME v
Proof
    rpt STRIP_TAC >>
    Cases_on `env` >>
    rw [bir_env_lookup_def, bir_env_lookup_rel_cases]
QED


val _ = export_theory ()
