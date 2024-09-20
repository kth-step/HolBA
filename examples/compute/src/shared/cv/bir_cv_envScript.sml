(* ------------------------------------------------------------------------- *)
(*  Alternate env representation for cv computation                          *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;
open birTheory bir_cv_basicTheory;
open alistTheory;

val _ = new_theory "bir_cv_env";


Datatype:
  bir_cv_env_t = BCVEnv ((ident # bir_cv_val_t) list)
End

Definition bir_cv_empty_env_def:
  bir_cv_empty_env = BCVEnv []
End

Definition bir_cv_env_lookup_def:
  bir_cv_env_lookup (BCVEnv l) (BVar id) = ALOOKUP l id
End

Definition bir_cv_env_update_def:
  bir_cv_env_update (BCVEnv env) (BVar id) v = BCVEnv ((id, v)::env)
End

Definition from_cv_env_def:
  from_cv_env (BCVEnv []) = bir_empty_env /\
  from_cv_env (BCVEnv (t::q)) = 
    bir_env_update (from_cv_env (BCVEnv q)) (BVar (FST t)) (from_cv_val (SND t))
End


Definition env_eq_def:
  env_eq env cv_env = 
    !var. bir_env_lookup env var = from_cv_val_option (bir_cv_env_lookup cv_env var)
End


Theorem env_eq_from_cv_env:
  !cvenv. env_eq (from_cv_env cvenv) cvenv
Proof
  Cases_on `cvenv` >> 
  Induct_on `l` >| [
    rw [env_eq_def, from_cv_env_def] >>
    Cases_on `var` >>
    rw [bir_empty_env_def, bir_env_lookup_def, bir_cv_env_lookup_def, from_cv_val_option_def],

    rw [env_eq_def, from_cv_env_def] >>
    Cases_on `var` >>
    Cases_on `h` >>
    rw [bir_cv_env_lookup_def, bir_env_lookup_def, ALOOKUP_def] >| [
      simp [bir_env_lookup_update] >>
      simp [from_cv_val_def, from_cv_val_option_def],

      rw [bir_env_lookup_update_neq] >>
      metis_tac [env_eq_def, bir_cv_env_lookup_def]
    ]
  ]
QED

Theorem from_cv_env_empty:
  bir_empty_env = (from_cv_env bir_cv_empty_env)
Proof
  simp [bir_empty_env_def, from_cv_env_def, bir_cv_empty_env_def]
QED

Theorem from_cv_env_cons:
  !id v q env. ((BEnv env) = from_cv_env (BCVEnv q)) ==> 
    (BEnv ((id =+ SOME (from_cv_val v)) env)) = from_cv_env (BCVEnv ((id,v)::q))
Proof
  simp [from_cv_env_def] >>
  rw [GSYM bir_env_update_def]
QED


(* Correction theorem of update *)
Theorem from_cv_env_cv_env_update:
  !env var v. from_cv_env (bir_cv_env_update env var v) =
    bir_env_update (from_cv_env env) var (from_cv_val v)
Proof
  Cases_on `env` >> Cases_on `var` >>
  Induct_on `l` >>
  rw [bir_cv_env_update_def, from_cv_env_def, bir_env_update_def]
QED


val _ = export_theory ();


