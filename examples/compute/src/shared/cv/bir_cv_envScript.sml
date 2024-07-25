(* ------------------------------------------------------------------------- *)
(*  Alternate env representation for cv computation                          *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open bir_basicTheory ;
open bir_envTheory ;
open alistTheory ;

val _ = new_theory "bir_cv_env" ;


Datatype:
  bir_cv_env_t = BCVEnv ((ident # bir_val_t) list)
End

Definition bir_cv_empty_env_def:
  bir_cv_empty_env = BCVEnv []
End

Definition bir_cv_env_lookup_def:
  bir_cv_env_lookup (BCVEnv l) (BVar id) = ALOOKUP l id
End


Definition to_env_def:
  to_env (BCVEnv []) = bir_empty_env /\
  to_env (BCVEnv (t::q)) = bir_env_update (to_env (BCVEnv q)) (BVar (FST t)) (SND t)
End


Definition env_eq_def:
  env_eq env cv_env = 
    !var. bir_env_lookup env var = bir_cv_env_lookup cv_env var
End


Theorem env_eq_to_env:
  !cvenv. env_eq (to_env cvenv) cvenv
Proof
  Cases_on `cvenv` >> 
  Induct_on `l` >| [
    rw [env_eq_def, to_env_def] >>
    Cases_on `var` >>
    rw [bir_empty_env_def, bir_env_lookup_def, bir_cv_env_lookup_def],

    rw [env_eq_def, to_env_def] >>
    Cases_on `var` >>
    Cases_on `h` >>
    rw [bir_cv_env_lookup_def, bir_env_lookup_def, ALOOKUP_def] >| [
      simp [bir_env_lookup_update],

      rw [bir_env_lookup_update_neq] >>
      METIS_TAC [env_eq_def, bir_cv_env_lookup_def]
    ]
  ]
QED

Theorem to_env_empty:
  bir_empty_env = (to_env bir_cv_empty_env)
Proof
  simp [bir_empty_env_def, to_env_def, bir_cv_empty_env_def]
QED

Theorem to_env_cons:
  !id v q env. ((BEnv env) = to_env (BCVEnv q)) ==> 
    (BEnv ((id =+ SOME v) env)) = to_env (BCVEnv ((id,v)::q))
Proof
  simp [to_env_def] >>
  rw [GSYM bir_env_update_def]
QED



val _ = export_theory () ;


