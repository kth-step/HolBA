(* ------------------------------------------------------------------------- *)
(*  Example regarding a function that increments a variable in the env       *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
open bir_basicTheory bir_envTheory;
open bir_binexpTheory;
open bir_computeTheory;


val _ = new_theory "ex_increment";

Definition reg_var_def:
  reg_var = BVar "r1"
End

(* Creates an environment where r1 is set to w *)
Definition start_env_def:
  start_env w = bir_env_update bir_empty_env reg_var (BVal_Imm (Imm64 w))
End

Definition increment_exp_def:
  increment_exp = 
    BExp_BinExp BIExp_Plus
      (BExp_Den reg_var)
      (BExp_Const (Imm64 1w))
End


Theorem increment_exp_correct:
  !w. bir_compute_exp increment_exp (start_env w) = SOME (BVal_Imm (Imm64 (w + 1w)))
Proof
  rw [bir_compute_exp_def, increment_exp_def] >>

  rw [bir_env_lookup_def, start_env_def] >>
  rw [bir_env_lookup_update] >>

  rw [bir_compute_binexp_def, bir_compute_binexp_imm_def, bir_binexp_get_oper_def] >>
  rw [val_from_imm_option_def]
QED 




val _ = export_theory ();
