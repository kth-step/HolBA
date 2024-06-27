open HolKernel Parse boolLib bossLib
open bir_evalTheory bir_computeTheory



val _ = new_theory "bir_meta"

Theorem bir_eval_exp_eq_compute_exp:
    !env e v. bir_eval_exp env e v <=> (bir_compute_exp e env = SOME v)
Proof
    cheat
QED




val _ = export_theory ()
