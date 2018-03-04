open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

load "pairLib";

val _ = new_theory "bir_wp_simp";









(* TODO: memory load store updates *)











val bir_wp_simp_eval_and_thm = store_thm("bir_wp_simp_eval_and_thm", ``
    !prem e1 e2.
      (!s. (prem s) ==> (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s = bir_val_true))
      <=>
      (
       (!s. (prem s) ==> (bir_eval_exp e1 s = bir_val_true))
       /\
       (!s. (prem s) ==> (bir_eval_exp e2 s = bir_val_true))
      )
``,

  cheat
);

val bir_wp_simp_eval_imp_thm = store_thm("bir_wp_simp_eval_imp_thm", ``
    !prem e1 e2.
      (
       !s. (prem s) ==>
           (bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e1) e2) s = bir_val_true)
      )
      <=>
      (
       !s. ((\s. (prem s) /\ (bir_eval_exp e1 s = bir_val_true)) s)
           ==>
           (bir_eval_exp e2 s = bir_val_true)
      )
``,

  cheat
);














(* does something like this already exist, or parts? *)
val bir_wp_simp_eval_subst_lemma = store_thm("bir_wp_simp_eval_subst_lemma1", ``
    !substs v' vo' e sm.
      (*(!v. (v IN (FDOM substs)) ==> (~(v' IN (bir_vars_of_exp (FAPPLY substs v))))) ==>*)
      (FEVERY (\(_, t). ~(v' IN (bir_vars_of_exp t))) substs) ==>
      (~(v' IN (bir_vars_of_exp e))) ==>
      (
       (bir_eval_exp (bir_exp_subst substs e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst substs e) (BEnv (FUPDATE sm (bir_var_name v', (bir_var_type v', vo')))))
      )
``,

(*
  REPEAT STRIP_TAC >>
*)
  cheat
);


(* TODO: should probably be somewhere else *)
val bir_exp_conj_from_list_def = Define `
  bir_exp_conj_from_list = FOLDL (\expa. \exp. BExp_BinExp BIExp_And expa exp) (BExp_Const (Imm1 1w))
`;

val bir_exp_varsubst_def = Define `
  bir_exp_varsubst vm = FUN_FMAP (\(x:bir_var_t). BExp_Den (FAPPLY vm x)) (FDOM vm)
`;

val bir_wp_simp_eval_subst_thm = store_thm("bir_wp_simp_eval_subst_thm", ``
    !vvtl vtm vvm bconj e prem.
      (vtm = FUPDATE_LIST FEMPTY (MAP (\(v, _, t). (v, t)) vvtl)) ==>
      (vvm = FUPDATE_LIST FEMPTY (MAP (\(v, v', _). (v, v')) vvtl)) ==>
      (bconj = bir_exp_conj_from_list (MAP (\(_, v', t). BExp_BinPred BIExp_Equal (BExp_Den v') t) vvtl)) ==>
      (EVERY (\v'. ~(v' IN (bir_vars_of_exp e)) /\ EVERY (\t. ~(v' IN (bir_vars_of_exp t))) (MAP (\(_, _, t). t) vvtl))) (MAP (\(_, v', _). v') vvtl) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst vtm e) s = bir_val_true))
       <=>
       (!s. ((prem s) /\
             (bir_eval_exp bconj s = bir_val_true)
            )
            ==>
            (bir_eval_exp (bir_exp_subst (bir_exp_varsubst vvm) e) s = bir_val_true)
       )
      )
``,

(*
  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

  ) >>
*)
  cheat
);
















(* TODO: should be in bir_exp_substitutionsTheory *)
(*
TODO: in the following is something wrong, this doesn't work, has to be fixed
*)
val bir_exp_subst_update_def = Define `
  bir_exp_subst_update s1 s2 = FUN_FMAP (\x. bir_exp_subst s1 (FAPPLY s2 x)) (FDOM s2)
`;

val bir_exp_subst_update_exec_thm = store_thm("bir_exp_subst_update_exec_thm", ``
    !s1 s2 e.
      (!s1. bir_exp_subst_update s1 FEMPTY = FEMPTY) /\
      (!s1 s2 v e. bir_exp_subst_update s1 (FUPDATE s2 (v,e)) =
           FUPDATE (bir_exp_subst_update s1 s2) (v, bir_exp_subst s1 e))
``,

(*finite_mapTheory.FDOM_FINITE*)
  cheat
);


val bir_exp_subst_bir_exp_subst_thm = store_thm("bir_exp_subst_bir_exp_subst_thm", ``
    !s1 s2 e.
      bir_exp_subst s1 (bir_exp_subst s2 e)
      =
      bir_exp_subst (bir_exp_subst_update s1 s2) (bir_exp_subst s1 e)
``,

  cheat
);


val _ = export_theory();

