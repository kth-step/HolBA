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




(*
bir_exp_subst (FEMPTY |+ (v,t)) e
*)


val bir_wp_simp_eval_subst_lemma1 = store_thm("bir_wp_simp_eval_subst_lemma1", ``
    !substs v v' vo' t e sm.
      (~(v' IN (bir_vars_of_exp t))) ==>
      (~(v' IN (bir_vars_of_exp e))) ==>
      (
       (bir_eval_exp (bir_exp_subst (substs |+ (v,t)) e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst (substs |+ (v,t)) e) (BEnv (FUPDATE sm (bir_var_name v', (bir_var_type v', vo')))))
      )
``,

(*
  REPEAT STRIP_TAC >>
*)
  cheat
);


val bir_wp_simp_eval_subst_lemma2 = store_thm("bir_wp_simp_eval_subst_lemma2", ``
    !v' substs v t e.
      (~(v' IN (bir_vars_of_exp t))) ==>
      (~(v' IN (bir_vars_of_exp e))) ==>
      (
       (!s. (bir_eval_exp (bir_exp_subst (substs |+ (v,t)) e) s) = bir_val_true)
       <=>
       (!s. (bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_Equal (BExp_Den v') t)) (bir_exp_subst (substs |+ (v,BExp_Den v')) e)) s) = bir_val_true)
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

(*
val bir_wp_simp_eval_subst_thm = store_thm("bir_wp_simp_eval_subst_thm", ``
    !v' prem substs v t e.
      (~(v' IN (bir_vars_of_exp t))) ==>
      (~(v' IN (bir_vars_of_exp e))) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst (substs |+ (v,t)) e) s = bir_val_true))
       <=>
       (!s. (
             (prem s)
             /\
             (bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den v') t) s = bir_val_true)
            )
            ==>
            (bir_eval_exp (bir_exp_subst (substs |+ (v,BExp_Den v')) e) s = bir_val_true)
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
*)


(* does this already exist? *)
(* memory load store updates *)





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


(*
val bir_wp_simp_and_eval_thm = store_thm("bir_wp_simp_and_eval_thm", ``
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
*)



(* should be in bir_exp_substitutionsTheory *)
(*
val bir_exp_subst_update_def = Define `
  (bir_exp_subst_update s1 FEMPTY = FEMPTY) /\
  (bir_exp_subst_update s1 (FUPDATE s2 (v,e)) =
     FUPDATE (bir_exp_subst_update s1 s2) (v, bir_exp_subst s1 e)
  )
`;
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

