open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory;
open bir_immTheory bir_typing_expTheory;
open bir_exp_memTheory bir_expTheory;
open bir_exp_immTheory bir_bool_expTheory;
open bir_exp_substitutionsTheory pred_setTheory;
open bir_exp_congruencesTheory
open HolBACoreSimps

(* This theory talks about tautologies and satisfiability of bir-expressions.  *)


val _ = new_theory "bir_exp_tautologies";


(* A tautology is an expression that holds in all enviroments. However,
   this general definition is for our purposes not really suitable.
   Let's instead consider also the type and that all vars need to
   be initialised. *)

val bir_exp_is_taut_def = Define `bir_exp_is_taut e <=> (
  bir_is_bool_exp e /\ (bir_var_set_is_well_typed (bir_vars_of_exp e)) /\
  (!env. (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
         (bir_eval_exp e env = SOME bir_val_true)))`;



(* An expression is satisfiable, if there is an environment satisfying it.*)
val bir_exp_is_satisfiable_def = Define `bir_exp_is_satisfiable e <=> (
  bir_is_bool_exp e /\ (bir_var_set_is_well_typed (bir_vars_of_exp e)) /\
  (?env. (bir_env_vars_are_initialised env (bir_vars_of_exp e) /\
         (bir_eval_exp e env = SOME bir_val_true))))`;




val bir_exp_satisfiable_taut_NEGATION = store_thm ("bir_exp_satisfiable_taut_NEGATION",
``!e. bir_is_bool_exp e /\ (bir_var_set_is_well_typed (bir_vars_of_exp e)) ==>
      (bir_exp_is_satisfiable e <=> ~(bir_exp_is_taut (BExp_UnaryExp BIExp_Not e)))``,

SIMP_TAC std_ss [bir_exp_is_taut_def, bir_is_bool_exp_REWRS,
  bir_exp_is_satisfiable_def, bir_vars_of_exp_def,
  bir_eval_exp_def] >>
REPEAT STRIP_TAC >>
ConseqConv.CONSEQ_CONV_TAC (K ConseqConv.EXISTS_EQ___CONSEQ_CONV) >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >> REPEAT STRIP_TAC >>
`?va. (bir_eval_exp e env = SOME va) /\ (type_of_bir_val va = (BType_Imm Bit1))` by (
METIS_TAC [bir_is_bool_exp_def, type_of_bir_exp_THM_with_init_vars]
) >>
`bir_val_is_Bool va` by METIS_TAC[bir_val_checker_TO_type_of, BType_Bool_def] >>
FULL_SIMP_TAC std_ss [bir_val_is_Bool_bool2b_DEF, bir_unary_exp_BOOL_OPER_EVAL,
   BVal_Imm_bool2b_EQ_TF_REWRS, bir_eval_unary_exp_def]);



(* These definitions are compatible with the congruences defined. *)

val bir_exp_is_taut_WEAK_CONG_IMPL = store_thm ("bir_exp_is_taut_WEAK_CONG_IMPL",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> (bir_exp_is_taut e1 ==> bir_exp_is_taut e2)``,

SIMP_TAC std_ss [bir_exp_is_taut_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  METIS_TAC[bir_env_oldTheory.bir_var_set_is_well_typed_SUBSET]
) >>
MP_TAC (Q.SPECL [`bir_vars_of_exp e2`, `bir_vars_of_exp e1`, `env`] bir_env_oldTheory.bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [bir_vars_of_exp_FINITE] >>
STRIP_TAC >>
rename1 `bir_env_vars_are_initialised env' (bir_vars_of_exp e1)` >>
`bir_eval_exp e2 env' = SOME bir_val_true` by METIS_TAC[] >>
`bir_eval_exp e2 env = bir_eval_exp e2 env'` suffices_by METIS_TAC[] >>

MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
ASM_REWRITE_TAC[]);


val bir_exp_is_taut_WEAK_CONG_IFF = store_thm ("bir_exp_is_taut_WEAK_CONG_IFF",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> bir_var_set_is_well_typed (bir_vars_of_exp e1) ==>
        (bir_exp_is_taut e1 <=> bir_exp_is_taut e2)``,

REPEAT STRIP_TAC >> EQ_TAC >- (
  METIS_TAC[bir_exp_is_taut_WEAK_CONG_IMPL]
) >>
FULL_SIMP_TAC std_ss [bir_exp_is_taut_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT STRIP_TAC >>
METIS_TAC[bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET]);


val bir_exp_is_taut_WEAK_CONG_IFF = store_thm ("bir_exp_is_taut_WEAK_CONG_IFF",
``!e1 e2. bir_exp_CONG e1 e2 ==>
        (bir_exp_is_taut e1 <=> bir_exp_is_taut e2)``,

FULL_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_exp_is_taut_def, bir_exp_CONG_def, bir_is_bool_exp_def]);


val bir_exp_is_satisfiable_WEAK_CONG_IMPL = store_thm ("bir_exp_is_satisfiable_WEAK_CONG_IMPL",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> (bir_exp_is_satisfiable e1 ==> bir_exp_is_satisfiable e2)``,

SIMP_TAC std_ss [bir_exp_is_satisfiable_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  METIS_TAC[bir_env_oldTheory.bir_var_set_is_well_typed_SUBSET]
) >>
Q.EXISTS_TAC `env` >>
METIS_TAC[bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET]);


val bir_exp_is_satisfiable_WEAK_CONG_IFF = store_thm ("bir_exp_is_satisfiable_WEAK_CONG_IFF",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> bir_var_set_is_well_typed (bir_vars_of_exp e1) ==>
        (bir_exp_is_satisfiable e1 <=> bir_exp_is_satisfiable e2)``,

REPEAT STRIP_TAC >> EQ_TAC >- (
  METIS_TAC[bir_exp_is_satisfiable_WEAK_CONG_IMPL]
) >>
FULL_SIMP_TAC std_ss [bir_exp_is_satisfiable_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`bir_vars_of_exp e2`, `bir_vars_of_exp e1`, `env`] bir_env_oldTheory.bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [bir_vars_of_exp_FINITE] >>
STRIP_TAC >>
rename1 `bir_env_vars_are_initialised env' (bir_vars_of_exp e1)` >>
`bir_eval_exp e2 env = bir_eval_exp e2 env'` suffices_by METIS_TAC[] >>
MATCH_MP_TAC bir_vars_of_exp_THM_EQ_FOR_VARS >>
ASM_REWRITE_TAC[]);


val bir_exp_is_satisfiable_CONG_IFF = store_thm ("bir_exp_is_satisfiable_CONG_IFF",
``!e1 e2. bir_exp_CONG e1 e2 ==>
        (bir_exp_is_satisfiable e1 <=> bir_exp_is_satisfiable e2)``,

FULL_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_exp_is_satisfiable_def, bir_exp_CONG_def, bir_is_bool_exp_def] >>
METIS_TAC[]);



(* Now the real important part.
   Abbreviate common parts of an expression with
   fresh vars while preserving whether it is a tautology.

   The idea is as follows:

   You have a large expression e_large and you need to check whether it is a
   tautology. You want to do this via an external tool (e.g. an SMT solver) and
   have a translation. However, the external oracle requires short inputs, i.e. it
   has trouble with repetition. Therefore, you want to abbreviate common parts of
   the expression by introducing additional variables.

   Step 1) in SML search for a subexpression "ve" that occurs multiple times
   Step 2) in SML generate a fresh var "v" and replace "ve" in "e_large" with "v" resulting in "e"
   Step 3) via simple evaluation show "bir_exp_subst1 v ve e = e_large"
   Step 4) use the theorem below to transforms "bir_exp_subst1 v ve e" into an
           bir expression using the new variable "v" to abbreviate "ve". In contrast
           to "bir_exp_subst1 v ve e" this is however a simple bir-expression without
           any fancy features

   Iterate steps 1-4 to get a small expression "e_small" such that
   bir_exp_is_taut e_large <=> bir_exp_is_taut e_small.

   Check "e_small" with external tool and then lift result to "e_large".
 *)

(* TODO: is not used at the moment anyways *)
val bir_exp_is_taut_INTRODUCE_FRESH_VAR_AS_ABBREV = store_thm ("bir_exp_is_taut_INTRODUCE_FRESH_VAR_AS_ABBREV",

``!v ve e ty. (bir_type_is_Imm ty /\
              (bir_var_type v = ty) /\
              (type_of_bir_exp ve = SOME ty) /\
              (bir_var_set_is_well_typed (v INSERT bir_vars_of_exp (bir_exp_subst1 v ve e))) /\
              (v IN (bir_vars_of_exp e)) /\
              ~(v IN (bir_vars_of_exp ve))) ==>

(bir_exp_is_taut (bir_exp_subst1 v ve e) <=>
bir_exp_is_taut (BExp_BinPred BIExp_LessOrEqual
                 (BExp_BinPred BIExp_Equal (BExp_Den v) ve)
                 e))``,

cheat);



val _ = export_theory();
