open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory;
open bir_immTheory bir_typing_expTheory;
open bir_mem_expTheory bir_expTheory;
open bir_imm_expTheory bir_bool_expTheory;
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
         (bir_eval_exp e env = bir_val_true)))`;



(* An expression is satisfiable, if there is an environment satisfying it.*)
val bir_exp_is_satisfiable_def = Define `bir_exp_is_satisfiable e <=> (
  bir_is_bool_exp e /\ (bir_var_set_is_well_typed (bir_vars_of_exp e)) /\
  (?env. (bir_env_vars_are_initialised env (bir_vars_of_exp e) /\
         (bir_eval_exp e env = bir_val_true))))`;




val bir_exp_satisfiable_taut_NEGATION = store_thm ("bir_exp_satisfiable_taut_NEGATION",
``!e. bir_is_bool_exp e /\ (bir_var_set_is_well_typed (bir_vars_of_exp e)) ==>
      (bir_exp_is_satisfiable e <=> ~(bir_exp_is_taut (BExp_UnaryExp BIExp_Not e)))``,

SIMP_TAC std_ss [bir_exp_is_taut_def, bir_is_bool_exp_REWRS,
  bir_exp_is_satisfiable_def, bir_vars_of_exp_def,
  bir_eval_exp_def] >>
REPEAT STRIP_TAC >>
ConseqConv.CONSEQ_CONV_TAC (K ConseqConv.EXISTS_EQ___CONSEQ_CONV) >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >> REPEAT STRIP_TAC >>

`bir_val_is_Bool (bir_eval_exp e env)` by METIS_TAC[bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL,
  bir_is_bool_exp_env_def] >>
FULL_SIMP_TAC std_ss [bir_val_is_Bool_bool2b_DEF, bir_unary_exp_BOOL_OPER_EVAL,
   BVal_Imm_bool2b_EQ_TF_REWRS, bir_eval_unary_exp_def]);



(* These definitions are compatible with the congruences defined. *)

val bir_exp_is_taut_WEAK_CONG_IMPL = store_thm ("bir_exp_is_taut_WEAK_CONG_IMPL",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> (bir_exp_is_taut e1 ==> bir_exp_is_taut e2)``,

SIMP_TAC std_ss [bir_exp_is_taut_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  METIS_TAC[bir_var_set_is_well_typed_SUBSET]
) >>
MP_TAC (Q.SPECL [`bir_vars_of_exp e2`, `bir_vars_of_exp e1`, `env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [bir_vars_of_exp_FINITE] >>
STRIP_TAC >>
rename1 `bir_env_vars_are_initialised env' (bir_vars_of_exp e1)` >>
`bir_eval_exp e2 env' = bir_val_true` by METIS_TAC[] >>
`bir_eval_exp e2 env = bir_eval_exp e2 env'` suffices_by METIS_TAC[] >>

MATCH_MP_TAC bir_vars_of_exp_THM >>
METIS_TAC[bir_env_read_EQ_lookup_IMPL]);


val bir_exp_is_taut_WEAK_CONG_IFF = store_thm ("bir_exp_is_taut_WEAK_CONG_IFF",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> bir_var_set_is_well_typed (bir_vars_of_exp e1) ==>
        (bir_exp_is_taut e1 <=> bir_exp_is_taut e2)``,

REPEAT STRIP_TAC >> EQ_TAC >- (
  METIS_TAC[bir_exp_is_taut_WEAK_CONG_IMPL]
) >>
FULL_SIMP_TAC std_ss [bir_exp_is_taut_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT STRIP_TAC >>
METIS_TAC[bir_env_vars_are_initialised_SUBSET]);


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
  METIS_TAC[bir_var_set_is_well_typed_SUBSET]
) >>
Q.EXISTS_TAC `env` >>
METIS_TAC[bir_env_vars_are_initialised_SUBSET]);


val bir_exp_is_satisfiable_WEAK_CONG_IFF = store_thm ("bir_exp_is_satisfiable_WEAK_CONG_IFF",
``!e1 e2. bir_exp_CONG_WEAK e1 e2 ==> bir_var_set_is_well_typed (bir_vars_of_exp e1) ==>
        (bir_exp_is_satisfiable e1 <=> bir_exp_is_satisfiable e2)``,

REPEAT STRIP_TAC >> EQ_TAC >- (
  METIS_TAC[bir_exp_is_satisfiable_WEAK_CONG_IMPL]
) >>
FULL_SIMP_TAC std_ss [bir_exp_is_satisfiable_def, bir_exp_CONG_WEAK_def, bir_is_bool_exp_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`bir_vars_of_exp e2`, `bir_vars_of_exp e1`, `env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>
ASM_SIMP_TAC std_ss [bir_vars_of_exp_FINITE] >>
STRIP_TAC >>
rename1 `bir_env_vars_are_initialised env' (bir_vars_of_exp e1)` >>
`bir_eval_exp e2 env = bir_eval_exp e2 env'` suffices_by METIS_TAC[] >>
MATCH_MP_TAC bir_vars_of_exp_THM >>
METIS_TAC[bir_env_read_EQ_lookup_IMPL]);


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

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exp_is_taut_def, bir_is_bool_exp_def,
  bir_is_bool_exp_def, type_of_bir_exp_def, pairTheory.pair_case_thm,
  bir_vars_of_exp_def, UNION_IDEMPOT, GSYM UNION_ASSOC,
  bir_eval_exp_def, bir_exp_subst1_TYPE_EQ] >>
Cases_on `type_of_bir_exp e` >> (
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [BType_Bool_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >>
rename1 `BType_Imm s` >>
REPEAT BasicProvers.VAR_EQ_TAC >>
Q.ABBREV_TAC `vs = bir_vars_of_exp (bir_exp_subst1 v ve e)` >>
Q.SUBGOAL_THEN `({v} UNION (bir_vars_of_exp ve UNION bir_vars_of_exp e)) = (v INSERT vs)`
  SUBST1_TAC >- (
  Q.UNABBREV_TAC `vs` >>
  ASM_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS, EXTENSION, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
    IN_DIFF] >>
  METIS_TAC[]
) >>
`~(v IN vs)` by (
  Q.UNABBREV_TAC `vs` >>
  ASM_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS, IN_UNION, IN_DIFF, IN_INSERT]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_var_set_is_well_typed_INSERT] >>
`(bir_vars_of_exp e SUBSET (v INSERT vs)) /\ (bir_vars_of_exp ve SUBSET vs)` by (
  Q.UNABBREV_TAC `vs` >>
  ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, bir_exp_subst1_USED_VARS,
    IN_UNION, IN_DIFF, NOT_IN_EMPTY]
) >>
`!v'. (bir_var_name v' = bir_var_name v) ==> ~(v' IN vs)` by (
  METIS_TAC[bir_var_eq_EXPAND]
) >>
Q.PAT_X_ASSUM `!v'. v' IN vs ==> _ ==> _` (K ALL_TAC) >>
`?vn. v = BVar vn (BType_Imm s)` by (
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [bir_var_type_def] >>
  METIS_TAC[]
) >>
REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC std_ss [bir_var_type_def, bir_env_read_def, bir_var_name_def,
  bir_env_vars_are_initialised_INSERT, bir_env_var_is_initialised_def, PULL_EXISTS,
  pairTheory.pair_case_thm, type_of_bir_val_EQ_ELIMS, bir_val_true_def,
  bir_val_TF_bool2b_DEF] >>
`!env. bir_env_vars_are_initialised env ((BVar vn (BType_Imm s)) INSERT vs) ==>
       bir_val_is_Bool (bir_eval_exp e env)` by (
   REPEAT STRIP_TAC >>
   MATCH_MP_TAC bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL >>
   FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_is_bool_exp_def] >>
   METIS_TAC[bir_env_vars_are_initialised_SUBSET]
) >>

`!env. bir_env_vars_are_initialised env vs ==>
       (?i'. (bir_eval_exp ve env = BVal_Imm i') /\ (type_of_bir_imm i' = s))` by (
   REPEAT STRIP_TAC >>
   `type_of_bir_val (bir_eval_exp ve env) = SOME (BType_Imm s)` by (
     METIS_TAC[type_of_bir_exp_THM_with_init_vars, bir_env_vars_are_initialised_SUBSET]
   ) >>
   FULL_SIMP_TAC (std_ss++QI_ss) [type_of_bir_val_EQ_ELIMS]
) >>
EQ_TAC >> REPEAT STRIP_TAC >| [
  `bir_val_is_Bool (bir_eval_exp e env)` by (
     Q.PAT_X_ASSUM `!env. _` MATCH_MP_TAC >>
     ASM_SIMP_TAC std_ss [bir_env_vars_are_initialised_INSERT,
       bir_env_var_is_initialised_def, type_of_bir_val_def, bir_var_name_def, bir_var_type_def]
  ) >>
  `?i'. (bir_eval_exp ve env = BVal_Imm i') /\ (type_of_bir_imm i' = s)` by METIS_TAC[] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_is_Bool_bool2b_DEF,
    bir_bin_pred_BOOL_OPER_EVAL, bir_bin_pred_Equal_REWR] >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `bir_eval_exp (bir_exp_subst1 (BVar vn (BType_Imm s)) ve e) env =
   BVal_Imm (Imm1 1w)` by METIS_TAC[] >>
  `bir_eval_exp (bir_exp_subst1 (BVar vn (BType_Imm s)) ve e) env =
   bir_eval_exp e env` by (
     MATCH_MP_TAC bir_exp_subst1_EVAL_EQ >>
     ASM_SIMP_TAC std_ss [bir_env_read_def, bir_var_name_def,
       pairTheory.pair_case_thm, bir_var_type_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [],


  `?i. (bir_eval_exp ve env = BVal_Imm i) /\ (type_of_bir_imm i = s)` by METIS_TAC[] >>
  Cases_on `env` >> rename1 `BEnv env_f` >>
  Q.ABBREV_TAC `env' = BEnv (env_f |+ (vn,  (BType_Imm s,SOME (BVal_Imm i))))` >>

  `!v. v IN vs ==> (bir_env_lookup (bir_var_name v) env' = bir_env_lookup (bir_var_name v) (BEnv env_f))` by (
     REPEAT STRIP_TAC >>
     Q.UNABBREV_TAC `env'` >>
     `vn <> bir_var_name v` by METIS_TAC[] >>
     FULL_SIMP_TAC std_ss [bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
  ) >>
  `!v. v IN vs ==> (bir_env_read v env' = bir_env_read v (BEnv env_f))` by (
     METIS_TAC [bir_env_read_EQ_lookup_IMPL]
  ) >>
  `bir_env_lookup vn env' = SOME (BType_Imm s,SOME (BVal_Imm i))` by (
    Q.UNABBREV_TAC `env'` >>
    ASM_SIMP_TAC std_ss [bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
  ) >>
  `bir_env_read (BVar vn (BType_Imm s)) env' = BVal_Imm i` by (
     ASM_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm,
       bir_var_name_def, bir_var_type_def]
  ) >>
  `bir_env_vars_are_initialised env' vs` by (
    FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def] >>
    REPEAT STRIP_TAC >>
    `bir_env_var_is_initialised (BEnv env_f) v` by METIS_TAC[] >>
    POP_ASSUM MP_TAC >>
    Cases_on `v` >>
    SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>
    METIS_TAC[bir_var_name_def]
  ) >>

  `bir_eval_exp ve env' = bir_eval_exp ve (BEnv env_f)` by (
     MATCH_MP_TAC bir_vars_of_exp_THM >> METIS_TAC[SUBSET_DEF]
  ) >>
  `bir_val_is_Bool (bir_eval_exp e env')` by (
     Q.PAT_X_ASSUM `!env. _` MATCH_MP_TAC >>
     ASM_SIMP_TAC std_ss [bir_env_vars_are_initialised_INSERT,
       bir_env_var_is_initialised_def, type_of_bir_val_def,
       bir_var_name_def, bir_var_type_def]
  ) >>

  Q.PAT_X_ASSUM `!env i. _ ==> _` (MP_TAC o Q.SPECL [`env'`, `i`]) >>
  FULL_SIMP_TAC std_ss [bir_eval_bin_pred_REWRS, bir_bin_pred_Equal_REWR,
    bir_val_is_Bool_bool2b_DEF, type_of_bool2b, bir_bin_pred_BOOL_OPER_EVAL,
    bir_val_t_11, bool2b_EQ_IMM1_ELIMS] >>
  FULL_SIMP_TAC std_ss [bool2b_def, bool2w_def] >>
  `(bir_eval_exp (bir_exp_subst1 (BVar vn (BType_Imm s)) ve e) (BEnv env_f) =
    bir_eval_exp (bir_exp_subst1 (BVar vn (BType_Imm s)) ve e) env') /\
   (bir_eval_exp (bir_exp_subst1 (BVar vn (BType_Imm s)) ve e) env' =
    bir_eval_exp e env')` suffices_by METIS_TAC[] >>

  CONJ_TAC >| [
    MATCH_MP_TAC bir_vars_of_exp_THM >>
    ASM_SIMP_TAC std_ss [],

    MATCH_MP_TAC bir_exp_subst1_EVAL_EQ >>
    ASM_SIMP_TAC std_ss [bir_env_read_def]
  ]
]);



val _ = export_theory();
