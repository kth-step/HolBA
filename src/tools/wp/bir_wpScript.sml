(* From BIR core: *)
open bir_programTheory bir_typing_progTheory bir_envTheory
     bir_auxiliaryTheory bir_valuesTheory bir_expTheory
     bir_exp_immTheory;

(* From BIR lib: *)
open bir_program_blocksTheory bir_program_terminationTheory
     bir_program_valid_stateTheory bir_exp_substitutionsTheory
     bir_bool_expTheory bir_program_env_orderTheory
     bir_program_multistep_propsTheory;

open HolBACoreSimps;

load "pairLib";

val _ = new_theory "bir_wp";

(*
   -------------------------------------------------------------
                    SOME LEMMATA & DEFINITIONS
   -------------------------------------------------------------
*)

val bir_mk_bool_val_true_thm = prove(
  ``!v1.
      (bir_mk_bool_val v1 = bir_val_true) = v1``,

RW_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF, 
               bir_val_false_def, bir_val_true_def, word1_distinct]
);

(*** Theorems to check bir_is_bool_exp_env ***)
(* Conditional rewrite *)
val bir_is_bool_exp_env_GSYM = prove(
  ``!env e.
      bir_is_bool_exp e ==>
      ((bir_env_vars_are_initialised env (bir_vars_of_exp e)) =
        bir_is_bool_exp_env env e)``,

RW_TAC std_ss [bir_is_bool_exp_env_def]
);

val bir_is_bool_exp_GSYM = prove(
  ``!ex.
      (type_of_bir_exp ex = SOME BType_Bool) =
        (bir_is_bool_exp ex)``,

RW_TAC std_ss [BType_Bool_def,GSYM bir_is_bool_exp_def]
);

val bir_env_vars_are_initialised_INTRO = prove(
  ``!e ope e1 e2.
      bir_env_vars_are_initialised e
        (bir_vars_of_exp (BExp_BinExp ope e1 e2)) ==>
      (bir_env_vars_are_initialised e (bir_vars_of_exp e1) /\
       bir_env_vars_are_initialised e (bir_vars_of_exp e2)
      )``,

REPEAT STRIP_TAC >>
RW_TAC std_ss [bir_is_bool_exp_env_REWRS,
               bir_is_bool_exp_env_def] >>
FULL_SIMP_TAC std_ss [bir_vars_of_exp_def,
                      bir_env_vars_are_initialised_UNION]
);

(* NOTE: Shouldn't "env" and "exp" swap place in this name, to
 * reflect bir_is_bool_exp_env_def? *)
val bir_is_bool_exp_env_INTRO = prove(
``!env ope e1 e2.
    bir_is_bool_exp_env env (BExp_BinExp ope e1 e2) ==>
    (bir_is_bool_exp_env env e1 /\ bir_is_bool_exp_env env e2)``,

REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS]
);

(* Add type condition *)
(* eval({e1/var}ex, en) = eval(ex, {eval(e1, en)/var} en)*)
val bir_eval_exp_subst1_env = prove(
``!ex en var ty e1.
    (?r. (bir_env_lookup var (BEnv en)) = SOME (ty, r)) ==>
    (bir_eval_exp ex
      (BEnv (en |+ (var,ty,SOME (bir_eval_exp e1 (BEnv en))))) =
      bir_eval_exp (bir_exp_subst1 (BVar var ty) e1 ex) (BEnv en)
    )``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Induct_on `ex` >> (
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_exp_subst1_REWRS]
) >>
(* Case not handled: BExp_Den *)
Cases_on `b = BVar var ty` >- (
  RW_TAC std_ss [bir_env_read_def, bir_var_name_def,
                 bir_env_lookup_def] >>
  EVAL_TAC
) >>
Cases_on `b` >>
Cases_on `var <> s` >- (
  FULL_SIMP_TAC std_ss [bir_eval_exp_def] >>
  EVAL_TAC >>
  FULL_SIMP_TAC std_ss []
) >>
subgoal `b' <> ty` >- (
  METIS_TAC[]
) >>
FULL_SIMP_TAC std_ss [bir_env_lookup_def] >>
EVAL_TAC >>
RW_TAC std_ss [] >>
CASE_TAC
);

val bir_env_vars_are_initialised_unary_INTRO = prove(
  ``!env ope ex.
      bir_env_vars_are_initialised env
        (bir_vars_of_exp (BExp_UnaryExp ope ex)) ==>
      bir_env_vars_are_initialised env (bir_vars_of_exp ex)``,

REPEAT STRIP_TAC >>
RW_TAC std_ss [bir_is_bool_exp_env_REWRS,
               bir_is_bool_exp_env_def] >>
FULL_SIMP_TAC std_ss [bir_vars_of_exp_def,
                      bir_env_vars_are_initialised_UNION]
);

val bir_bool_values = store_thm("bir_bool_values",
  ``!env ex.
      bir_env_vars_are_initialised env (bir_vars_of_exp ex) ==>
      (bir_is_bool_exp ex ==>
       (((bir_eval_exp ex env) = bir_val_false) \/
        ((bir_eval_exp ex env) = bir_val_true)
       )
      )``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_def] >>
IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
Cases_on `(bir_eval_exp ex env)` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_val_def] >> (
    rename1 `(BVal_Imm b = bir_val_false)` >>
    Cases_on `b` >- (
      SUBGOAL_THEN
        ``!c.
            ((BVal_Imm (Imm1 c)) = bir_val_true) \/
            ((BVal_Imm (Imm1 c)) = bir_val_false)``
        (fn thm => METIS_TAC [thm]) >- (
           FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++
                          wordsLib.WORD_BIT_EQ_ss)
             [bir_val_true_def, bir_val_false_def] >>
           METIS_TAC []
        )
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_imm_def]
  )
)
);

val bit1_neg = store_thm("bit1_neg",
  ``(~(0w:word1) = 1w) /\ (~(1w:word1) = 0w)``,

SIMP_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_BIT_EQ_ss) []
);

(* If BIR And evaluates to BIR True, both conjuncts must have been
 * BIR True, assuming both conjunct are of the same Immtype. *)
val bir_exp_and_true = store_thm("bir_exp_and_true",
  ``!b b'.
    (type_of_bir_imm b = type_of_bir_imm b') ==>
    (bir_bin_exp BIExp_And b' b = Imm1 1w) ==>
    ((b' = Imm1 1w) /\ (b = Imm1 1w))``,
  
(* First, which immtypes can b and b' have? There is only one
 * relevant case: Bit1, Bit1. *)
Cases >> Cases >- (
  RW_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_BIT_EQ_ss)
         [bir_bin_exp_REWRS, bir_bin_exp_GET_OPER_def] >>
  METIS_TAC []
) >>
(* Rest of cases can be handled by this. The two last theorems
 * handle cases where the immediate types are equal. *)
SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_imm_def,
                                 bir_bin_exp_REWRS,
                                 bir_bin_exp_GET_OPER_def]
);

(* BIR And is equivalent to HOL conjunction of two propositions. *)
val bir_and_equiv = store_thm("bir_and_equiv",
  ``!env ex1 ex2.
      (bir_eval_exp ex1 env = bir_val_true) /\
        (bir_eval_exp ex2 env = bir_val_true) <=>
      (bir_eval_exp (BExp_BinExp BIExp_And ex1 ex2) env =
         bir_val_true
      )``,

REPEAT GEN_TAC >>
EQ_TAC >| [
  REPEAT STRIP_TAC >>
  ASM_SIMP_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_BIT_EQ_ss)
               [bir_eval_exp_def, bir_val_true_def,
                bir_eval_bin_exp_def, bir_bin_exp_def,
                bir_bin_exp_GET_OPER_def],

  (* We need to make the same proof for both conjuncts. *)
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_val_true_def] >>
    (* Here, we must look at the options for the arguments of
     * the BIR conjunction. *)
    Cases_on `(bir_eval_exp ex1 env)` >>
    Cases_on `(bir_eval_exp ex2 env)` >> (
      (* All the garbage cases solved by below row: *)
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_eval_bin_exp_REWRS]
    ) >>
    (* Case where both conjuncts evaluate to Imm is the relevant
     * one: *)
    rename1 `type_of_bir_imm b <> type_of_bir_imm b'` >>
    Cases_on `type_of_bir_imm b <> type_of_bir_imm b'` >> (
      (* Case of non-equal Imm type trivially resolved here... *)
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    (* ... while equal case requires a small lemma in addition. *)
    METIS_TAC [bir_exp_and_true]
  )
]
);

(* A BIR disjunction implies the equivalent HOL disjunction. *)
val bir_disj_impl = store_thm("bir_disj_impl",
  ``!env ex1 ex2.
      ((bir_eval_exp (BExp_BinExp BIExp_Or ex1 ex2) env =
        bir_val_true) ==>
      ((bir_eval_exp ex1 env = bir_val_true) \/
       (bir_eval_exp ex2 env = bir_val_true))
      )``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++
               wordsLib.WORD_BIT_EQ_ss)
              [bir_val_true_def, bir_eval_exp_def,
               bir_eval_bin_exp_def, bir_bin_exp_def,
               bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
Cases_on `bir_eval_exp ex1 env` >>
Cases_on `bir_eval_exp ex2 env` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_eval_bin_exp_def]
) >>
Cases_on `type_of_bir_imm b <> type_of_bir_imm b'` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_eval_bin_exp_def]
) >>
Cases_on `b` >> Cases_on `b'` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_eval_bin_exp_def] >>
  blastLib.FULL_BBLAST_TAC
)
);

(* BIR negation is equivalent to HOL negation, under the
 * circumstances of the expression being Boolean and all its
 * variables being initialised. *)
val bir_not_equiv = store_thm("bir_not_equiv",
  ``!env ex.
      bir_env_vars_are_initialised env (bir_vars_of_exp ex) ==>
      bir_is_bool_exp ex ==>
      (~(bir_eval_exp ex env = bir_val_true) <=>
        (bir_eval_exp (BExp_UnaryExp BIExp_Not ex) env =
          bir_val_true)
      )``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_bool_values >>
FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++
               wordsLib.WORD_BIT_EQ_ss)
              [bir_eval_exp_def, bir_val_true_def,
               bir_val_false_def, bir_eval_unary_exp_def,
               bir_unary_exp_def, bir_unary_exp_GET_OPER_def]
);

(* If the BIR negation of a value evaluates to BIR True, then said
 * value itself must evaluate to BIR False. *)
val bir_neg_val_true = store_thm("bir_neg_val_true",
  ``!env ex.
      (bir_eval_exp (BExp_UnaryExp BIExp_Not ex) env =
        bir_val_true) <=>
      (bir_eval_exp ex env = bir_val_false)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_eval_exp_def,
                      bir_val_true_def, bir_val_false_def] >>
Cases_on `(bir_eval_exp ex env)` >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [],

  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    SIMP_TAC (bool_ss++wordsLib.WORD_ss++wordsLib.WORD_BIT_EQ_ss) []
  ),

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

val bir_disj1_false = store_thm("bir_disj1_false",
  ``!ex env.
      (bir_eval_bin_exp BIExp_Or bir_val_false (bir_eval_exp ex env)
        = bir_val_true) ==>
      (bir_eval_exp ex env = bir_val_true)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def,
                                      bir_val_false_def] >>
Cases_on `(bir_eval_exp ex env)` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `type_of_bir_imm b` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `b` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_bin_exp_def]
) >>
blastLib.FULL_BBLAST_TAC
);

(*
   -------------------------------------------------------------
                      Single basic statements
   -------------------------------------------------------------
*)

(* In summary: a valid status must be Running or
 * AssumptionViolated. *)
val bir_is_valid_status_def = Define `
  bir_is_valid_status state = 
    (state.bst_status <> BST_Failed) /\
    (!l. state.bst_status <> BST_JumpOutside l) /\
    (!v. state.bst_status <> BST_Halted v) /\
    (state.bst_status <> BST_AssertionViolated)`;

(* The pre- and postcondition of the Hoare triple. *)
val bir_pre_post_def = Define `
  bir_pre_post s pre s' post =
    bir_is_bool_exp_env s.bst_environ pre ==>
    (
      (bir_is_valid_status s /\
       (bir_eval_exp pre (s.bst_environ) = bir_val_true)
      ) /\
      (s.bst_status = BST_Running)
    ) ==>
    (
      (bir_is_bool_exp_env s'.bst_environ post /\
        (bir_is_valid_status s' /\
          (bir_eval_exp post (s'.bst_environ) = bir_val_true)
        ) \/
        (s'.bst_status = BST_AssumptionViolated)
      )
    )`;

(* Hoare triple for the execution of one basic BIR statement. *)
val bir_exec_stmtB_triple_def = Define `
  bir_exec_stmtB_triple stmt pre post =
    !s s' obs.
      (* Note: Variable initialisation is actually not required by,
       * for example, Assert.
       * This could perhaps be added to the different statements
       * individually as needed. *)
      bir_env_vars_are_initialised s.bst_environ
        (bir_vars_of_stmtB stmt) ==>
      (bir_exec_stmtB stmt s = (obs, s')) ==>
      bir_pre_post s pre s' post`;

(* Theorem stating the soundness of the precondition e /\ Q for the
 * statement Assert e, with the postcondition Q. *)
(* {e /\ Q} Assert e {Q} *)
val bir_triple_exec_stmtB_assert_thm =
  store_thm("bir_triple_exec_stmtB_assert_thm",
  ``!ex post.
      bir_exec_stmtB_triple (BStmt_Assert ex)
                            (BExp_BinExp BIExp_And ex post) post``,

REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [] >>
(* Obtain that ex holds in the initial state from bir_and_equiv *)
SUBGOAL_THEN
  ``bir_eval_exp ex s.bst_environ = bir_val_true``
  (fn thm => ASSUME_TAC thm) >- (
  METIS_TAC [bir_and_equiv]
) >>
(* ... which with the below theorems gives that s = s' from
 * evaluating execution. *)
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                      bir_exec_stmt_assert_def,
                      bir_dest_bool_val_TF] >>
SUBGOAL_THEN
  ``bir_eval_exp post s.bst_environ = bir_val_true``
  (fn thm => ASSUME_TAC thm) >- (
  METIS_TAC [bir_status_t_nchotomy, bir_and_equiv]
) >>
REV_FULL_SIMP_TAC std_ss [] >>
METIS_TAC [bir_is_bool_exp_env_INTRO]
);

(* Theorem stating the soundness of the precondition ~e \/ Q for the
 * statement Assume e, with the postcondition Q. *)
(* {~e \/ Q} Assume e {Q} *)
val bir_triple_exec_stmtB_assume_thm =
  store_thm("bir_triple_exec_stmtB_assume_thm",
  ``!ex post.
      bir_is_well_typed_stmtB (BStmt_Assume ex) ==>
      bir_exec_stmtB_triple (BStmt_Assume ex)
                            (BExp_BinExp BIExp_Or
                              (BExp_UnaryExp BIExp_Not ex) post
                            ) post``,

REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_eval_exp (BExp_UnaryExp BIExp_Not ex) s.bst_environ =
            bir_val_true` >| [
  (* If ~ex holds, that means ex evaluates to BIR False. *)
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                        bir_exec_stmt_assume_def,
                        bir_neg_val_true, bir_dest_bool_val_TF] >>
  (* If ex evaluates to BIR False, then s' will have status
   * AssumptionViolated. *)
  SUBGOAL_THEN
    ``s'.bst_status = BST_AssumptionViolated``
    (fn thm => ASSUME_TAC thm) >- (
    Cases_on `s` >>
    RW_TAC (std_ss++holBACore_ss) []
  ) >>
  IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def],

  (* If ~ex does not hold, and if ex is Boolean, then ex must
   * hold. *)
  IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def,
                        bir_neg_val_true] >>
  IMP_RES_TAC bir_env_vars_are_initialised_unary_INTRO >>
  FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def] >>
  FULL_SIMP_TAC std_ss [BType_Bool_def,
                        GSYM bir_is_bool_exp_def] >>
  SUBGOAL_THEN
    ``bir_eval_exp ex s.bst_environ = bir_val_true``
    (fn thm => ASSUME_TAC thm) >- (
       PAT_ASSUM ``bir_env_vars_are_initialised
                     s.bst_environ  (bir_vars_of_exp ex)``
         (fn thm1 => (
            PAT_ASSUM ``bir_is_bool_exp ex``
              (fn thm2 => 
                ASSUME_TAC (
                  HO_MATCH_MP (HO_MATCH_MP bir_bool_values thm1)
                              thm2
                )
              )
         )) >>
       FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++
                      wordsLib.WORD_BIT_EQ_ss)
                     [bir_eval_unary_exp_def, bir_neg_val_true,
                      bir_val_false_def, bir_val_true_def,
                      bit1_neg] >>
       FULL_SIMP_TAC std_ss []
  ) >>
  (* We evaluate execution... *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtB_def,
                                        bir_exec_stmt_assume_def,
                                        bir_dest_bool_val_TF] >>
  (* If ex holds, then by the original assumption (~ex) \/ post,
   * post must also hold. *)
  SUBGOAL_THEN
    ``bir_eval_exp post s.bst_environ = bir_val_true``
    (fn thm => ASSUME_TAC thm) >- (
    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_def,
                              bir_eval_unary_exp_def,
                              bir_unary_exp_def,
                              bir_unary_exp_GET_OPER_def,
                              bir_val_false_def, bir_val_true_def,
                              bir_disj1_false,
                              bit1_neg]
  ) >>
  (* Everything is in place, just finish this however you like,
   * depending on which style of exposition you prefer. *)
  Cases_on `s` >> Cases_on `s'` >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

(* Theorem stating the soundness of the precondition {e/v}Q for
 * the statement Assign v:=e, with the postcondition Q. *)
(* {{e/v}Q} Assign v:=e {Q} *)
val bir_triple_exec_stmtB_assign_thm =
  store_thm("bir_triple_exec_stmtB_assign_thm",
  ``!v ex post.
      bir_is_well_typed_stmtB (BStmt_Assign v ex) ==>
      bir_is_bool_exp post ==>
      bir_exec_stmtB_triple (BStmt_Assign v ex) 
        (bir_exp_subst1 v ex post) post``,

REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* 1. Resolve effect of execution *)
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                      bir_exec_stmt_assign_def,
                      bir_env_write_def,
                      (GEN_ALL o SYM)
                        bir_env_var_is_declared_ALT_DEF] >>
(*    Prove that v is declared *)
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      bir_env_vars_are_initialised_INSERT] >>
REV_FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_weaken] >>
(*    Resolve the effects of bir_env_update *)
Cases_on `v` >>
Cases_on `s.bst_environ` >>
FULL_SIMP_TAC std_ss [bir_var_name_def,
                      bir_env_update_def, bir_var_type_def] >>
subgoal `type_of_bir_val (bir_eval_exp ex (BEnv f)) = SOME(b)` >- (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def,
                        bir_var_type_def,
                        type_of_bir_exp_THM_with_init_vars]
) >>
FULL_SIMP_TAC std_ss [LET_DEF, bir_env_var_is_initialised_def] >>
(* 2. Obtain the result of evaluating post in the environment of
 *    s'. *)
IMP_RES_TAC bir_eval_exp_subst1_env >>
PAT_X_ASSUM ``!ex.p`` (fn thm => ASSUME_TAC
                         (Q.SPECL [`post`, `ex`] thm)
                      ) >>
FULL_SIMP_TAC std_ss [bir_var_name_def, bir_var_type_def] >>
(*    Now, the effects of execution have been cleaned up in the
 *    assumptions.
 *
 * Split the goal into
 *   bir_is_bool_exp_env s' post
 * and
 *   bir_is_valid_status s'. *)
RW_TAC std_ss [] >| [
(* Consider the theorem
 *   bir_exp_substitutionsTheory.bir_exp_subst1_USED_VARS *)
(* Expand the goal *)
  Q.RENAME1_TAC `BVar id ty` >>
  FULL_SIMP_TAC pure_ss [bir_is_bool_exp_env_def] >>
  REWRITE_TAC [] >>
(* Now, it only remains to prove the variables of v' are
 * initialised in s'. *)
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
           [bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>
  Q.RENAME1_TAC `v2 IN bir_vars_of_exp post` >>
  Cases_on `v2 = BVar id ty` >- (
    ASM_REWRITE_TAC [bir_env_var_is_initialised_def,
                     bir_var_type_def, bir_var_name_def,
                     bir_env_lookup_def,
                     finite_mapTheory.FLOOKUP_UPDATE] >>
    METIS_TAC []
  ) >>
  Cases_on `bir_var_name v2 = id` >- (
    subgoal `bir_env_var_is_initialised (BEnv f) v2` >- (
      FULL_SIMP_TAC std_ss
        [bir_exp_subst1_USED_VARS,
         bir_env_vars_are_initialised_UNION] >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
                    [bir_env_vars_are_initialised_def,
                     pred_setTheory.DIFF_DEF]
    ) >>
    Cases_on `v2` >>
    FULL_SIMP_TAC std_ss [bir_var_name_def,
                          bir_env_var_is_initialised_def,
                          bir_var_type_def] >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss []
  ) >>

  Cases_on `v2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
                [bir_var_name_def, bir_env_var_is_initialised_def,
                 bir_env_lookup_def,
                 finite_mapTheory.FLOOKUP_UPDATE,
                 bir_env_vars_are_initialised_def] >>
  Q.RENAME1_TAC `BVar id2 ty2 IN bir_vars_of_exp post` >>
  subgoal `(BVar id2 ty2) IN
             bir_vars_of_exp (bir_exp_subst1 (BVar id ty)
                                             ex post)` >- (
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
                 [bir_exp_subst1_USED_VARS]
  ) >>
  METIS_TAC [bir_var_name_def],

  (* Valid status of s' can be proved directly. *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_status_def]
]
);

val bir_env_vars_are_initialised_observe_INSERT = prove(
  ``!e ec el obf.
      bir_env_vars_are_initialised e
        (bir_vars_of_stmtB (BStmt_Observe ec el obf)) ==>
      bir_env_vars_are_initialised e (bir_vars_of_exp ec)``,

REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      listTheory.LIST_TO_SET,
                      pred_setTheory.IMAGE_INSERT,
                      pred_setTheory.BIGUNION_INSERT,
                      bir_env_vars_are_initialised_UNION]
);

(* Theorem stating the soundness of the precondition Q for
 * the statement Observe ex, with the postcondition Q. *)
(* {Q} Observe ex {Q} *)
val bir_triple_exec_stmtB_observe_thm =
  store_thm("bir_triple_exec_stmtB_observe_thm",
  ``!ec el obf post.
      bir_is_well_typed_stmtB (BStmt_Observe ec el obf) ==>
      bir_is_bool_exp post ==>
      bir_exec_stmtB_triple (BStmt_Observe ec el obf) post post``,

REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* Prove that the observation condition is well typed *)
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,bir_exec_stmt_observe_def,
  bir_is_well_typed_stmtB_def, bir_is_bool_exp_GSYM] >>
IMP_RES_TAC bir_env_vars_are_initialised_observe_INSERT >>
REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                      bir_mk_bool_val_inv] >>
(* Two cases for for the observation condition *)
Cases_on `bir_eval_bool_exp ec s.bst_environ` >> (
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss []
)
);

val bir_wp_exec_stmtB_def = Define `
  (bir_wp_exec_stmtB (BStmt_Assert ex) post =
    (BExp_BinExp BIExp_And ex post)) /\
  (bir_wp_exec_stmtB (BStmt_Assume ex) post =
    (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post)) /\
  (bir_wp_exec_stmtB (BStmt_Assign v ex) post =
    (bir_exp_subst1 v ex post)) /\
  (bir_wp_exec_stmtB (BStmt_Observe ec el obf) post = post)`;

val bir_isnot_declare_stmt_def = Define `
  bir_isnot_declare_stmt stm = (~(?v . stm = (BStmt_Declare v)))`;

val bir_wp_exec_stmtB_sound_thm =
  store_thm("bir_wp_exec_stmtB_sound_thm",
  ``!stm post.
      bir_isnot_declare_stmt stm ==>
      bir_is_well_typed_stmtB stm ==>
      bir_is_bool_exp post ==>
      bir_exec_stmtB_triple stm (bir_wp_exec_stmtB stm post) post``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Cases_on `stm` >>
FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
                      bir_triple_exec_stmtB_assign_thm,
                      bir_triple_exec_stmtB_assert_thm,
                      bir_triple_exec_stmtB_assume_thm,
                      bir_triple_exec_stmtB_observe_thm,
                      bir_isnot_declare_stmt_def] >> (
  RW_TAC std_ss []
)
);

val bir_wp_exec_stmtB_bool_thm =
  store_thm("bir_wp_exec_stmtB_bool_thm",
  ``!stm post.
      bir_isnot_declare_stmt stm ==>
      bir_is_well_typed_stmtB stm ==>
      bir_is_bool_exp post ==>
      bir_is_bool_exp (bir_wp_exec_stmtB stm post)``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Cases_on `stm` >> (
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
                        bir_triple_exec_stmtB_assign_thm,
                        bir_triple_exec_stmtB_assert_thm,
                        bir_triple_exec_stmtB_assume_thm,
                        bir_triple_exec_stmtB_observe_thm,
                        bir_isnot_declare_stmt_def,
                        bir_is_well_typed_stmtB_def,
                        bir_is_bool_exp_GSYM,
                        bir_is_bool_exp_REWRS] >> (
    RW_TAC std_ss []
  ) >> (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_def,
                          bir_exp_subst1_TYPE_EQ]
  )
)
);

(*
   -------------------------------------------------------------
                    Multiple basic statements
   -------------------------------------------------------------
*)
(* Hoare triple for several basic statements *)
val bir_exec_stmtsB_triple_def = Define `
  bir_exec_stmtsB_triple stmts pre post =
    !s s' obs obs' c c'.
      (EVERY
        (\stmt.
          bir_env_vars_are_initialised s.bst_environ
            (bir_vars_of_stmtB stmt)
        ) stmts
      ) ==>
      (bir_exec_stmtsB stmts (obs, c, s) = (obs', c', s')) ==>
      (bir_pre_post s pre s' post)`;


val bir_wp_exec_stmtsB_def = Define `
  (bir_wp_exec_stmtsB [] post = post) /\
  (bir_wp_exec_stmtsB (stmt::stmts) post = 
    bir_wp_exec_stmtB stmt (bir_wp_exec_stmtsB stmts post)
  )`;

val bir_wp_exec_stmtsB_bool_thm =
  store_thm("bir_wp_exec_stmtsB_bool_thm",
  ``!stmts post.
      EVERY bir_is_well_typed_stmtB stmts ==>
      EVERY bir_isnot_declare_stmt stmts ==>
      bir_is_bool_exp post ==>
      bir_is_bool_exp (bir_wp_exec_stmtsB stmts post)``,

REPEAT GEN_TAC >>
Induct_on `stmts` >- (
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def,
                        bir_exec_stmtsB_triple_def,
                        bir_exec_stmtsB_def]
) >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def, listTheory.EVERY_DEF,
                      bir_wp_exec_stmtB_bool_thm]
);

val exec_preserves_initialized_vars_thm = prove(
  ``!r h st stmts.
      (r = bir_exec_stmtB_state (h:'a bir_stmt_basic_t) st) ==>
      (EVERY (\stmt:'a bir_stmt_basic_t.
               bir_env_vars_are_initialised st.bst_environ
                 (bir_vars_of_stmtB stmt)
             ) stmts
      ) ==>
      (EVERY (\stmt.
               bir_env_vars_are_initialised r.bst_environ
                 (bir_vars_of_stmtB stmt)
             ) stmts
      )``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
subgoal `!x. 
 (\stmt:'a bir_stmt_basic_t.
   bir_env_vars_are_initialised st.bst_environ
     (bir_vars_of_stmtB stmt)) x ==>
 (\stmt. bir_env_vars_are_initialised r.bst_environ
           (bir_vars_of_stmtB stmt)) x` >- (
  GEN_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  DISCH_TAC >>     
  MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO]
                 bir_env_vars_are_initialised_ORDER) >>
  Q.EXISTS_TAC `st.bst_environ` >>
  ASM_SIMP_TAC std_ss [bir_exec_stmtB_ENV_ORDER]
) >>

ASSUME_TAC (ISPECL [``(\stmt:'a bir_stmt_basic_t.
                        bir_env_vars_are_initialised st.bst_environ
                          (bir_vars_of_stmtB stmt))``,
                    ``(\stmt:'a bir_stmt_basic_t.
                        bir_env_vars_are_initialised r.bst_environ
                          (bir_vars_of_stmtB stmt))``]
                   listTheory.EVERY_MONOTONIC) >>
REV_FULL_SIMP_TAC std_ss []
);

val bir_assviol_exec_stmtsB =
  store_thm("bir_assviol_exec_stmtsB",
  ``!obs c s stmts.
      (s.bst_status = BST_AssumptionViolated) ==>
      (bir_exec_stmtsB stmts (obs, c, s) = (REVERSE obs, c, s))
  ``,

REPEAT GEN_TAC >>
Cases_on `stmts` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_stmtsB_def]
)
);

val bir_running_by_exclusion =
  store_thm("bir_running_by_exclusion",
  ``!s.
      bir_is_valid_status s ==>
      (s.bst_status <> BST_AssumptionViolated) ==>
      (s.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
Cases_on `s.bst_status` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_status_def]
);

val bir_wp_exec_stmtsB_sound_thm =
  store_thm("bir_wp_exec_stmtsB_sound_thm",
  ``!stmts post.
      EVERY bir_is_well_typed_stmtB stmts ==>
      EVERY bir_isnot_declare_stmt stmts ==>
      bir_is_bool_exp post ==>
      (bir_exec_stmtsB_triple stmts
         (bir_wp_exec_stmtsB stmts post) post
      )``,

  REPEAT GEN_TAC >>
  Induct_on `stmts` >-
  (
   FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def,
                         bir_exec_stmtsB_triple_def,
                         bir_exec_stmtsB_def, bir_pre_post_def]
  ) >>
  SIMP_TAC std_ss [bir_exec_stmtsB_triple_def, bir_pre_post_def] >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  (* Naming convention:
   * Initial state: s
   * Middle state (after execution of h): s'
   * Final state: s'' *)
  rename1 `bir_exec_stmtsB (h::stmts) (obs,c,s) = (obs',c',s'')` >>
  FULL_SIMP_TAC std_ss [listTheory.EVERY_DEF] >>
  (* First, obtain the effects of execution of h. *)
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def,
                        bir_state_is_terminated_def] >>
    Q.ABBREV_TAC `s't = bir_exec_stmtB h s` >>
    Cases_on `s't` >>
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    rename1 `bir_exec_stmtsB stmts (OPT_CONS q obs,SUC c,s') =
               (obs',c',s'')` >>
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def] >>
    Q.ABBREV_TAC `penult_wp = (bir_wp_exec_stmtsB stmts post)` >>
    (* Handle the first step *)
    ASSUME_TAC (Q.SPECL [`h`, `penult_wp`]
                        bir_wp_exec_stmtB_sound_thm) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    IMP_RES_TAC bir_wp_exec_stmtsB_bool_thm >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exec_stmtB_triple_def] >>
    PAT_X_ASSUM ``!s s' obs. p`` (fn thm =>
    ASSUME_TAC (Q.SPECL [`s`, `s'`, `q`] thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC std_ss [bir_pre_post_def] >| [
      Cases_on `s'.bst_status = BST_AssumptionViolated` >| [
        (* Case: AssumptionViolated in s'.
         * bir_exec_stmtsB is used to relate s'' to s', so you
         * should be able to prove this case easily. *)
        FULL_SIMP_TAC std_ss [bir_assviol_exec_stmtsB] >>
        REV_FULL_SIMP_TAC std_ss [],

        (* Case: Running in s. *)
        SUBGOAL_THEN ``s'.bst_status = BST_Running``
                     (fn thm => ASSUME_TAC thm) >- (
          FULL_SIMP_TAC std_ss [bir_running_by_exclusion]
        ) >>
        (* Use induction hypothesis *)
        FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>
        PAT_X_ASSUM ``!s s' obs obs' c c'. blah`` (fn thm =>
          ASSUME_TAC (Q.SPECL [`s'`, `s''`, `OPT_CONS q obs`,
                               `obs'`, `SUC c`, `c':num`] thm)) >>
        REV_FULL_SIMP_TAC std_ss [] >>
        (* Prove assumptions of induction hypothesis *)
        subgoal `s' = bir_exec_stmtB_state h s` >- (
          FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def]
        ) >>
        IMP_RES_TAC exec_preserves_initialized_vars_thm >>
        FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
        REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                          [bir_is_valid_status_def]
      ],

    FULL_SIMP_TAC std_ss [bir_assviol_exec_stmtsB] >>
    REV_FULL_SIMP_TAC std_ss []
  ]
);

(*
   -------------------------------------------------------------
             Whole blocks: basic and end statements
   -------------------------------------------------------------
*)
(* Hoare triple for a block *)
val bir_exec_block_jmp_triple_def = Define`
  bir_exec_block_jmp_triple p bl pre post l =
    !s l1 c1 s'.
      bir_env_vars_are_initialised s.bst_environ
                                   (bir_vars_of_block bl) ==>
      (bir_exec_block p bl s = (l1,c1,s')) ==>
      (s.bst_status = BST_Running) ==>
      bir_is_bool_exp_env s.bst_environ pre ==>
      (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
      (
        (bir_is_bool_exp_env s'.bst_environ post /\
         bir_is_valid_status s' /\ 
         (bir_eval_exp post (s'.bst_environ) = bir_val_true) /\
         (s'.bst_pc = bir_block_pc l)
        ) \/ (
         (s'.bst_status = BST_AssumptionViolated)
        )
      )
`;

val SUBSET_BIGUNION_IMAGE_thm = prove(
  ``!x s f.
      (x IN s) ==> ((f x) SUBSET (BIGUNION (IMAGE f s)))``,

SIMP_TAC pure_ss [pred_setTheory.IMAGE_DEF,
                  pred_setTheory.BIGUNION,
                  pred_setTheory.SUBSET_DEF] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
Q.EXISTS_TAC `f x` >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
Q.EXISTS_TAC `x` >>
METIS_TAC []
);

val bir_vars_are_initialized_block_then_every_stmts_thm = prove(
  ``!st bl.
      (bir_env_vars_are_initialised st.bst_environ
                                    (bir_vars_of_block bl)) ==>
      (EVERY
        (\stmt.
          bir_env_vars_are_initialised st.bst_environ
            (bir_vars_of_stmtB stmt)
        ) bl.bb_statements
      )``,

FULL_SIMP_TAC std_ss [bir_vars_of_block_def,
                      listTheory.EVERY_MEM] >>
REPEAT STRIP_TAC >>

METIS_TAC [bir_env_vars_are_initialised_UNION,
           SUBSET_BIGUNION_IMAGE_thm,
           bir_env_vars_are_initialised_SUBSET]
);

val bir_exec_block_jmp_triple_wp_thm =
  store_thm("bir_exec_block_jmp_triple_wp_thm",
  ``!p bl post l.
      bir_is_well_typed_block bl ==>
      EVERY bir_isnot_declare_stmt bl.bb_statements ==>
      bir_is_bool_exp post ==>
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l))) ==>
      MEM l (bir_labels_of_program p) ==>
      (bir_exec_block_jmp_triple p bl 
        (bir_wp_exec_stmtsB bl.bb_statements post) post l)``,

(* Expand definitions *)
SIMP_TAC std_ss [bir_exec_block_jmp_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "wp" is the weakest precondition of the block of basic
 * statements. *)
Q.ABBREV_TAC `wp = bir_wp_exec_stmtsB bl.bb_statements post` >>
ASSUME_TAC (Q.SPECL [`bl.bb_statements`, `post`]
                    bir_wp_exec_stmtsB_sound_thm
           ) >>
REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def,
                          bir_exec_stmtsB_triple_def] >>
(* Start resolving the effects of execution: *)
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
(* "ns" is the new state resulting from execution of the block of
 * basic BIR statements with initial state s. *)
Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,s)` >>
pairLib.PairCases_on `ns` >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
PAT_X_ASSUM ``!x. p``
            (fn thm =>
              ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:'a list`, `ns0`,
                                   `0:num`, `ns1`] thm
                         )
            ) >>
REV_FULL_SIMP_TAC std_ss
  [bir_vars_are_initialized_block_then_every_stmts_thm] >>
(* Now, we don't know if ns2 is Running or
 * AssumptionViolated. We will have to do a case split here. *)
Cases_on `ns2.bst_status <> BST_AssumptionViolated` >>
FULL_SIMP_TAC std_ss [bir_pre_post_def,
                      bir_state_is_terminated_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >| [
  (* Case 1: Status of ns2 is Running. *)
  ASSUME_TAC (SPEC ``ns2:bir_state_t`` bir_running_by_exclusion) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_def,
                        bir_eval_label_exp_def,
                        bir_exec_stmt_jmp_to_label_def] >>
  subgoal `(ns2 with bst_pc := bir_block_pc l).bst_status =
             ns2.bst_status` >- (
    RW_TAC (srw_ss()) []
  ) >>
  RW_TAC (srw_ss()) [],

  (* Case 2: Status of ns2 is AssumptionViolated. *)
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  subgoal `(ns2 with bst_pc := bir_block_pc l).bst_status =
             ns2.bst_status` >- (
    RW_TAC (srw_ss()) []
  ) >>
  RW_TAC (srw_ss()) []
]
);

val bir_exec_block_cjmp_triple_def = Define `
  bir_exec_block_cjmp_triple p bl pre post1 l1 post2 l2 =
    !s obs' c1 s'.
      bir_env_vars_are_initialised s.bst_environ
        (bir_vars_of_block bl) ==>
      (bir_exec_block p bl s = (obs',c1,s')) ==>
      (s.bst_status = BST_Running) ==>
      bir_is_bool_exp_env s.bst_environ pre ==>
      (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
      (bir_is_valid_status s' /\
       (
         (bir_is_bool_exp_env s'.bst_environ post1 /\
         (bir_eval_exp post1 (s'.bst_environ) = bir_val_true) /\
         (s'.bst_pc = bir_block_pc l1)
       ) \/ (
         bir_is_bool_exp_env s'.bst_environ post2 /\
         (bir_eval_exp post2 (s'.bst_environ) = bir_val_true) /\
         (s'.bst_pc = bir_block_pc l2)
       )
      ) \/ (
        (s'.bst_status = BST_AssumptionViolated)
      )
     )`;

val bir_exec_block_cjmp_triple_wp_thm =
  store_thm("bir_exec_block_cjmp_triple_wp_thm",
  ``!p bl e post1 l1 post2 l2.
      bir_is_well_typed_block bl ==>
      EVERY bir_isnot_declare_stmt bl.bb_statements ==>
      bir_is_bool_exp post1 ==>
      bir_is_bool_exp post2 ==>
      (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1)
                                            (BLE_Label l2)
                              )
      ) ==>
      MEM l1 (bir_labels_of_program p) ==>
      MEM l2 (bir_labels_of_program p) ==>
      (bir_exec_block_cjmp_triple p bl 
        (bir_wp_exec_stmtsB bl.bb_statements
            (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_Or
                (BExp_UnaryExp BIExp_Not e)
                post1
              ) (BExp_BinExp BIExp_Or e post2)
            )
        ) post1 l1 post2 l2)``,

(* Expand definitions *)
SIMP_TAC std_ss [bir_exec_block_cjmp_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "q1" is the weakest precondition of CJmp in case the expression
 * e holds, while "q2" is the converse case.
 * "post_stmts" is the collective weakest precondition of the CJmp
 * statement.
 * "wp" is the weakest precondition of the block of basic BIR
 * statements. *)
Q.ABBREV_TAC `q1 = (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e)
                     post1)` >> 
Q.ABBREV_TAC `q2 = (BExp_BinExp BIExp_Or e post2)` >>
Q.ABBREV_TAC `post_stmts = (BExp_BinExp BIExp_And q1 q2)` >> 
Q.ABBREV_TAC `wp = bir_wp_exec_stmtsB bl.bb_statements
                                      post_stmts` >>
(* We use the fact that the WP of basic statements is sound *)
ASSUME_TAC (Q.SPECL [`bl.bb_statements`, `post_stmts`]
                    bir_wp_exec_stmtsB_sound_thm) >>
REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def,
                          bir_exec_stmtsB_triple_def] >>
subgoal `bir_is_bool_exp post_stmts` >- (
  FULL_SIMP_TAC std_ss [Abbr `q1`, Abbr `q2`, Abbr `post_stmts`,
                        bir_is_bool_exp_REWRS,
                        bir_is_well_typed_stmtE_def, BType_Bool_def,
                        GSYM bir_is_bool_exp_def]
) >>
(* Evaluate the effects of execution *)
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,s)` >>
pairLib.PairCases_on `ns` >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
PAT_X_ASSUM ``!x. p`` (fn thm =>
  ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:'a list`, `ns0`, `0:num`,
                       `ns1`] thm)) >>
REV_FULL_SIMP_TAC std_ss
  [bir_vars_are_initialized_block_then_every_stmts_thm] >>
(* Here, we must make a case split on whether the status of
 * ns2 is AssumptionViolated or not. *)
Cases_on `ns2.bst_status <> BST_AssumptionViolated` >>
FULL_SIMP_TAC std_ss [bir_pre_post_def,
                      bir_state_is_terminated_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >| [
  (* Case 1: Status of ns2 is Running. *)
  ASSUME_TAC (SPEC ``ns2:bir_state_t`` bir_running_by_exclusion) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC std_ss [] >>
  Q.ABBREV_TAC `st2 = (bir_exec_stmtE p
                        (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))
                        ns2)` >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def,
                        bir_exec_stmt_cjmp_def] >>
  (* Prove that bir_is_bool_exp e *)
  subgoal `bir_is_bool_exp_env ns2.bst_environ e` >- (
    FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
    REV_FULL_SIMP_TAC std_ss [Abbr `post_stmts`, Abbr `q1`,
                              Abbr `q2`] >>
    IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
    IMP_RES_TAC bir_is_bool_exp_env_INTRO
  ) >>
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                        bir_mk_bool_val_inv] >>
  REV_FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
  (* Proves that since
   *   eval_bool (q1 /\ q2)
   * then
   *   eval_bool q1 /\ eval_bool q2 *)
  FULL_SIMP_TAC std_ss [Abbr `post_stmts`] >>
  IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                        bir_mk_bool_val_true_thm,
                        bir_eval_bool_exp_BExp_BinExp_REWRS] >>
  Cases_on `bir_eval_bool_exp e ns2.bst_environ` >- (
    FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def,
                          bir_eval_label_exp_def,
                          bir_exec_stmt_jmp_to_label_def] >>
    REV_FULL_SIMP_TAC std_ss [Abbr `st2`,
                              bir_state_is_terminated_def] >>
    RW_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [Abbr `q1`] >>
    IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
    subgoal `~(bir_eval_bool_exp (BExp_UnaryExp BIExp_Not e)
                                 ns2.bst_environ) ` >- (
      FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_UnaryExp_REWRS]
    ) >>
    FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS,
                          bir_eval_bool_exp_INTRO,
                          bir_mk_bool_val_true_thm]
  ) >>
  (* Remaining case: e does not hold *)
  FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def,
                        bir_eval_label_exp_def,
                        bir_exec_stmt_jmp_to_label_def] >>
  REV_FULL_SIMP_TAC std_ss [Abbr `st2`,
                            bir_state_is_terminated_def] >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [Abbr `q2`] >>
  IMP_RES_TAC bir_is_bool_exp_env_INTRO >>
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS,
                        bir_eval_bool_exp_INTRO,
                        bir_mk_bool_val_true_thm],

  (* Case 2: Status of ns2 is AssumptionViolated. *)
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  subgoal `(ns2 with bst_pc := bir_block_pc l).bst_status =
             ns2.bst_status` >- (
    RW_TAC (srw_ss()) []
  ) >>
  RW_TAC (srw_ss()) []
]
);


(*
   -------------------------------------------------------------
             Entire program up to label (DAG of blocks)
   -------------------------------------------------------------
*)
  
val bir_exec_to_labels_triple_def = Define `
  bir_exec_to_labels_triple p l ls pre post =
  !s r.
    bir_env_vars_are_initialised s.bst_environ
                                 (bir_vars_of_program p) ==>
    ((s.bst_pc.bpc_index = 0) /\ (s.bst_pc.bpc_label = l)) ==>
    (s.bst_status = BST_Running) ==>
    bir_is_bool_exp_env s.bst_environ pre ==>
    (bir_eval_exp pre (s.bst_environ) = bir_val_true) ==>
    ((bir_exec_to_labels ls p s) = r) ==>
    (?l1 c1 c2 s'.
      (
        (r = BER_Ended l1 c1 c2 s') /\
        (s'.bst_status = BST_Running) /\
        bir_is_bool_exp_env s'.bst_environ post /\
        (bir_eval_exp post (s'.bst_environ) = bir_val_true) /\
        ((s'.bst_pc.bpc_index = 0) /\ (s'.bst_pc.bpc_label IN ls))
      ) \/ (
        (s'.bst_status = BST_AssumptionViolated)
      )
    )`;

val bir_declare_free_prog_def = Define `
  bir_declare_free_prog (BirProgram l) =
  !bl.
    MEM bl l ==>
    EVERY bir_isnot_declare_stmt bl.bb_statements`;

val bir_declare_free_prog_exec_def = Define `
  (bir_declare_free_prog_exec (BirProgram []) = T) /\
  (bir_declare_free_prog_exec (BirProgram (h::l)) =
    ((EVERY bir_isnot_declare_stmt h.bb_statements) /\
     (bir_declare_free_prog_exec (BirProgram l))
    )
  )`;

val bir_declare_free_prog_exec_eq_thm =
  store_thm("bir_declare_free_prog_exec_eq_thm",
  ``!p.
      (bir_declare_free_prog p = bir_declare_free_prog_exec p)``,

Cases_on `p` >> Q.RENAME1_TAC `(BirProgram bls)` >>
Induct_on `bls` >- (
  REWRITE_TAC [bir_declare_free_prog_def,
               bir_declare_free_prog_exec_def, listTheory.MEM]
) >>
REWRITE_TAC [bir_declare_free_prog_def,
             bir_declare_free_prog_exec_def, listTheory.MEM] >>
STRIP_TAC >> EQ_TAC >- (
  REPEAT STRIP_TAC >> (
    METIS_TAC [listTheory.MEM, bir_declare_free_prog_def]
  )
) >>
REPEAT STRIP_TAC >> (
  METIS_TAC [bir_declare_free_prog_def]
)
);

val bir_env_vars_are_initialised_prog_block_thm = prove(
  ``!p l bl env.
      bir_is_valid_program p ==>
      bir_env_vars_are_initialised env (bir_vars_of_program p) ==>
      MEM l (bir_labels_of_program p) ==>
      (SND (THE (bir_get_program_block_info_by_label p l)) = bl) ==>
      bir_env_vars_are_initialised env (bir_vars_of_block bl)``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Cases_on `p` >>
FULL_SIMP_TAC std_ss [bir_vars_of_program_def] >>
subgoal `bl IN (set l')` >- (
  IMP_RES_TAC
    bir_get_program_block_info_by_label_MEM >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [bir_is_valid_program_def,
    bir_get_program_block_info_by_label_valid_THM,
    listTheory.MEM_EL] >>
  EXISTS_TAC ``i:num`` >>
  FULL_SIMP_TAC std_ss []
) >>
METIS_TAC [bir_env_vars_are_initialised_UNION,
           SUBSET_BIGUNION_IMAGE_thm,
           bir_env_vars_are_initialised_SUBSET]
);
    
val bir_get_current_block_SOME_MEM = prove(
  ``!l pc bl.
      bir_is_valid_program (BirProgram l) ==>
      (bir_get_current_block (BirProgram l) pc = SOME bl) ==>
      (MEM bl l)``,

REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_get_current_block_def] >>
Cases_on `bir_get_program_block_info_by_label (BirProgram l)
                                              pc.bpc_label` >- (
  FULL_SIMP_TAC std_ss []
) >>
Cases_on `x` >>
  REV_FULL_SIMP_TAC std_ss [
    bir_is_valid_program_def,
    bir_get_program_block_info_by_label_valid_THM,
    listTheory.MEM_EL] >>
EXISTS_TAC ``q:num`` >>
FULL_SIMP_TAC std_ss []
);

val bir_exec_block_running_at_least_one_step = prove(
  ``!p bl st l' c' st'.
      (bir_exec_block p bl st = (l',c',st')) ==>
      (st'.bst_status = BST_Running) ==>
      (0<c')``,

RW_TAC std_ss [bir_exec_block_def] >>
Q.ABBREV_TAC `s' = bir_exec_stmtsB bl.bb_statements ([],0,st)` >>
pairLib.PairCases_on `s'` >>
FULL_SIMP_TAC std_ss [LET_DEF, bir_state_is_terminated_def] >>
Cases_on `s'2.bst_status <> BST_Running` >- (
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss []>>
  FULL_SIMP_TAC (srw_ss()) []
) >>
FULL_SIMP_TAC (srw_ss()) []>>
RW_TAC std_ss []
);

val bir_exec_to_labels_triple_jmp =
  store_thm("bir_exec_to_labels_triple_jmp",
  ``!p l bl l1 ls post post'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog p ==>
      MEM l (bir_labels_of_program p) ==>
      MEM l1 (bir_labels_of_program p) ==>
      (SND(THE(bir_get_program_block_info_by_label p l)) = bl) ==>
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l1))) ==>
      (((l1 IN ls) ==> (post' = post)) /\
       ((~(l1 IN ls)) ==>
        (bir_exec_to_labels_triple p l1 ls post' post) /\
        (bir_is_bool_exp post')
       )
      ) ==>
      (bir_exec_to_labels_triple p l ls
        (bir_wp_exec_stmtsB bl.bb_statements post') post
      )``,

(* Expand definitions *)
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "s'" is the state resulting from execution with
 * bir_exec_to_labels from s. *)
Q.ABBREV_TAC `s' = bir_exec_to_labels ls p s` >>
Q.ABBREV_TAC `cnd = l1 IN ls /\ (post' = post) \/
  bir_exec_to_labels_triple p l1 ls pre post'` >>
subgoal `(bir_get_current_block p s.bst_pc = SOME bl)` >- (
  FULL_SIMP_TAC std_ss [bir_get_current_block_def,
                        bir_get_program_block_info_by_label_MEM] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
(* Evaluate execution of bir_exec_to_labels using the lemma
 * bir_exec_to_labels_block. *)
IMP_RES_TAC bir_exec_to_labels_block >>
PAT_X_ASSUM ``!ls. p``
            (fn thm => FULL_SIMP_TAC std_ss [Q.SPEC `ls` thm]) >>
(* Specialize and introduce bir_exec_block_jmp_triple_wp_thm. *)
ASSUME_TAC (Q.SPECL [`p`, `bl`, `post'`, `l1`]
                    bir_exec_block_jmp_triple_wp_thm
           ) >>
Cases_on `p` >>
IMP_RES_TAC bir_get_current_block_SOME_MEM >>
subgoal `bir_is_well_typed_block bl` >- (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_program_def,
                        listTheory.EVERY_MEM] 
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `EVERY bir_isnot_declare_stmt bl.bb_statements` >- (
  FULL_SIMP_TAC std_ss [bir_declare_free_prog_def]
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp post'` >- (
  Cases_on `l1 IN ls` >> (
    FULL_SIMP_TAC std_ss [Abbr `cnd`]
  )
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `wp = (bir_wp_exec_stmtsB bl.bb_statements post')` >>
FULL_SIMP_TAC std_ss [bir_exec_block_jmp_triple_def] >>
Q.ABBREV_TAC `st1 = bir_exec_block (BirProgram l') bl s` >>
pairLib.PairCases_on `st1` >>
PAT_X_ASSUM ``!s.p`` (fn thm =>
  ASSUME_TAC (Q.SPECL [`s`, `st10`, `st11`, `st12`] thm)
) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_block bl)` >- (
  METIS_TAC [bir_env_vars_are_initialised_prog_block_thm]
) >>
(* Here, we end up with two cases: status AssumptionViolated in
 * st12 or not. *)
Cases_on `st12.bst_status <> BST_AssumptionViolated` >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_pre_post_def, bir_state_is_terminated_def,
               bir_is_valid_status_def] >| [
  (* Case 1: Status of st12 is Running. *)
  ASSUME_TAC (SPEC ``st12:bir_state_t`` bir_running_by_exclusion) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  (* Now we know that after executing the internal block we get
   * post' *)
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  Cases_on `l1 IN  ls` >- (
    FULL_SIMP_TAC std_ss [Abbr `cnd`, LET_DEF,
                          bir_state_COUNT_PC_def] >>
    ASSUME_TAC (Q.SPECL [`(BirProgram l')`, `bl`, `s`, `st10`,
                         `st11`, `st12`]
                        bir_exec_block_running_at_least_one_step
    ) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (srw_ss()) [bir_block_pc_def, Abbr `s'`] >>
    EXISTS_TAC ``st10:'a list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* Case: We have not reach an end label *)
  FULL_SIMP_TAC std_ss [Abbr `cnd`, LET_DEF, bir_state_COUNT_PC_def,
                        bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_triple_def] >>
  PAT_X_ASSUM ``!s''.p``
              (fn thm => ASSUME_TAC (Q.SPEC `st12` thm)) >>
  REV_FULL_SIMP_TAC (srw_ss()) [] >>
  subgoal `bir_env_vars_are_initialised st12.bst_environ
             (bir_vars_of_program (BirProgram l'))` >- (
    (* Use initialization monotonicity *)
    MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO]
                            bir_env_vars_are_initialised_ORDER) >>
    Q.EXISTS_TAC `s.bst_environ` >>
    subgoal `st12 = (SND (SND (bir_exec_block
                                (BirProgram l') bl s)))` >- (
      Q.ABBREV_TAC `s_tmp = bir_exec_block (BirProgram l') bl s` >>
      pairLib.PairCases_on `s_tmp` >>
      FULL_SIMP_TAC (srw_ss()) [markerTheory.Abbrev_def]
    ) >>
    FULL_SIMP_TAC std_ss [bir_exec_block_ENV_ORDER]
  ) >>
  (* The below line induces a case split for the different
   * postconditions in the assumption HT *)
  FULL_SIMP_TAC std_ss [] >> (
    FULL_SIMP_TAC (srw_ss()) [Abbr `s'`] >>
    EXISTS_TAC ``(st10 ++ l1'):'a list`` >>
    EXISTS_TAC ``(st11 + c1):num`` >>
    EXISTS_TAC ``c2:num`` >>
    EXISTS_TAC ``s'':bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ),

  EXISTS_TAC ``arbitrary:'a list`` >>
  EXISTS_TAC ``stuff:num`` >>
  EXISTS_TAC ``here:num`` >>
  EXISTS_TAC ``st12:bir_state_t`` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

val bir_exec_to_labels_triple_cjmp =
  store_thm("bir_exec_to_labels_triple_cjmp",
  ``!p l bl e l1 l2 ls post post1' post2'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog p ==>
      MEM l (bir_labels_of_program p) ==>
      MEM l1 (bir_labels_of_program p) ==>
      MEM l2 (bir_labels_of_program p) ==>
      (SND (THE (bir_get_program_block_info_by_label p l)) = bl) ==>
      (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1)
                                            (BLE_Label l2))
      ) ==>
      (((l1 IN ls) ==> (post1' = post)) /\
       ((~(l1 IN ls)) ==>
         bir_exec_to_labels_triple p l1 ls post1' post /\
         bir_is_bool_exp post1'
       )
      ) ==>
      (((l2 IN ls) ==> (post2' = post)) /\
       ((~(l2 IN ls)) ==>
         bir_exec_to_labels_triple p l2 ls post2' post /\
         bir_is_bool_exp post2'
       )
      ) ==>
      (bir_exec_to_labels_triple p l ls
        (bir_wp_exec_stmtsB bl.bb_statements 
        (
          (BExp_BinExp BIExp_And 
            (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e)
                                  post1'
            )
            (BExp_BinExp BIExp_Or e post2')
          )
        )
      ) post)``,

(* Expand definitions *)
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "s'" is the final state of execution *)
Q.ABBREV_TAC `s' = bir_exec_to_labels ls p s` >>
subgoal `(bir_get_current_block p s.bst_pc = SOME bl)` >- (
  FULL_SIMP_TAC std_ss [bir_get_current_block_def,
                        bir_get_program_block_info_by_label_MEM] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
(* Evaluate execution of bir_exec_to_labels using the lemma
 * bir_exec_to_labels_block. *)
IMP_RES_TAC bir_exec_to_labels_block >>
PAT_X_ASSUM ``!ls. p``
            (fn thm => FULL_SIMP_TAC std_ss [Q.SPEC `ls` thm]) >>
(* Specialize and introduce bir_exec_block_jmp_triple_wp_thm. *)
ASSUME_TAC (Q.SPECL [`p`, `bl`, `e`, `post1'`, `l1`, `post2'`, `l2`]
                    bir_exec_block_cjmp_triple_wp_thm
           ) >>
Cases_on `p` >>
IMP_RES_TAC bir_get_current_block_SOME_MEM >>
subgoal `bir_is_well_typed_block bl` >- (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_program_def,
                        listTheory.EVERY_MEM] 
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `EVERY bir_isnot_declare_stmt bl.bb_statements` >- (
  FULL_SIMP_TAC std_ss [bir_declare_free_prog_def]
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp post1'` >- (
  Cases_on `l1 IN ls` >> (
    FULL_SIMP_TAC std_ss []
  )
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp post2'` >- (
  Cases_on `l2 IN ls` >> (
    FULL_SIMP_TAC std_ss []
  )
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>

(* "wp" is the weakest precondition of the block of basic BIR
 * statements and the given postcondition. *)
Q.ABBREV_TAC
  `wp = (bir_wp_exec_stmtsB bl.bb_statements
          (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e)
                                  post1'
            )
            (BExp_BinExp BIExp_Or e post2')
          )
        )` >>
FULL_SIMP_TAC std_ss [bir_exec_block_cjmp_triple_def] >>
Q.ABBREV_TAC `st1 = bir_exec_block (BirProgram l') bl s` >>
pairLib.PairCases_on `st1` >>
PAT_X_ASSUM ``!s. p`` (fn thm =>
  ASSUME_TAC (Q.SPECL [`s`, `st10`, `st11`, `st12`] thm)
) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Now we know that after executing the internal block we get
 * post' *)
subgoal `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_block bl)` >- (
  METIS_TAC [bir_env_vars_are_initialised_prog_block_thm]
) >>
(* At this point, a case split is necessary. We get three subgoals:
 * the first two correspond to Running with the different
 * CJmp postconditions and the third is AssumptionViolated. *)
Cases_on `st12.bst_status <> BST_AssumptionViolated` >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_pre_post_def, bir_state_is_terminated_def,
               bir_is_valid_status_def, LET_DEF] >| [
  (* Case 1: Status of st12 is Running, post1. *)
  ASSUME_TAC (SPEC ``st12:bir_state_t`` bir_running_by_exclusion) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  Cases_on `l1 IN  ls` >- (
    FULL_SIMP_TAC std_ss [LET_DEF,
                          bir_state_COUNT_PC_def] >>
    ASSUME_TAC (Q.SPECL [`(BirProgram l')`, `bl`, `s`, `st10`,
                         `st11`,`st12`]
                        bir_exec_block_running_at_least_one_step) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (srw_ss()) [bir_block_pc_def, Abbr `s'`] >>
    EXISTS_TAC ``st10:'a list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* We have not reached an end label *)
  FULL_SIMP_TAC std_ss [LET_DEF,
                        bir_state_COUNT_PC_def, bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_triple_def] >>
  PAT_X_ASSUM ``!s''.p`` (fn thm=>ASSUME_TAC (Q.SPEC `st12` thm)) >>
  REV_FULL_SIMP_TAC (srw_ss()) [] >>
  subgoal `bir_env_vars_are_initialised st12.bst_environ
             (bir_vars_of_program (BirProgram l'))` >- (
    (* Use initialization monotonicity *)
    MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO]
                   bir_env_vars_are_initialised_ORDER
    ) >>
    Q.EXISTS_TAC `s.bst_environ` >>
    subgoal `st12 = (SND (SND (bir_exec_block
                                (BirProgram l') bl s)))` >- ( 
      Q.ABBREV_TAC `s_tmp = bir_exec_block (BirProgram l') bl s` >>
      pairLib.PairCases_on `s_tmp` >>
      FULL_SIMP_TAC (srw_ss()) [markerTheory.Abbrev_def]
    ) >>
    FULL_SIMP_TAC std_ss [bir_exec_block_ENV_ORDER]
  ) >>
  (* The below line induces a case split for the different
   * postconditions in the assumption HT *)
  FULL_SIMP_TAC std_ss [] >> (
    FULL_SIMP_TAC (srw_ss()) [Abbr `s'`] >>
    EXISTS_TAC ``(st10 ++ l1'):'a list`` >>
    EXISTS_TAC ``(st11 + c1):num`` >>
    EXISTS_TAC ``c2:num`` >>
    EXISTS_TAC ``s'':bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ),

  (* Case 2: Status of st12 is Running, post2. *)
  ASSUME_TAC (SPEC ``st12:bir_state_t`` bir_running_by_exclusion) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_is_valid_status_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  Cases_on `l2 IN  ls` >- (
    FULL_SIMP_TAC std_ss [LET_DEF,
                          bir_state_COUNT_PC_def] >>
    ASSUME_TAC (Q.SPECL [`(BirProgram l')`, `bl`, `s`, `st10`,
                         `st11`,`st12`]
                        bir_exec_block_running_at_least_one_step) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (srw_ss()) [bir_block_pc_def, Abbr `s'`] >>
    EXISTS_TAC ``st10:'a list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* We have not reached an end label *)
  FULL_SIMP_TAC std_ss [LET_DEF,
                        bir_state_COUNT_PC_def, bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_triple_def] >>
  PAT_X_ASSUM ``!s''.p`` (fn thm=>ASSUME_TAC (Q.SPEC `st12` thm)) >>
  REV_FULL_SIMP_TAC (srw_ss()) [] >>
  subgoal `bir_env_vars_are_initialised st12.bst_environ
             (bir_vars_of_program (BirProgram l'))` >- (
    (* Use initialization monotonicity *)
    MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_env_vars_are_initialised_ORDER) >>
    Q.EXISTS_TAC `s.bst_environ` >>
    subgoal `st12 = (SND (SND (bir_exec_block
                                (BirProgram l') bl s)))` >- ( 
      Q.ABBREV_TAC `s_tmp = bir_exec_block (BirProgram l') bl s` >>
      pairLib.PairCases_on `s_tmp` >>
      FULL_SIMP_TAC (srw_ss()) [markerTheory.Abbrev_def]
    ) >>
    FULL_SIMP_TAC std_ss [bir_exec_block_ENV_ORDER]
  ) >>
  (* The below line induces a case split for the different
   * postconditions in the assumption HT *)
  FULL_SIMP_TAC std_ss [] >> (
    FULL_SIMP_TAC (srw_ss()) [Abbr `s'`] >>
    EXISTS_TAC ``(st10 ++ l1'):'a list`` >>
    EXISTS_TAC ``(st11 + c1):num`` >>
    EXISTS_TAC ``c2:num`` >>
    EXISTS_TAC ``s'':bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ),

  (* Case 3: st12 has status AssumptionViolated *)
  EXISTS_TAC ``arbitrary:'a list`` >>
  EXISTS_TAC ``stuff:num`` >>
  EXISTS_TAC ``here:num`` >>
  EXISTS_TAC ``st12:bir_state_t`` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
);

(*
   -------------------------------------------------------------
                  Procedure for WP in DAG
   -------------------------------------------------------------
*)

val bir_wp_exec_of_block_def = Define `
  bir_wp_exec_of_block p l ls post wps = 
    case FLOOKUP wps l of
      SOME wp => SOME wps
    | NONE    => (
        let bl = SND
                   (THE(bir_get_program_block_info_by_label p l)) in
          case bl.bb_last_statement of
            BStmt_Jmp (BLE_Label l1) => (
              case FLOOKUP wps l1 of
                NONE => NONE
              | SOME wp =>
                  SOME (wps |+ (l, (bir_wp_exec_stmtsB
                                     bl.bb_statements wp
                                   )))
            )
          | BStmt_CJmp e (BLE_Label l1) (BLE_Label l2) => ( 
              case FLOOKUP wps l1 of
                NONE => NONE
              | SOME wp1 => (
                  case FLOOKUP wps l2 of
                    NONE => NONE
                  | SOME wp2 => SOME (wps |+ (l,
                      (bir_wp_exec_stmtsB bl.bb_statements 
                        (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_Or
                            (BExp_UnaryExp BIExp_Not e) wp1)
                          (BExp_BinExp BIExp_Or e wp2)
                        )
                      )))
                )
              )
          | _ => NONE
      )`;

val bir_jmp_direct_labels_only_def = Define `
  bir_jmp_direct_labels_only (BirProgram l) =
    (!bl. (MEM bl l) ==>
      (?l1. bl.bb_last_statement = BStmt_Jmp (BLE_Label l1)) \/
      (?e l1 l2.
         bl.bb_last_statement = BStmt_CJmp e (BLE_Label l1)
                                             (BLE_Label l2)
      )
    )`;

val bir_jmp_direct_labels_only_exec_def = Define `
  (bir_jmp_direct_labels_only_exec (BirProgram []) = T) /\
  (bir_jmp_direct_labels_only_exec (BirProgram (h::l)) =
    (case h.bb_last_statement of
      BStmt_Jmp (BLE_Label _) => T
    | BStmt_CJmp _ (BLE_Label _) (BLE_Label _) => T
    | _ => F) /\
  (bir_jmp_direct_labels_only_exec (BirProgram l)))`;

val bir_jmp_direct_labels_only_exec_eq_thm =
  store_thm("bir_jmp_direct_labels_only_exec_eq_thm",
  ``!p.
    (bir_jmp_direct_labels_only p =
      bir_jmp_direct_labels_only_exec p)``,

Cases_on `p` >> Q.RENAME1_TAC `(BirProgram bls)` >>
Induct_on `bls` >- (
  REWRITE_TAC [bir_jmp_direct_labels_only_def,
               bir_jmp_direct_labels_only_exec_def,
               listTheory.MEM]
) >>
REWRITE_TAC [bir_jmp_direct_labels_only_def,
             bir_jmp_direct_labels_only_exec_def,
             listTheory.MEM] >>
GEN_TAC >> EQ_TAC >- (
  REPEAT STRIP_TAC >- (
    Q.PAT_X_ASSUM `!x. y`
                  (fn thm => ASSUME_TAC (Q.SPEC `h` thm)) >>
    FULL_SIMP_TAC (srw_ss()) []
  ) >>
  METIS_TAC [bir_jmp_direct_labels_only_def]
) >>
REPEAT STRIP_TAC >- (
  Cases_on `h.bb_last_statement` >| [
    Cases_on `b`,

    Cases_on `b0` >> (Cases_on `b1`),

    ALL_TAC
  ] >> (
    FULL_SIMP_TAC (srw_ss()) []
  )
) >>
METIS_TAC [bir_jmp_direct_labels_only_def]
);

val bir_edge_in_prog_def = Define `
  bir_edge_in_prog (BirProgram bls) l1 l2 =
    ?bl1. (MEM bl1 bls) /\
          (bl1.bb_label = l1) /\
          ( (bl1.bb_last_statement = BStmt_Jmp (BLE_Label l2)) \/
            (?e l3. bl1.bb_last_statement =
              BStmt_CJmp e (BLE_Label l2) (BLE_Label l3)
            ) \/
            (?e l3. bl1.bb_last_statement =
              BStmt_CJmp e (BLE_Label l3) (BLE_Label l2)
            )
          )`;

val bir_edges_blocks_in_prog_def = Define `
  bir_edges_blocks_in_prog (BirProgram bls) l1 =
    !l2. (bir_edge_in_prog (BirProgram bls) l1 l2) ==>
         (?bl2. ( (MEM bl2 bls) /\ (bl2.bb_label = l2) ))`;

val bir_targets_in_prog_exec_def = Define `
  bir_targets_in_prog_exec p l1 =
    case bir_get_program_block_info_by_label p l1 of
      NONE => []
    | SOME (_,bl1) => 
        case bl1.bb_last_statement of
          BStmt_Jmp (BLE_Label l2) => [l2]
        | BStmt_CJmp e (BLE_Label l2) (BLE_Label l3) => [l2;l3]
        | BStmt_Halt e => []
        | _ => []`;

val bir_edges_blocks_in_prog_exec_def = Define `
  bir_edges_blocks_in_prog_exec (BirProgram bls) l1 =
    EVERY (\l2. EXISTS (\bl2. bl2.bb_label = l2) bls)
          (bir_targets_in_prog_exec (BirProgram bls) l1)`;

val bir_edges_blocks_in_prog_exec_eq_thm =
  store_thm("bir_edges_blocks_in_prog_exec_eq_thm",
  ``!p l1.
      bir_is_valid_labels p ==>
      (bir_edges_blocks_in_prog p l1 =
        bir_edges_blocks_in_prog_exec p l1
      )``,

Cases_on `p` >> Q.RENAME1_TAC `(BirProgram bls)` >>
REPEAT STRIP_TAC >>
REWRITE_TAC [bir_targets_in_prog_exec_def, bir_edge_in_prog_def,
             bir_edges_blocks_in_prog_def,
             bir_edges_blocks_in_prog_exec_def,
             listTheory.EVERY_MEM, listTheory.EXISTS_MEM,
             LET_DEF] >>
BETA_TAC >>
Cases_on `bir_get_program_block_info_by_label
            (BirProgram bls) l1` >- (
  FULL_SIMP_TAC std_ss
                [bir_get_program_block_info_by_label_valid_THM,
                 listTheory.MEM] >>
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss []
) >>
Cases_on `x` >> Q.RENAME1_TAC `SOME (idx, bl1)` >>
REV_FULL_SIMP_TAC std_ss
                  [bir_get_program_block_info_by_label_valid_THM] >>
EQ_TAC >- (
  REPEAT STRIP_TAC >>
  Cases_on `bl1.bb_last_statement` >| [
    Cases_on `b`,

    Cases_on `b0` >> (
      Cases_on `b1`
    ),
     
    ALL_TAC
  ] >> (
    FULL_SIMP_TAC (srw_ss()) [] >>
    METIS_TAC [rich_listTheory.EL_MEM]
  )
) >>
REPEAT STRIP_TAC >> (
  subgoal `bl1' = bl1` >- (
    FULL_SIMP_TAC std_ss [bir_is_valid_labels_def,
                          bir_labels_of_program_def,
                          listTheory.MEM_EL] >>
    METIS_TAC [listTheory.ALL_DISTINCT_EL_IMP,
               listTheory.LENGTH_MAP, listTheory.EL_MAP]
  ) >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  METIS_TAC []
)
);

val bir_stmt_end_ss = rewrites (type_rws ``:bir_stmt_end_t``);
val bir_label_exp_ss = rewrites (type_rws ``:bir_label_exp_t``);

val FEVERY_FEVERY_DRESTRICT_thm = prove(
  ``!P M S.
      FEVERY P M ==> FEVERY P (DRESTRICT M S)``,

FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
              [finite_mapTheory.FEVERY_DEF,
               finite_mapTheory.FDOM_DRESTRICT,
               finite_mapTheory.DRESTRICT_DEF]
);

val bir_wp_exec_of_block_bool_thm =
  store_thm("bir_wp_exec_of_block_bool_thm",
  ``!p l ls post wps wps'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog p ==>
      MEM l (bir_labels_of_program p) ==>
      FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps ==>
      ((bir_wp_exec_of_block p l ls post wps) = SOME wps') ==>
      (FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps')``,

REPEAT STRIP_TAC >>
Cases_on `p` >>
Q.RENAME1_TAC `BirProgram bls` >>
FULL_SIMP_TAC std_ss [bir_wp_exec_of_block_def,
                      bir_get_program_block_info_by_label_MEM,
                      LET_DEF] >>
Cases_on `FLOOKUP wps l` >- (
  subgoal `MEM bl bls` >- (
    METIS_TAC [bir_get_program_block_info_by_label_def,
               INDEX_FIND_EQ_SOME_0, listTheory.MEM_EL]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Cases_on `(?l1.
              bl.bb_last_statement = BStmt_Jmp (BLE_Label l1)) \/
            (?e l1 l2.
              bl.bb_last_statement =
                BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))` >| [
    ALL_TAC,

    Cases_on `bl.bb_last_statement` >| [
      Cases_on `b` >>
      FULL_SIMP_TAC std_ss [],

      Cases_on `b0` >> Cases_on `b1` >>
      FULL_SIMP_TAC (srw_ss()) [],

      FULL_SIMP_TAC (srw_ss()) []
    ]
  ] >> (
    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF,
                          finite_mapTheory.FDOM_FUPDATE,
                          pred_setTheory.COMPONENT] >>
    FULL_SIMP_TAC (std_ss++bir_stmt_end_ss++bir_label_exp_ss) []
  ) >| [
    Cases_on `l1 IN FDOM wps` >- (
      FULL_SIMP_TAC std_ss [] >>
      subgoal `bir_is_bool_exp
                 (bir_wp_exec_stmtsB bl.bb_statements
                                     (FAPPLY wps l1)
                 )` >- (
        FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_DEF,
                              bir_declare_free_prog_def] >>
        METIS_TAC [bir_is_well_typed_program_def,
                   bir_is_well_typed_block_def,
                   listTheory.EVERY_MEM,
                   bir_wp_exec_stmtsB_bool_thm]
      ) >>
      Q.PAT_X_ASSUM `FUPDATE A B = C`
                    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
                                              (wps ' l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
                            FEVERY_FEVERY_DRESTRICT_thm]
    ) >>
    FULL_SIMP_TAC std_ss [],

    Cases_on `l1 IN FDOM wps /\ l2 IN FDOM wps` >- (
      FULL_SIMP_TAC std_ss [] >>
      Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_Or
                       (BExp_UnaryExp BIExp_Not e)
                       (FAPPLY wps l1)
                     )
                     (BExp_BinExp BIExp_Or e (FAPPLY wps l2)))` >>
      subgoal `bir_is_bool_exp (exp1)` >- (
        subgoal `bir_is_well_typed_stmtE
                  (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))` >- (
          METIS_TAC [bir_is_well_typed_program_def,
                     listTheory.EVERY_MEM,
                     bir_is_well_typed_block_def]
        ) >>
        FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS,
                              finite_mapTheory.FEVERY_DEF,
                              bir_is_well_typed_stmtE_def,
                              bir_is_bool_exp_GSYM, Abbr `exp1`]
      ) >>
      subgoal `bir_is_bool_exp
                (bir_wp_exec_stmtsB bl.bb_statements exp1)` >- (
        FULL_SIMP_TAC std_ss [bir_declare_free_prog_def] >>
        METIS_TAC [bir_is_well_typed_program_def,
                   bir_is_well_typed_block_def,
                   listTheory.EVERY_MEM,
                   bir_wp_exec_stmtsB_bool_thm]
      ) >>
      Q.PAT_X_ASSUM `FUPDATE A B = C`
                    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
                                              (wps ' l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
                            FEVERY_FEVERY_DRESTRICT_thm]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>
    Cases_on `l1 IN FDOM wps` >> (
      FULL_SIMP_TAC std_ss []
    )
  ]
) >>
FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF]
);

val bir_wp_exec_of_block_sound_thm =
  store_thm("bir_wp_exec_of_block_sound_thm",
  ``!p l ls post wps wps'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_edges_blocks_in_prog p l ==>
      ~(l IN ls) ==>
      FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps ==>
      FEVERY (\(l1, wp1).
               ((l1 IN ls) ==> (wp1 = post)) /\
               ((~(l1 IN ls)) ==>
                 (bir_exec_to_labels_triple p l1 ls wp1 post)
               )
             ) wps ==>
      ((bir_wp_exec_of_block p l ls post wps) = SOME wps') ==>
      (FEVERY (\(l1, wp1).
                ((l1 IN ls) ==> (wp1 = post)) /\
                ((~(l1 IN ls)) ==>
                  (bir_exec_to_labels_triple p l1 ls wp1 post)
                )
              ) wps')
  ``,

REPEAT STRIP_TAC >>
Cases_on `p` >>
Q.RENAME1_TAC `BirProgram bls` >>
FULL_SIMP_TAC std_ss [bir_wp_exec_of_block_def,
                      bir_get_program_block_info_by_label_MEM,
                      LET_DEF] >>
Cases_on `FLOOKUP wps l` >- (
  subgoal `MEM bl bls` >- (
    METIS_TAC [bir_get_program_block_info_by_label_def,
               INDEX_FIND_EQ_SOME_0, listTheory.MEM_EL]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Cases_on `(?l1.
              bl.bb_last_statement = BStmt_Jmp (BLE_Label l1)) \/
            (?e l1 l2.
              bl.bb_last_statement =
                BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))` >| [
    ALL_TAC,

    Cases_on `bl.bb_last_statement` >| [
      Cases_on `b` >>
      FULL_SIMP_TAC std_ss [],

      Cases_on `b0` >>
      Cases_on `b1` >>
      FULL_SIMP_TAC (srw_ss()) [],

      FULL_SIMP_TAC (srw_ss()) []
    ]
  ] >> (
    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF,
                          finite_mapTheory.FDOM_FUPDATE,
                          pred_setTheory.COMPONENT] >>
    FULL_SIMP_TAC (std_ss++bir_stmt_end_ss++bir_label_exp_ss) []
  ) >| [
    Cases_on `l1 IN FDOM wps` >- (
      FULL_SIMP_TAC std_ss [] >>
      subgoal `bir_exec_to_labels_triple (BirProgram bls) l ls
                 (bir_wp_exec_stmtsB bl.bb_statements
                                     (FAPPLY wps l1)
                 ) post` >- (
        ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `l1`,
                             `ls`, `post`]
                            bir_exec_to_labels_triple_jmp) >>
        subgoal `MEM l1 (bir_labels_of_program
                          (BirProgram bls)
                        )` >- (
          FULL_SIMP_TAC std_ss [bir_edges_blocks_in_prog_def,
                                bir_labels_of_program_def] >>
          Q.PAT_X_ASSUM `!A. bir_edge_in_prog B C D ==>
                         ?E. G`
                        (fn thm => ASSUME_TAC (Q.SPEC `l1` thm)) >>
          FULL_SIMP_TAC list_ss
                        [bir_edge_in_prog_def,
                         bir_get_program_block_info_by_label_THM,
                         listTheory.MEM_MAP] >>
          METIS_TAC []
        ) >>
        FULL_SIMP_TAC std_ss
                      [bir_get_program_block_info_by_label_MEM,
                       finite_mapTheory.FEVERY_DEF]
      ) >>  
      Q.PAT_X_ASSUM `FUPDATE A B = C`
                    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
                                              (FAPPLY wps l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
                            FEVERY_FEVERY_DRESTRICT_thm]
    ) >>
    FULL_SIMP_TAC std_ss [],

    Cases_on `l1 IN FDOM wps /\ l2 IN FDOM wps` >- (
      FULL_SIMP_TAC std_ss [] >>
      Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
                             (BExp_BinExp BIExp_Or
                               (BExp_UnaryExp BIExp_Not e)
                               (FAPPLY wps l1)
                             )
                             (BExp_BinExp BIExp_Or e
                                                   (FAPPLY wps l2)
                             )
                           )` >>
      subgoal `bir_exec_to_labels_triple (BirProgram bls) l ls
                (bir_wp_exec_stmtsB bl.bb_statements exp1)
                post` >- (
        ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `e`, `l1`,
                             `l2`, `ls`, `post`]
                   bir_exec_to_labels_triple_cjmp) >>
        subgoal `MEM l1
                  (bir_labels_of_program (BirProgram bls)) /\
                 MEM l2
                  (bir_labels_of_program (BirProgram bls))` >- (
          FULL_SIMP_TAC std_ss [bir_edges_blocks_in_prog_def,
                                bir_labels_of_program_def] >>
          Q.PAT_X_ASSUM `!A. bir_edge_in_prog B C D ==> ?E. G`
                        (fn thm => ASSUME_TAC (Q.SPEC `l1` thm) >>
          ASSUME_TAC (Q.SPEC `l2` thm)) >>
          FULL_SIMP_TAC std_ss
                        [bir_edge_in_prog_def,
                         bir_get_program_block_info_by_label_THM,
                         listTheory.MEM_MAP] >>
          METIS_TAC []
        ) >>
        FULL_SIMP_TAC std_ss
                      [bir_get_program_block_info_by_label_MEM,
                       finite_mapTheory.FEVERY_DEF, Abbr `exp1`]
      ) >>
      Q.PAT_X_ASSUM `FUPDATE A B = C`
                    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
                                              (FAPPLY wps l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
                            FEVERY_FEVERY_DRESTRICT_thm]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [] >>
    Cases_on `l1 IN FDOM wps` >>
    FULL_SIMP_TAC std_ss []
  ]
) >>
FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF]
);

val bir_bool_wps_map_def = Define `
  bir_bool_wps_map wps =
    (FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps)`;

val bir_sound_wps_map_def = Define `
  bir_sound_wps_map p ls post wps =
    (FEVERY (\(l1, wp1).
              ((l1 IN ls) ==> (wp1 = post)) /\
              ((~(l1 IN ls)) ==>
                (bir_exec_to_labels_triple p l1 ls wp1 post)
              )
            ) wps
    )`;

val bir_wp_exec_of_block_bool_exec_thm =
  store_thm("bir_wp_exec_of_block_bool_exec_thm",
  ``!p l (ls:bir_label_t->bool) post wps wps'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog_exec p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_bool_wps_map wps ==>
      ((bir_wp_exec_of_block p l ls post wps) = SOME wps') ==>
      (bir_bool_wps_map wps')``,

REWRITE_TAC [bir_bool_wps_map_def] >>
METIS_TAC [bir_declare_free_prog_exec_eq_thm,
           bir_wp_exec_of_block_bool_thm]
);

val bir_wp_exec_of_block_sound_exec_thm =
  store_thm("bir_wp_exec_of_block_sound_exec_thm",
``!p l ls post wps wps'.
    bir_is_bool_exp post ==>
    bir_is_well_typed_program p ==>
    bir_is_valid_program p ==>
    bir_declare_free_prog_exec p ==>
    MEM l (bir_labels_of_program p) ==>
    bir_edges_blocks_in_prog_exec p l ==>
    ~(l IN ls) ==>
    bir_bool_wps_map wps ==>
    bir_sound_wps_map p ls post wps ==>
    ((bir_wp_exec_of_block p l ls post wps) = SOME wps') ==>
    (bir_sound_wps_map p ls post wps')``,

  REWRITE_TAC [bir_bool_wps_map_def, bir_sound_wps_map_def] >>
  METIS_TAC [bir_declare_free_prog_exec_eq_thm,
             bir_is_valid_program_def,
             bir_edges_blocks_in_prog_exec_eq_thm,
             bir_wp_exec_of_block_sound_thm]
);

val bir_wp_exec_of_block_reusable_thm =
  store_thm("bir_wp_exec_of_block_reusable_thm",
  ``!p l ls post wps wps'.
      bir_is_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      bir_declare_free_prog_exec p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_edges_blocks_in_prog_exec p l ==>
      ~(l IN ls) ==>
      ((bir_bool_wps_map wps) /\
       (bir_sound_wps_map p ls post wps)
      ) ==>
      ((bir_wp_exec_of_block p l ls post wps) = SOME wps') ==>
      ((bir_bool_wps_map wps') /\
       (bir_sound_wps_map p ls post wps')
      )``,

METIS_TAC [bir_wp_exec_of_block_sound_exec_thm,
           bir_wp_exec_of_block_bool_exec_thm]
);

val _ = export_theory();
