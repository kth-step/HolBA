open HolKernel Parse boolLib bossLib;

(* Theories from theory/bir: *)
open bir_programTheory bir_typing_progTheory bir_envTheory
     holba_auxiliaryTheory bir_valuesTheory bir_expTheory
     bir_exp_immTheory bir_typing_expTheory bir_immTheory;
open bir_env_oldTheory;

(* Theories from theory/bir-support: *)
open bir_program_blocksTheory bir_program_terminationTheory
     bir_program_valid_stateTheory bir_exp_substitutionsTheory
     bir_bool_expTheory bir_program_env_orderTheory
     bir_program_multistep_propsTheory bir_exp_equivTheory
     bir_bool_expTheory bir_program_no_assumeTheory;

(* Simplification sets from theory/bir: *)
open HolBACoreSimps;

val _ = new_theory "bir_wp";

(* Lemmata to move: *)

Theorem bir_varinit_invar_bstmt:
  !s s' obs vars (bstmt:'a bir_stmt_basic_t).
      bir_env_vars_are_initialised s.bst_environ vars ==>
      (bir_env_vars_are_initialised
        (bir_exec_stmtB_state bstmt s).bst_environ vars)
Proof
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``s:bir_state_t``,
                   ``bstmt:'a bir_stmt_basic_t``]
                  bir_exec_stmtB_ENV_ORDER
           ) >>
IMP_RES_TAC bir_env_vars_are_initialised_ORDER
QED

Theorem bir_is_bool_exp_env_invar_bstmt:
  !s s' obs ex (bstmt:'a bir_stmt_basic_t).
      bir_is_bool_exp_env s.bst_environ ex ==>
      (bir_exec_stmtB bstmt s = (obs, s')) ==>
      (bir_is_bool_exp_env s'.bst_environ ex)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def] >>
IMP_RES_TAC bir_varinit_invar_bstmt >>
PAT_X_ASSUM ``!bstmt. _``
            (fn thm => ASSUME_TAC
              (SPEC ``bstmt:'a bir_stmt_basic_t`` thm)
            ) >>
REV_FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def]
QED

(*
   -------------------------------------------------------------
                      Single basic statements
   -------------------------------------------------------------
*)

(* In summary: a valid status must be Running or
 * AssumptionViolated. *)
Definition bir_is_valid_status_def:
  bir_is_valid_status state = 
    ((state.bst_status <> BST_Failed) /\
    (state.bst_status <> BST_TypeError) /\
    (!l. state.bst_status <> BST_JumpOutside l) /\
    (!v. state.bst_status <> BST_Halted v) /\
    (state.bst_status <> BST_AssertionViolated))
End

(* The pre- and postcondition of the Hoare triple. *)
Definition bir_pre_post_def:
  bir_pre_post s pre s' post =
    (bir_is_bool_exp_env s.bst_environ pre ==>
    (
      (bir_is_valid_status s /\
       (bir_eval_exp pre (s.bst_environ) = SOME bir_val_true)
      ) /\
      (s.bst_status = BST_Running)
    ) ==>
    (
      (bir_is_bool_exp_env s'.bst_environ post /\
        (bir_is_valid_status s' /\
          (bir_eval_exp post (s'.bst_environ) = SOME bir_val_true)
        ) \/
        (s'.bst_status = BST_AssumptionViolated)
      )
    ))
End

(* Hoare triple for the execution of one basic BIR statement. *)
Definition bir_exec_stmtB_triple_def:
  bir_exec_stmtB_triple stmt pre post =
    !s s' obs.
      (* Note: Variable initialisation is only used by
       * Assign and Observe. *)
      bir_env_vars_are_initialised s.bst_environ
        (bir_vars_of_stmtB stmt) ==>
      (bir_exec_stmtB stmt s = (obs, s')) ==>
      bir_pre_post s pre s' post
End

(* Preservation of valid status for the Assert statement *)
Theorem bir_assert_valid_status:
  !s s' ex post obs.
      bir_is_valid_status s ==>
      (bir_eval_exp (BExp_BinExp BIExp_And ex post) s.bst_environ =
        SOME bir_val_true) ==>
      (bir_exec_stmtB (BStmt_Assert ex) s = (obs,s')) ==>
      bir_is_valid_status s'
Proof
REPEAT STRIP_TAC >>
subgoal `bir_eval_exp ex s.bst_environ = SOME bir_val_true` >- (
  METIS_TAC [bir_and_equiv]
) >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                      bir_exec_stmt_assert_def,
                      bir_dest_bool_val_TF]
QED

(* The postcondition of the Assert statement can be proved given
 * the precondition. *)
Theorem bir_assert_postcond:
  !s s' ex post obs.
      (bir_eval_exp (BExp_BinExp BIExp_And ex post) s.bst_environ =
        SOME bir_val_true) ==>
      (bir_exec_stmtB (BStmt_Assert ex) s = (obs,s')) ==>
      (bir_eval_exp post s'.bst_environ = SOME bir_val_true)
Proof
REPEAT STRIP_TAC >>
subgoal `bir_eval_exp post s.bst_environ = SOME bir_val_true` >- (
  METIS_TAC [bir_and_equiv]
) >>
subgoal `bir_eval_exp ex s.bst_environ = SOME bir_val_true` >- (
  METIS_TAC [bir_and_equiv]
) >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                      bir_exec_stmt_assert_def,
                      bir_dest_bool_val_TF] >>
REV_FULL_SIMP_TAC std_ss []
QED

(* Theorem stating the soundness of the precondition ex /\ post for the
 * statement Assert ex, with the postcondition post. *)
(* {ex /\ post} Assert ex {post} *)
Theorem bir_triple_exec_stmtB_assert_thm:
  !ex post.
      bir_exec_stmtB_triple (BStmt_Assert ex)
                            (BExp_BinExp BIExp_And ex post) post
Proof
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
subgoal `bir_is_bool_exp_env s'.bst_environ post` >- (
  METIS_TAC [bir_is_bool_exp_env_REWRS,
             bir_is_bool_exp_env_invar_bstmt]
) >>
subgoal `bir_is_valid_status s'` >- (
  METIS_TAC [bir_assert_valid_status]
) >>
subgoal `bir_eval_exp post s'.bst_environ = SOME bir_val_true` >- (
  METIS_TAC [bir_assert_postcond]
) >>
FULL_SIMP_TAC std_ss []
QED

(* Preservation of valid status for the Assume statement *)
Theorem bir_assume_valid_status:
  !s s' ex post obs.
      bir_is_valid_status s ==>
      (* TODO: We need some type of antecedent to guarantee Failed
       * does not occur. This could be either Booleanity+var.init.
       * or the Assume precondition. *)
      bir_is_bool_exp_env s.bst_environ
        (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post) ==>
      (bir_exec_stmtB (BStmt_Assume ex) s = (obs,s')) ==>
      bir_is_valid_status s'
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS] >>
PAT_X_ASSUM ``bir_is_bool_exp_env s.bst_environ ex``
            (fn thm => ASSUME_TAC (HO_MATCH_MP bir_bool_values thm)) >>
FULL_SIMP_TAC std_ss [] >> (
  FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                        bir_exec_stmt_assume_def,
                        bir_dest_bool_val_TF]
) >>
Cases_on `s` >>
Cases_on `s'` >> (
  FULL_SIMP_TAC std_ss [bir_state_t_fn_updates] >>
  RW_TAC std_ss [bir_is_valid_status_def]
)
QED

(* Given the precondition and the Assumed expression holding
 * in the initial state, the postcondition must hold in the
 * final state whenever the Assumed expression holds. *)
Theorem bir_assume_postcond:
  !s s' ex post obs.
      (bir_eval_exp (BExp_BinExp BIExp_Or
                      (BExp_UnaryExp BIExp_Not ex) post
                    ) s.bst_environ =
        SOME bir_val_true) ==>
      (bir_eval_exp ex s.bst_environ =
        SOME bir_val_true) ==>
      (bir_exec_stmtB (BStmt_Assume ex) s = (obs,s')) ==>
      (bir_eval_exp post s'.bst_environ = SOME bir_val_true)
Proof
REPEAT STRIP_TAC >>
subgoal
  `bir_eval_exp post s.bst_environ = SOME bir_val_true` >- (
  FULL_SIMP_TAC std_ss [bir_eval_exp_def,
                        bir_eval_unary_exp_def,
                        bir_unary_exp_def,
                        bir_unary_exp_GET_OPER_def,
                        bir_val_false_def, bir_val_true_def,
                        bir_disj1_false, word1_neg]
) >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtB_def,
                                          bir_exec_stmt_assume_def,
                                          bir_dest_bool_val_TF]
QED

(* Given the Assumed expression not holding in the initial
 * state, the final state will have status AssumptionViolated. *)
(* TODO: This theorem could also be stated with the precondition
 * holding instead of Booleanity holding. This antecedent is
 * needed to translate "not equal to True" to "equal to False". *)
Theorem bir_assume_assumviol:
  !s s' ex post obs.
      bir_is_bool_exp_env s.bst_environ
           (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex)
                                 post
           ) ==>
      (bir_eval_exp ex s.bst_environ <>
        SOME bir_val_true) ==>
      (bir_exec_stmtB (BStmt_Assume ex) s = (obs,s')) ==>
      (s'.bst_status = BST_AssumptionViolated)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS] >>
PAT_X_ASSUM ``bir_is_bool_exp_env s.bst_environ ex``
            (fn thm => ASSUME_TAC
              (HO_MATCH_MP bir_bool_values thm)
            ) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [bir_not_val_true, bir_exec_stmtB_def,
                      bir_exec_stmt_assume_def,
                      bir_dest_bool_val_TF, bir_val_TF_dist] >>
Cases_on `s` >> Cases_on `s'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_t_fn_updates]
QED

(* Theorem stating the soundness of the precondition ~e \/ Q for the
 * statement Assume e, with the postcondition Q. *)
(* {~e \/ Q} Assume e {Q} *)
Theorem bir_triple_exec_stmtB_assume_thm:
  !ex post.
      bir_is_well_typed_stmtB (BStmt_Assume ex) ==>
      bir_exec_stmtB_triple (BStmt_Assume ex)
                            (BExp_BinExp BIExp_Or
                              (BExp_UnaryExp BIExp_Not ex) post
                            ) post
Proof
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
subgoal `bir_is_bool_exp_env s'.bst_environ post` >- (
  METIS_TAC [bir_is_bool_exp_env_REWRS,
             bir_is_bool_exp_env_invar_bstmt]
) >>
subgoal `bir_is_valid_status s'` >- (
  METIS_TAC [bir_assume_valid_status]
) >>
Cases_on `bir_eval_exp ex s.bst_environ = SOME bir_val_true` >| [
  subgoal `bir_eval_exp post s'.bst_environ = SOME bir_val_true` >- (
    METIS_TAC [bir_assume_postcond]
  ) >>
  FULL_SIMP_TAC std_ss [],

  subgoal `s'.bst_status = BST_AssumptionViolated` >- (
    METIS_TAC [bir_assume_assumviol]
  ) >>
  FULL_SIMP_TAC std_ss []
]
QED

(* Theorem that proves (conditional) preservation of Booleanity
 * under substitution *)
local
  val subst_induct_tac = (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_exp_subst_def, type_of_bir_exp_def] >>
    ASSUME_TAC (SPEC ``(FEMPTY |+ (v,ex)):bir_var_t |-> bir_exp_t``
                     bir_exp_subst_TYPE_EQ
               ) >>
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
                          finite_mapTheory.DRESTRICT_FEMPTY,
                          finite_mapTheory.FEVERY_FEMPTY] >>
    REV_FULL_SIMP_TAC std_ss []
  )

  val one_op_tac = (
    subst_induct_tac >>
    PAT_X_ASSUM ``!e. _`` (fn thm => ASSUME_TAC (SPEC ``ex':bir_exp_t`` thm)) >>
    Cases_on `type_of_bir_exp ex'` >> (
      FULL_SIMP_TAC std_ss []
    )
  )

  val two_op_tac = (
    subst_induct_tac >>
    PAT_ASSUM ``!e. _``
              (fn thm => ASSUME_TAC (SPEC ``ex':bir_exp_t`` thm)) >>
    PAT_X_ASSUM ``!e. _``
                (fn thm => ASSUME_TAC
                  (SPEC ``ex'':bir_exp_t`` thm)
                ) >>
    Cases_on `type_of_bir_exp ex'` >>
    Cases_on `type_of_bir_exp ex''` >> (
      FULL_SIMP_TAC std_ss []
    )
  )

  val three_op_tac = (
    subst_induct_tac >>
    PAT_ASSUM ``!e. _``
              (fn thm => ASSUME_TAC (SPEC ``ex':bir_exp_t`` thm)) >>
    PAT_ASSUM ``!e. _``
              (fn thm => ASSUME_TAC
                (SPEC ``ex'':bir_exp_t`` thm)
              ) >>
    PAT_X_ASSUM ``!e. _``
                (fn thm => ASSUME_TAC
                  (SPEC ``ex''':bir_exp_t`` thm)
                ) >>
    Cases_on `type_of_bir_exp ex'` >>
    Cases_on `type_of_bir_exp ex''` >>
    Cases_on `type_of_bir_exp ex'''` >> (
      FULL_SIMP_TAC std_ss []
    )
  )

in

Theorem bir_exp_subst1_bool:
  !v ex ex'.
      bir_is_bool_exp
        (bir_exp_subst1 v ex ex') ==>
      (type_of_bir_exp ex = SOME (bir_var_type v)) ==>
      bir_is_bool_exp ex'
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_def,
                      bir_exp_subst1_def] >>

Induct_on `ex'` >| [
  (* Const *)
  FULL_SIMP_TAC std_ss [bir_exp_subst_def],

  (* MemConst *)
  FULL_SIMP_TAC std_ss [bir_exp_subst_def],

  (* Den *)
  REPEAT STRIP_TAC >>
  Cases_on `b` >> Cases_on `v` >>
  FULL_SIMP_TAC std_ss [type_of_bir_exp_def, bir_var_type_def,
                        bir_exp_subst_def, bir_exp_subst_var_def] >>
  Cases_on `(BVar s' b) = (BVar s b')` >| [
    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_UPDATE,
                          bir_var_t_11],

    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_UPDATE,
                          finite_mapTheory.FLOOKUP_EMPTY,
                          type_of_bir_exp_def, bir_var_type_def]
  ],

  (* Cast *)
  one_op_tac,

  (* UnaryExp *)
  one_op_tac,

  (* BinExp *)
  two_op_tac,

  (* BinPred *)
  two_op_tac,

  (* MemEq *)
  two_op_tac,

  (* IfThenElse *)
  three_op_tac,

  (* Load *)
  two_op_tac,

  (* Store *)
  three_op_tac
]
QED
end;

(* Theorem that proves the result of executing Assign, given regular
 * circumstances. *)
Theorem bir_assign_exec:
  !s s' vname vtype ex obs f.
    bir_is_well_typed_stmtB (BStmt_Assign (BVar vname vtype) ex) ==>
    bir_env_vars_are_initialised s.bst_environ
      (bir_vars_of_stmtB (BStmt_Assign (BVar vname vtype) ex)) ==>
    (bir_exec_stmtB (BStmt_Assign (BVar vname vtype) ex) s =
       (obs,s')) ==>
    (s.bst_environ = (BEnv f)) ==>
    ((NONE=obs) /\
     (s with bst_environ :=
       BEnv ((vname =+ bir_eval_exp ex (BEnv f)) f) =
      s')
    )
Proof
REPEAT STRIP_TAC >>
(* Start to evaluate the effects of execution, in order to get the
 * new variable environment explicit in the goal. *)
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
                      bir_exec_stmt_assign_def,
                      bir_env_write_def,
                      (GEN_ALL o SYM)
                        bir_env_var_is_declared_ALT_DEF] >>
(* Split up assumption on variable initialisation of
 * Assign statement, in order to use initialisation of v. *)
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      bir_env_vars_are_initialised_INSERT] >>
(* Conclude that since v is initialised, it is also declared. *)
REV_FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_weaken] >>
(* Subgoal: ex evaluated in the variable environment of s has type
 * vtype. *)
(* (This holds since variables of ex are initialised, and type is
 * given by well-typedness of statement) *)
FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def,
                        bir_var_type_def,
                        type_of_bir_exp_THM_with_init_vars] >>
IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
FULL_SIMP_TAC std_ss [bir_var_name_def,
                      bir_env_update_def, bir_var_type_def,
                      LET_DEF, bir_env_var_is_initialised_def,
                      bir_env_lookup_def] >>
REV_FULL_SIMP_TAC std_ss []
QED

(* Preservation of Booleanity and variable initialisation for the
 * Assign statement *)
Theorem bir_assign_bool_exp_env:
  !s s' v ex post obs.
      (* Antecedents from outside the Hoare triple: *)
      bir_is_well_typed_stmtB (BStmt_Assign v ex) ==>
      (* Antecedents from within the Hoare triple: *)
      bir_is_bool_exp_env s.bst_environ
        (bir_exp_subst1 v ex post) ==>
      bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_stmtB (BStmt_Assign v ex)) ==>
      (bir_exec_stmtB (BStmt_Assign v ex) s = (obs,s')) ==>
      bir_is_bool_exp_env s'.bst_environ post
Proof
REPEAT STRIP_TAC >>
(* First, Booleanity can be proved immediately: *)
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def] >>
subgoal `bir_is_bool_exp post` >- (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def] >>
  IMP_RES_TAC bir_exp_subst1_bool >>
  FULL_SIMP_TAC std_ss []
) >>
(* Second, we use bir_assign_exec to resolve effects of
 * execution: *)
Cases_on `v` >> rename1 `(BVar vname vtype)` >>
IMP_RES_TAC bir_assign_exec >>
Cases_on `s.bst_environ` >> rename1 `BEnv f` >>
PAT_X_ASSUM ``!f'. p1 ==> p2``
            (fn thm =>
               ASSUME_TAC (SPEC ``f:string -> bir_val_t option``
                                thm
                          )
            ) >>
PAT_X_ASSUM ``!f'. _``
            (fn thm =>
               ASSUME_TAC (SPEC ``f:string -> bir_val_t option``
                                thm
                          )
            ) >>
(* Split up assumption on variable initialisation of
 * Assign statement, in order to use initialisation of v. *)
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      bir_env_vars_are_initialised_INSERT,
                      bir_is_well_typed_stmtB_def] >>

IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
RW_TAC std_ss [] >>
(* Expand definitions in the goal: we are now proving that one
 * arbitrary variable v2 among the variables of post must
 * be initialised. *)
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
         [bir_env_vars_are_initialised_def] >>
REPEAT STRIP_TAC >>
rename1 `v2 IN bir_vars_of_exp post` >>
Cases_on `v2` >>
rename1 `BVar vname2 vtype2 IN bir_vars_of_exp post` >>
(* The vehicle to prove the goal is the assumption which states
 * that

     bir_env_vars_are_initialised (BEnv f)
       (bir_vars_of_exp (bir_exp_subst1 (BVar vname vtype) ex post)

 * which together with the assumption

     BVar vname2 vtype2 IN bir_vars_of_exp post

 * proves the goal under two conditions: v and v2 are not equal, and
 * specifically their names must also not be equal. *)

(* Case: v2 is equal to v *)
(* Since we already have that
     SOME vtype = type_of_bir_val (bir_eval_exp ex (BEnv f))
 * we can just give witness
     (bir_eval_exp ex (BEnv f))
 * which results in a tautological goal.
 * (see bir_env_var_is_initialised_def)
 * Accordingly, we can continue with the other case. *)
REV_FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_weaken, bir_var_type_def] >>
Cases_on `BVar vname2 vtype2 = BVar vname vtype` >- (
  ASM_REWRITE_TAC [bir_env_var_is_initialised_def,
                   bir_var_type_def, bir_var_name_def,
                   bir_env_lookup_def,
                   finite_mapTheory.FLOOKUP_UPDATE] >>
  Q.EXISTS_TAC `va` >>
  FULL_SIMP_TAC std_ss [bir_var_t_11, combinTheory.UPDATE_APPLY]
) >>

(* Case: name of v2 is same as name of v *)
Cases_on `vname2 = vname` >- (
  (* Show that v2 was initialised in the initial state:
   * True since bir_vars_of_exp post were, and v2 is in
   * that set. *)
  subgoal `bir_env_var_is_initialised (BEnv f)
                                      (BVar vname2 vtype2)` >- (
    FULL_SIMP_TAC std_ss
      [bir_exp_subst1_USED_VARS,
       bir_env_vars_are_initialised_UNION] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
                  [bir_env_vars_are_initialised_def]
  ) >>
  (* We get that vtype = vtype2 which is a contradiction,
   * since we already have that the names are equal while
   * the variables as a whole are not. *)
  FULL_SIMP_TAC std_ss [bir_var_name_def,
                        bir_env_var_is_initialised_def,
                        bir_var_type_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_env_lookup_def, combinTheory.UPDATE_APPLY]
) >>

(* Some cleaning up... *)
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
	      [bir_var_name_def, bir_env_var_is_initialised_def,
	       bir_env_lookup_def,
	       finite_mapTheory.FLOOKUP_UPDATE,
	       bir_env_vars_are_initialised_def] >>

(* Proving the antecedent of assumption 2 gives the goal as
 * assumption: v2 is in vars of post, therefore it is also in
 * the vars of expression
     (bir_exp_subst1 (BVar vname vtype) ex post)
 * iff v2 is not equal to v, in the case their names are
 * not equal.
 * *)
subgoal `(BVar vname2 vtype2) IN
	   bir_vars_of_exp (bir_exp_subst1 (BVar vname vtype)
					   ex post
                           )` >- (
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [bir_exp_subst1_USED_VARS]
) >>
METIS_TAC [bir_var_name_def, bir_var_type_def, combinTheory.UPDATE_APPLY]
QED

(* Preservation of valid status for the Assign statement *)
Theorem bir_assign_valid_status:
  !s s' v ex post obs.
      (* Antecedents from outside the Hoare triple: *)
      bir_is_well_typed_stmtB (BStmt_Assign v ex) ==>
      (* Antecedents from within the Hoare triple: *)
      bir_is_bool_exp_env s.bst_environ
        (bir_exp_subst1 v ex post) ==>
      bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_stmtB (BStmt_Assign v ex)) ==>
      (bir_exec_stmtB (BStmt_Assign v ex) s = (obs,s')) ==>
      bir_is_valid_status s ==>
      bir_is_valid_status s'
Proof
REPEAT STRIP_TAC >>
Cases_on `v` >>
Cases_on `s.bst_environ` >>
subgoal `(s with
            bst_environ := BEnv ((s'' =+ (bir_eval_exp ex (BEnv f))) f) =
            s')` >- (
  METIS_TAC [bir_assign_exec]
) >>
RW_TAC std_ss [] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_status_def]
QED

(* Given the precondition holding in the initial state,
 * the postcondition must hold in the final state. *)
Theorem bir_assign_postcond:
  !s s' v ex post obs.
      (* Antecedents from outside the Hoare triple: *)
      bir_is_well_typed_stmtB (BStmt_Assign v ex) ==>
      (* Antecedents from within the Hoare triple: *)
      bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_stmtB (BStmt_Assign v ex)) ==>
      (bir_eval_exp (bir_exp_subst1 v ex post)
        s.bst_environ =
          SOME bir_val_true) ==>
      (bir_exec_stmtB (BStmt_Assign v ex) s = (obs,s')) ==>
      (bir_eval_exp post s'.bst_environ = SOME bir_val_true)
Proof
REPEAT STRIP_TAC >>
Cases_on `v` >>
Cases_on `s.bst_environ` >>
subgoal `(s with
            bst_environ :=
              BEnv ((s'' =+ (bir_eval_exp ex (BEnv f))) f
                   ) =
            s')` >- (
  METIS_TAC [bir_assign_exec]
) >>
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      bir_env_vars_are_initialised_INSERT] >>
FULL_SIMP_TAC std_ss [LET_DEF, bir_env_var_is_initialised_def] >>

`bir_env_lookup_type s'' (BEnv f) = SOME b` by (
  FULL_SIMP_TAC std_ss [bir_env_lookup_type_def, bir_var_type_def, bir_var_name_def]
) >>

FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def, bir_var_type_def, bir_var_name_def] >>
IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
IMP_RES_TAC bir_eval_exp_subst1_env >>
RW_TAC std_ss []
QED

(* Theorem stating the soundness of the precondition {e/v}Q for
 * the statement Assign v:=e, with the postcondition Q. *)
(* {{e/v}Q} Assign v:=e {Q} *)
Theorem bir_triple_exec_stmtB_assign_thm:
  !v ex post.
      bir_is_well_typed_stmtB (BStmt_Assign v ex) ==>
      bir_exec_stmtB_triple (BStmt_Assign v ex) 
        (bir_exp_subst1 v ex post) post
Proof
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
subgoal `bir_is_bool_exp_env s'.bst_environ post` >- (
  METIS_TAC [bir_assign_bool_exp_env]
) >>
subgoal `bir_is_valid_status s'` >- (
  METIS_TAC [bir_assign_valid_status]
) >>
subgoal `bir_eval_exp post s'.bst_environ = SOME bir_val_true` >- (
  METIS_TAC [bir_assign_postcond]
) >>
FULL_SIMP_TAC std_ss []
QED

Theorem bir_env_vars_are_initialised_observe_INSERT[local]:
  !e oid ec el obf.
      bir_env_vars_are_initialised e
        (bir_vars_of_stmtB (BStmt_Observe oid ec el obf)) ==>
      bir_env_vars_are_initialised e (bir_vars_of_exp ec)
Proof
REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_vars_of_stmtB_def,
                      listTheory.LIST_TO_SET,
                      pred_setTheory.IMAGE_INSERT,
                      pred_setTheory.BIGUNION_INSERT,
                      bir_env_vars_are_initialised_UNION]
QED

(*
 TODO: this and similar theorems should maybe be moved to bir-support
 *)
Theorem bir_observe_state_invar:
  !s s' oid ec el obf obs.
      (* Antecedents from outside the Hoare triple: *)
      bir_is_well_typed_stmtB (BStmt_Observe oid ec el obf) ==>
      (* Antecedents from within the Hoare triple: *)
      bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_stmtB (BStmt_Observe oid ec el obf)) ==>
      (bir_exec_stmtB (BStmt_Observe oid ec el obf) s = (obs, s')) ==>
      (s = s')
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def, bir_exec_stmt_observe_def,
  bir_is_well_typed_stmtB_def, bir_is_bool_exp_GSYM] >>
IMP_RES_TAC bir_env_vars_are_initialised_observe_INSERT >>
REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                      bir_mk_bool_val_inv] >>

FULL_SIMP_TAC std_ss [LET_DEF, combinTheory.o_DEF, bir_vars_of_stmtB_def] >>

`~(EXISTS IS_NONE (MAP (\e. bir_eval_exp e s.bst_environ) el))` by (
  REWRITE_TAC [listTheory.EXISTS_NOT_EVERY, optionTheory.IS_NONE_EQ_NONE] >>

  Q.PAT_ASSUM `EVERY A B` (fn thm1 => Q.PAT_ASSUM `bir_env_vars_are_initialised A B` (fn thm2 => REPEAT (POP_ASSUM (K ALL_TAC)) >> ASSUME_TAC thm1 >> ASSUME_TAC thm2)) >>

  FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  GEN_TAC >>
  Cases_on `~MEM e el` >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  Q.PAT_X_ASSUM `!x. A ==> B` IMP_RES_TAC >>
  `bir_env_vars_are_initialised s.bst_environ (bir_vars_of_exp e)` by (
    METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET,
               pred_setTheory.SUBSET_BIGUNION_I, pred_setTheory.IMAGE_IN, listTheory.MEM]
  ) >>
  METIS_TAC [type_of_bir_exp_THM_with_init_vars, optionTheory.NOT_NONE_SOME, optionTheory.IS_SOME_EXISTS]
) >>

Cases_on `bir_eval_bool_exp ec s.bst_environ` >> (
  FULL_SIMP_TAC std_ss [LET_DEF]
)
QED

(* Theorem stating the soundness of the precondition Q for
 * the statement Observe ex, with the postcondition Q. *)
(* {Q} Observe ex {Q} *)
Theorem bir_triple_exec_stmtB_observe_thm:
  !oid ec el obf post.
      bir_is_well_typed_stmtB (BStmt_Observe oid ec el obf) ==>
      bir_exec_stmtB_triple (BStmt_Observe oid ec el obf) post post
Proof
REWRITE_TAC [bir_exec_stmtB_triple_def, bir_pre_post_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
METIS_TAC [bir_observe_state_invar]
QED

Definition bir_wp_exec_stmtB_def:
  (bir_wp_exec_stmtB (BStmt_Assert ex) post =
    (BExp_BinExp BIExp_And ex post)) /\
  (bir_wp_exec_stmtB (BStmt_Assume ex) post =
    (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post)) /\
  (bir_wp_exec_stmtB (BStmt_Assign v ex) post =
    (bir_exp_subst1 v ex post)) /\
  (bir_wp_exec_stmtB (BStmt_Observe oid ec el obf) post = post)
End

Theorem bir_wp_exec_stmtB_sound_thm:
  !stm post.
      bir_is_well_typed_stmtB stm ==>
      bir_exec_stmtB_triple stm (bir_wp_exec_stmtB stm post) post
Proof
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Cases_on `stm` >>
FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
                      bir_triple_exec_stmtB_assign_thm,
                      bir_triple_exec_stmtB_assert_thm,
                      bir_triple_exec_stmtB_assume_thm,
                      bir_triple_exec_stmtB_observe_thm] >> (
  RW_TAC std_ss []
)
QED

Theorem bir_wp_exec_stmtB_bool_thm:
  !stm post.
      bir_is_well_typed_stmtB stm ==>
      bir_is_bool_exp post ==>
      bir_is_bool_exp (bir_wp_exec_stmtB stm post)
Proof
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
Cases_on `stm` >> (
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
                        bir_triple_exec_stmtB_assign_thm,
                        bir_triple_exec_stmtB_assert_thm,
                        bir_triple_exec_stmtB_assume_thm,
                        bir_triple_exec_stmtB_observe_thm,
                        bir_is_well_typed_stmtB_def,
                        bir_is_bool_exp_GSYM,
                        bir_is_bool_exp_REWRS] >> (
    RW_TAC std_ss []
  ) >> (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_def,
                          bir_exp_subst1_TYPE_EQ]
  )
)
QED

(*
   -------------------------------------------------------------
                    Multiple basic statements
   -------------------------------------------------------------
*)
(* Hoare triple for several basic statements *)
Definition bir_exec_stmtsB_triple_def:
  bir_exec_stmtsB_triple stmts pre post =
    !s s' obs obs' c c'.
      (EVERY
        (\stmt.
          bir_env_vars_are_initialised s.bst_environ
            (bir_vars_of_stmtB stmt)
        ) stmts
      ) ==>
      (bir_exec_stmtsB stmts (obs, c, s) = (obs', c', s')) ==>
      (bir_pre_post s pre s' post)
End


Definition bir_wp_exec_stmtsB_def:
  (bir_wp_exec_stmtsB [] post = post) /\
  (bir_wp_exec_stmtsB (stmt::stmts) post = 
    bir_wp_exec_stmtB stmt (bir_wp_exec_stmtsB stmts post)
  )
End

Theorem bir_wp_exec_stmtsB_bool_thm:
  !stmts post.
      EVERY bir_is_well_typed_stmtB stmts ==>
      bir_is_bool_exp post ==>
      bir_is_bool_exp (bir_wp_exec_stmtsB stmts post)
Proof
REPEAT GEN_TAC >>
Induct_on `stmts` >- (
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def,
                        bir_exec_stmtsB_triple_def,
                        bir_exec_stmtsB_def]
) >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def, listTheory.EVERY_DEF,
                      bir_wp_exec_stmtB_bool_thm]
QED

Theorem exec_preserves_initialized_vars_thm[local]:
  !r h st stmts.
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
      )
Proof
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
ASSUME_TAC (ISPECL [``(\stmt:'a bir_stmt_basic_t.
                        bir_env_vars_are_initialised st.bst_environ
                          (bir_vars_of_stmtB stmt))``,
                    ``(\stmt:'a bir_stmt_basic_t.
                        bir_env_vars_are_initialised r.bst_environ
                          (bir_vars_of_stmtB stmt))``]
                   listTheory.EVERY_MONOTONIC) >>
REV_FULL_SIMP_TAC std_ss [bir_varinit_invar_bstmt]
QED

Theorem bir_assumviol_exec_stmtsB:
  !obs c s stmts.
      (s.bst_status = BST_AssumptionViolated) ==>
      (bir_exec_stmtsB stmts (obs, c, s) = (REVERSE obs, c, s))
Proof
REPEAT GEN_TAC >>
Cases_on `stmts` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_stmtsB_def]
)
QED

Theorem bir_running_by_exclusion:
  !s.
      bir_is_valid_status s ==>
      (s.bst_status <> BST_AssumptionViolated) ==>
      (s.bst_status = BST_Running)
Proof
REPEAT STRIP_TAC >>
Cases_on `s.bst_status` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_valid_status_def]
QED

Theorem bir_wp_exec_stmtsB_sound_thm:
  !stmts post.
      EVERY bir_is_well_typed_stmtB stmts ==>
      (bir_exec_stmtsB_triple stmts
         (bir_wp_exec_stmtsB stmts post) post
      )
Proof
REPEAT GEN_TAC >>
  Induct_on `stmts` >-(
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
        FULL_SIMP_TAC std_ss [bir_assumviol_exec_stmtsB] >>
        REV_FULL_SIMP_TAC std_ss [],

        (* Case: Running in s. *)
        SUBGOAL_THEN ``s'.bst_status = BST_Running``
                     (fn thm => ASSUME_TAC thm) >- (
          FULL_SIMP_TAC std_ss [bir_running_by_exclusion]
        ) >>
        (* Use induction hypothesis *)
        FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>
        PAT_X_ASSUM ``!s s' obs obs' c c'. _`` (fn thm =>
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

    FULL_SIMP_TAC std_ss [bir_assumviol_exec_stmtsB] >>
    REV_FULL_SIMP_TAC std_ss []
  ]
QED

(*
   -------------------------------------------------------------
             Whole blocks: basic and end statements
   -------------------------------------------------------------
*)
(* Hoare triple for a block *)
Definition bir_exec_block_jmp_triple_def:
  bir_exec_block_jmp_triple p bl pre post l =
    !s l1 c1 s'.
      bir_env_vars_are_initialised s.bst_environ
                                   (bir_vars_of_block bl) ==>
      (bir_exec_block p bl s = (l1,c1,s')) ==>
      (s.bst_status = BST_Running) ==>
      bir_is_bool_exp_env s.bst_environ pre ==>
      (bir_eval_exp pre (s.bst_environ) = SOME bir_val_true) ==>
      (
        (bir_is_bool_exp_env s'.bst_environ post /\
         bir_is_valid_status s' /\ 
         (bir_eval_exp post (s'.bst_environ) = SOME bir_val_true) /\
         (s'.bst_pc = bir_block_pc l)
        ) \/ (
         (s'.bst_status = BST_AssumptionViolated)
        )
      )
End

Theorem SUBSET_BIGUNION_IMAGE_thm[local]:
  !x s f.
      (x IN s) ==> ((f x) SUBSET (BIGUNION (IMAGE f s)))
Proof
SIMP_TAC pure_ss [pred_setTheory.IMAGE_DEF,
                  pred_setTheory.BIGUNION,
                  pred_setTheory.SUBSET_DEF] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
Q.EXISTS_TAC `f x` >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
Q.EXISTS_TAC `x` >>
METIS_TAC []
QED

Theorem bir_vars_are_initialized_block_then_every_stmts_thm[local]:
  !st bl.
      (bir_env_vars_are_initialised st.bst_environ
                                    (bir_vars_of_block bl)) ==>
      (EVERY
        (\stmt.
          bir_env_vars_are_initialised st.bst_environ
            (bir_vars_of_stmtB stmt)
        ) bl.bb_statements
      )
Proof
FULL_SIMP_TAC std_ss [bir_vars_of_block_def,
                      listTheory.EVERY_MEM] >>
REPEAT STRIP_TAC >>

METIS_TAC [bir_env_vars_are_initialised_UNION,
           SUBSET_BIGUNION_IMAGE_thm,
           bir_env_vars_are_initialised_SUBSET]
QED

Theorem bir_exec_block_jmp_triple_wp_thm:
  !p bl post l.
      bir_is_well_typed_block bl ==>
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l))) ==>
      MEM l (bir_labels_of_program p) ==>
      (bir_exec_block_jmp_triple p bl 
        (bir_wp_exec_stmtsB bl.bb_statements post) post l)
Proof
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
              ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:(num # 'a) list`, `ns0`,
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
QED

Definition bir_exec_block_cjmp_triple_def:
  bir_exec_block_cjmp_triple p bl pre post1 l1 post2 l2 =
    !s obs' c1 s'.
      bir_env_vars_are_initialised s.bst_environ
        (bir_vars_of_block bl) ==>
      (bir_exec_block p bl s = (obs',c1,s')) ==>
      (s.bst_status = BST_Running) ==>
      bir_is_bool_exp_env s.bst_environ pre ==>
      (bir_eval_exp pre (s.bst_environ) = SOME bir_val_true) ==>
      (bir_is_valid_status s' /\
       (
         (bir_is_bool_exp_env s'.bst_environ post1 /\
         (bir_eval_exp post1 (s'.bst_environ) = SOME bir_val_true) /\
         (s'.bst_pc = bir_block_pc l1)
       ) \/ (
         bir_is_bool_exp_env s'.bst_environ post2 /\
         (bir_eval_exp post2 (s'.bst_environ) = SOME bir_val_true) /\
         (s'.bst_pc = bir_block_pc l2)
       )
      ) \/ (
        (s'.bst_status = BST_AssumptionViolated)
      )
     )
End

Theorem bir_exec_block_cjmp_triple_wp_thm:
  !p bl e post1 l1 post2 l2.
      bir_is_well_typed_block bl ==>
      (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1)
                                            (BLE_Label l2)
                              )
      ) ==>
      bir_is_bool_exp post1 ==>
      bir_is_bool_exp post2 ==>
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
        ) post1 l1 post2 l2)
Proof
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
  ASSUME_TAC (Q.SPECL [`s`, `ns2`, `[]:(num # 'a) list`, `ns0`, `0:num`,
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
    IMP_RES_TAC (el 6 (CONJUNCTS bir_is_bool_exp_env_REWRS)) >>
    IMP_RES_TAC (el 6 (CONJUNCTS bir_is_bool_exp_env_REWRS))
  ) >>
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                        bir_mk_bool_val_inv, LET_DEF] >>
  REV_FULL_SIMP_TAC std_ss [bir_pre_post_def] >>
  (* Proves that since
   *   eval_bool (q1 /\ q2)
   * then
   *   eval_bool q1 /\ eval_bool q2 *)
  FULL_SIMP_TAC std_ss [Abbr `post_stmts`] >>
  IMP_RES_TAC (el 6 (CONJUNCTS bir_is_bool_exp_env_REWRS)) >>
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO,
                        bir_mk_bool_val_true_thm,
                        bir_eval_bool_exp_BExp_BinExp_REWRS] >>
  REPEAT (Q.PAT_X_ASSUM `!bo._` (fn _ => ALL_TAC)) >>
  Cases_on `bir_eval_bool_exp e ns2.bst_environ` >- (
    FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def,
                          bir_eval_label_exp_def,
                          bir_exec_stmt_jmp_to_label_def] >>
    REV_FULL_SIMP_TAC std_ss [Abbr `st2`,
                              bir_state_is_terminated_def] >>
    RW_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [Abbr `q1`] >>
    IMP_RES_TAC (el 6 (CONJUNCTS bir_is_bool_exp_env_REWRS)) >>
    REPEAT (Q.PAT_X_ASSUM `!bo._` (fn _ => ALL_TAC)) >>
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
  IMP_RES_TAC (el 6 (CONJUNCTS bir_is_bool_exp_env_REWRS)) >>
  REPEAT (Q.PAT_X_ASSUM `!bo._` (fn _ => ALL_TAC)) >>
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
QED


(*
   -------------------------------------------------------------
             Entire program up to label (DAG of blocks)
   -------------------------------------------------------------
*)
  
Definition bir_exec_to_labels_or_assumviol_triple_def:
  bir_exec_to_labels_or_assumviol_triple p l ls pre post =
  !s r.
    bir_env_vars_are_initialised s.bst_environ
                                 (bir_vars_of_program p) ==>
    ((s.bst_pc.bpc_index = 0) /\ (s.bst_pc.bpc_label = l)) ==>
    (s.bst_status = BST_Running) ==>
    bir_is_bool_exp_env s.bst_environ pre ==>
    (bir_eval_exp pre (s.bst_environ) = SOME bir_val_true) ==>
    ((bir_exec_to_labels ls p s) = r) ==>
    (?l1 c1 c2 s'.
      (r = BER_Ended l1 c1 c2 s') /\
      (
        (
	  (s'.bst_status = BST_Running) /\
	  bir_is_bool_exp_env s'.bst_environ (post s'.bst_pc.bpc_label) /\
	  ((bir_eval_exp (post s'.bst_pc.bpc_label) s'.bst_environ) = SOME bir_val_true) /\
	  ((s'.bst_pc.bpc_index = 0) /\ (s'.bst_pc.bpc_label IN ls))
        ) \/ (
          (s'.bst_status = BST_AssumptionViolated)
        )
      )
    )
End

Theorem bir_exec_to_labels_pre_F:
  !p l ls post.
    bir_exec_to_labels_or_assumviol_triple p l ls bir_exp_false post
Proof
FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_exec_to_labels_or_assumviol_triple_def, bir_exp_false_def,
               bir_val_true_def, bir_eval_exp_def, word1_distinct]
QED

Theorem bir_env_vars_are_initialised_prog_block_thm[local]:
  !p l bl env.
      bir_is_valid_program p ==>
      bir_env_vars_are_initialised env (bir_vars_of_program p) ==>
      MEM l (bir_labels_of_program p) ==>
      (SND (THE (bir_get_program_block_info_by_label p l)) = bl) ==>
      bir_env_vars_are_initialised env (bir_vars_of_block bl)
Proof
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
QED
    
Theorem bir_get_current_block_SOME_MEM[local]:
  !l pc bl.
      bir_is_valid_program (BirProgram l) ==>
      (bir_get_current_block (BirProgram l) pc = SOME bl) ==>
      (MEM bl l)
Proof
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
QED

Theorem bir_exec_block_running_at_least_one_step[local]:
  !p bl st l' c' st'.
      (bir_exec_block p bl st = (l',c',st')) ==>
      (st'.bst_status = BST_Running) ==>
      (0 < c')
Proof
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
QED

(*
FIRST CHANGE TO a PROOF for POST MAP
this is only needed if l1 in ls to ensure  (bir_is_bool_exp post')
bir_is_bool_exp (post l1)
*)
Definition bir_wp_post_map_contains_bool_exp_def:
  bir_wp_post_map_contains_bool_exp post = (!l1. bir_is_bool_exp (post l1))
End


Theorem bir_exec_to_labels_or_assumviol_triple_jmp:
  !p l bl l1 ls post post'.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      MEM l1 (bir_labels_of_program p) ==>
      (SND(THE(bir_get_program_block_info_by_label p l)) = bl) ==>
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l1))) ==>
      (((l1 IN ls) ==> (post' = (post l1))) /\
       ((~(l1 IN ls)) ==>
        (bir_exec_to_labels_or_assumviol_triple p l1 ls post' post) /\
        (bir_is_bool_exp post')
       )
      ) ==>
      (bir_exec_to_labels_or_assumviol_triple p l ls
        (bir_wp_exec_stmtsB bl.bb_statements post') post
      )
Proof
(* Expand definitions *)
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
SIMP_TAC std_ss [bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "s'" is the state resulting from execution with
 * bir_exec_to_labels from s. *)
Q.ABBREV_TAC `s' = bir_exec_to_labels ls p s` >>
Q.ABBREV_TAC `cnd = (l1 IN ls /\ (post' = (post l1)) \/
  bir_exec_to_labels_or_assumviol_triple p l1 ls post' post)` >>
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
subgoal `bir_is_bool_exp post'` >- (
  Cases_on `l1 IN ls` >> (
    FULL_SIMP_TAC std_ss [Abbr `cnd`, bir_wp_post_map_contains_bool_exp_def]
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
    EXISTS_TAC ``st10:(num # 'a) list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* Case: We have not reach an end label *)
  FULL_SIMP_TAC std_ss [Abbr `cnd`, LET_DEF, bir_state_COUNT_PC_def,
                        bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_or_assumviol_triple_def] >>
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
    EXISTS_TAC ``(st10 ++ l1'):(num # 'a) list`` >>
    EXISTS_TAC ``(st11 + c1):num`` >>
    EXISTS_TAC ``c2:num`` >>
    EXISTS_TAC ``s'':bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ),

  (* Case: st12 is AssumptionViolated *)
  quantHeuristicsLib.QUANT_TAC [("s''", `st12`, [])] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF,
                                        bir_state_COUNT_PC_def,
                                        bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def] >>
  subgoal `bir_state_is_terminated st12` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  IMP_RES_TAC bir_exec_to_labels_n_REWR_TERMINATED >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  quantHeuristicsLib.QUANT_TAC [("l1", `(st10 ++ [])`, []),
                                ("c1", `st11`, []),
                                ("c2", `0`, [])] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
QED

Theorem bir_exec_to_labels_or_assumviol_triple_cjmp:
  !p l bl e l1 l2 ls post post1' post2'.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      MEM l1 (bir_labels_of_program p) ==>
      MEM l2 (bir_labels_of_program p) ==>
      (SND (THE (bir_get_program_block_info_by_label p l)) = bl) ==>
      (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1)
                                            (BLE_Label l2))
      ) ==>
      (((l1 IN ls) ==> (post1' = (post l1))) /\
       ((~(l1 IN ls)) ==>
         bir_exec_to_labels_or_assumviol_triple p l1 ls post1' post /\
         bir_is_bool_exp post1'
       )
      ) ==>
      (((l2 IN ls) ==> (post2' = (post l2))) /\
       ((~(l2 IN ls)) ==>
         bir_exec_to_labels_or_assumviol_triple p l2 ls post2' post /\
         bir_is_bool_exp post2'
       )
      ) ==>
      (bir_exec_to_labels_or_assumviol_triple p l ls
        (bir_wp_exec_stmtsB bl.bb_statements 
        (
          (BExp_BinExp BIExp_And 
            (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e)
                                  post1'
            )
            (BExp_BinExp BIExp_Or e post2')
          )
        )
      ) post)
Proof
(* Expand definitions *)
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
SIMP_TAC std_ss [bir_exec_to_labels_or_assumviol_triple_def] >>
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
subgoal `bir_is_bool_exp post1'` >- (
  Cases_on `l1 IN ls` >> (
    FULL_SIMP_TAC std_ss [bir_wp_post_map_contains_bool_exp_def]
  )
) >>
FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp post2'` >- (
  Cases_on `l2 IN ls` >> (
    FULL_SIMP_TAC std_ss [bir_wp_post_map_contains_bool_exp_def]
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
    EXISTS_TAC ``st10:(num # 'a) list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* We have not reached an end label *)
  FULL_SIMP_TAC std_ss [LET_DEF,
                        bir_state_COUNT_PC_def, bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_or_assumviol_triple_def] >>
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
    EXISTS_TAC ``(st10 ++ l1'):(num # 'a) list`` >>
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
    EXISTS_TAC ``st10:(num # 'a) list`` >>
    EXISTS_TAC ``st11:num`` >>
    EXISTS_TAC ``1:num`` >>
    EXISTS_TAC ``st12:bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  (* We have not reached an end label *)
  FULL_SIMP_TAC std_ss [LET_DEF,
                        bir_state_COUNT_PC_def, bir_block_pc_def] >>
  FULL_SIMP_TAC (srw_ss()) [bir_exec_to_labels_or_assumviol_triple_def] >>
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
    EXISTS_TAC ``(st10 ++ l1'):(num # 'a) list`` >>
    EXISTS_TAC ``(st11 + c1):num`` >>
    EXISTS_TAC ``c2:num`` >>
    EXISTS_TAC ``s'':bir_state_t`` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ),

  (* Case 3: st12 has status AssumptionViolated *)
  quantHeuristicsLib.QUANT_TAC [("s''", `st12`, [])] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF,
                                        bir_state_COUNT_PC_def,
                                        bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def] >>
  subgoal `bir_state_is_terminated st12` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  IMP_RES_TAC bir_exec_to_labels_n_REWR_TERMINATED >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  quantHeuristicsLib.QUANT_TAC [("l1", `(st10 ++ [])`, []),
                                ("c1", `st11`, []),
                                ("c2", `0`, [])] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
]
QED

(*
   -------------------------------------------------------------
                  Procedure for WP in DAG
   -------------------------------------------------------------
*)

Definition bir_wp_exec_of_block_def:
  bir_wp_exec_of_block p l ls wps post = 
    case FLOOKUP wps l of
      SOME wp => SOME wps
    | NONE    => (
        let bl = SND
                   (THE(bir_get_program_block_info_by_label p l)) in
          case bl.bb_last_statement of
            BStmt_Jmp (BLE_Label l1) => (
              if (l1 IN ls)
              then
		SOME (wps |+ (l, (bir_wp_exec_stmtsB
				   bl.bb_statements (post l1)
				 )))
              else
		case FLOOKUP wps l1 of
		  NONE => NONE
		| SOME wp =>
		    SOME (wps |+ (l, (bir_wp_exec_stmtsB
				       bl.bb_statements wp
				     )))
            )
          | BStmt_CJmp e (BLE_Label l1) (BLE_Label l2) => (
              if (l1 IN ls)
              then
                if (l2 IN ls)
                then
                  SOME (wps |+ (l,
		    (bir_wp_exec_stmtsB bl.bb_statements 
		      (BExp_BinExp BIExp_And
			(BExp_BinExp BIExp_Or
			  (BExp_UnaryExp BIExp_Not e) (post l1))
			(BExp_BinExp BIExp_Or e (post l2))
		      )
		    )))
                else
                  case FLOOKUP wps l2 of
                    NONE => NONE
                  | SOME wp2 => SOME (wps |+ (l,
                      (bir_wp_exec_stmtsB bl.bb_statements 
                        (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_Or
                            (BExp_UnaryExp BIExp_Not e) (post l1))
                          (BExp_BinExp BIExp_Or e wp2)
                        )
                      )))
              else
                if (l2 IN ls)
                then
                  case FLOOKUP wps l1 of
                    NONE => NONE
                  | SOME wp1 => SOME (wps |+ (l,
                      (bir_wp_exec_stmtsB bl.bb_statements 
                        (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_Or
                            (BExp_UnaryExp BIExp_Not e) wp1)
                          (BExp_BinExp BIExp_Or e (post l2))
                        )
                      )))
                else
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
      )
End

Definition bir_jmp_direct_labels_only_def:
  bir_jmp_direct_labels_only (BirProgram l) =
    (!bl. (MEM bl l) ==>
      (?l1. bl.bb_last_statement = BStmt_Jmp (BLE_Label l1)) \/
      (?e l1 l2.
         bl.bb_last_statement = BStmt_CJmp e (BLE_Label l1)
                                             (BLE_Label l2)
      )
    )
End

Definition bir_jmp_direct_labels_only_exec_def:
  (bir_jmp_direct_labels_only_exec (BirProgram []) = T) /\
  (bir_jmp_direct_labels_only_exec (BirProgram (h::l)) =
    ((case h.bb_last_statement of
      BStmt_Jmp (BLE_Label _) => T
    | BStmt_CJmp _ (BLE_Label _) (BLE_Label _) => T
    | _ => F) /\
  (bir_jmp_direct_labels_only_exec (BirProgram l))))
End

Theorem bir_jmp_direct_labels_only_exec_eq_thm:
  !p.
    (bir_jmp_direct_labels_only p =
      bir_jmp_direct_labels_only_exec p)
Proof
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
QED

Definition bir_edge_in_prog_def:
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
          )
End

Definition bir_edges_blocks_in_prog_def:
  bir_edges_blocks_in_prog (BirProgram bls) l1 =
    !l2. (bir_edge_in_prog (BirProgram bls) l1 l2) ==>
         (?bl2. ( (MEM bl2 bls) /\ (bl2.bb_label = l2) ))
End

Definition bir_targets_in_prog_exec_def:
  bir_targets_in_prog_exec p l1 =
    case bir_get_program_block_info_by_label p l1 of
      NONE => []
    | SOME (_,bl1) => 
        case bl1.bb_last_statement of
          BStmt_Jmp (BLE_Label l2) => [l2]
        | BStmt_CJmp e (BLE_Label l2) (BLE_Label l3) => [l2;l3]
        | BStmt_Halt e => []
        | _ => []
End

Definition bir_edges_blocks_in_prog_exec_def:
  bir_edges_blocks_in_prog_exec (BirProgram bls) l1 =
    EVERY (\l2. EXISTS (\bl2. bl2.bb_label = l2) bls)
          (bir_targets_in_prog_exec (BirProgram bls) l1)
End

Theorem bir_edges_blocks_in_prog_exec_eq_thm:
  !p l1.
      bir_is_valid_labels p ==>
      (bir_edges_blocks_in_prog p l1 =
        bir_edges_blocks_in_prog_exec p l1
      )
Proof
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
QED

val bir_stmt_end_ss = rewrites (type_rws ``:bir_stmt_end_t``);
val bir_label_exp_ss = rewrites (type_rws ``:bir_label_exp_t``);

Theorem FEVERY_FEVERY_DRESTRICT_thm[local]:
  !P M S.
      FEVERY P M ==> FEVERY P (DRESTRICT M S)
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
              [finite_mapTheory.FEVERY_DEF,
               finite_mapTheory.FDOM_DRESTRICT,
               finite_mapTheory.DRESTRICT_DEF]
QED

Theorem bir_wp_exec_of_block_bool_thm:
  !p l ls wps wps' post.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps ==>
      ((bir_wp_exec_of_block p l ls wps post) = SOME wps') ==>
      (FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps')
Proof
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
    Cases_on `l1 IN ls` >| [
      FULL_SIMP_TAC std_ss [] >>
      subgoal `bir_is_bool_exp (
		 bir_wp_exec_stmtsB bl.bb_statements (post l1)
	       )` >- (
	  FULL_SIMP_TAC std_ss [bir_wp_post_map_contains_bool_exp_def] >>
	  METIS_TAC [bir_is_well_typed_program_def,
		     bir_is_well_typed_block_def,
		     listTheory.EVERY_MEM,
		     bir_wp_exec_stmtsB_bool_thm]
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      Q.PAT_X_ASSUM `FUPDATE A B = C`
		    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
					      (post l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			    FEVERY_FEVERY_DRESTRICT_thm],

      FULL_SIMP_TAC std_ss [] >>
      Cases_on `l1 IN FDOM wps` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      subgoal `bir_is_bool_exp
		 (bir_wp_exec_stmtsB bl.bb_statements
				     (FAPPLY wps l1)
		 )` >- (
	FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_DEF] >>
	METIS_TAC [bir_is_well_typed_program_def,
		   bir_is_well_typed_block_def,
		   listTheory.EVERY_MEM,
		   bir_wp_exec_stmtsB_bool_thm]
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      Q.PAT_X_ASSUM `FUPDATE A B = C`
		    (fn thm => ASSUME_TAC (GSYM thm)) >>
      Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
					      (wps ' l1)` >>
      FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			    FEVERY_FEVERY_DRESTRICT_thm]
    ],

    subgoal `bir_is_well_typed_stmtE
	      (BStmt_CJmp e (BLE_Label l1)
			    (BLE_Label l2))` >- (
      METIS_TAC [bir_is_well_typed_program_def,
		 listTheory.EVERY_MEM,
		 bir_is_well_typed_block_def]
    ) >>
    Cases_on `l1 IN ls` >| [
      FULL_SIMP_TAC std_ss [] >>
      Cases_on `l2 IN ls` >| [
        FULL_SIMP_TAC std_ss [] >>
	Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
		       (BExp_BinExp BIExp_Or
			 (BExp_UnaryExp BIExp_Not e)
			 (post l1)
		       )
		       (BExp_BinExp BIExp_Or e (post l2)))` >>
	subgoal `bir_is_bool_exp exp1` >- (
	  FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS,
				finite_mapTheory.FEVERY_DEF,
				bir_is_well_typed_stmtE_def,
				bir_is_bool_exp_GSYM, Abbr `exp1`,
                                bir_wp_post_map_contains_bool_exp_def]
	) >>
	subgoal `bir_is_bool_exp
		  (bir_wp_exec_stmtsB bl.bb_statements exp1)` >- (
	  FULL_SIMP_TAC std_ss [] >>
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
			      FEVERY_FEVERY_DRESTRICT_thm],

        FULL_SIMP_TAC std_ss [] >>
        Cases_on `l2 IN FDOM wps` >> (
          FULL_SIMP_TAC std_ss []
        ) >>
	Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
		       (BExp_BinExp BIExp_Or
			 (BExp_UnaryExp BIExp_Not e)
			 (post l1)
		       )
		       (BExp_BinExp BIExp_Or e (wps ' l2)))` >>
	  subgoal `bir_is_bool_exp exp1` >- (
	    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS,
				  finite_mapTheory.FEVERY_DEF,
				  bir_is_well_typed_stmtE_def,
				  bir_is_bool_exp_GSYM, Abbr `exp1`,
				  bir_wp_post_map_contains_bool_exp_def]
	  ) >>
	  subgoal `bir_is_bool_exp
		    (bir_wp_exec_stmtsB bl.bb_statements exp1)` >- (
	    FULL_SIMP_TAC std_ss [] >>
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
        ],

        FULL_SIMP_TAC std_ss [] >>
        Cases_on `l2 IN ls` >| [
          FULL_SIMP_TAC std_ss [] >>
	  Cases_on `l1 IN FDOM wps` >> (
	    FULL_SIMP_TAC std_ss []
	  ) >>
          Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
		          (BExp_BinExp BIExp_Or
                            (BExp_UnaryExp BIExp_Not e)
			    (wps ' l1)
		        )
		       (BExp_BinExp BIExp_Or e (post l2)))` >>
	  subgoal `bir_is_bool_exp exp1` >- (
	    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS,
				  finite_mapTheory.FEVERY_DEF,
				  bir_is_well_typed_stmtE_def,
				  bir_is_bool_exp_GSYM, Abbr `exp1`,
				  bir_wp_post_map_contains_bool_exp_def]
	  ) >>
	  subgoal `bir_is_bool_exp
		    (bir_wp_exec_stmtsB bl.bb_statements exp1)` >- (
	    FULL_SIMP_TAC std_ss [] >>
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
				FEVERY_FEVERY_DRESTRICT_thm],

          FULL_SIMP_TAC std_ss [] >>
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
	      FULL_SIMP_TAC std_ss [] >>
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
      ]
    ]
) >>
FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF]
QED


Theorem bir_wp_exec_of_block_sound_thm:
  !p l ls post wps wps'.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_edges_blocks_in_prog p l ==>
      FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps ==>
      FEVERY (\(l1, wp1).
               (bir_exec_to_labels_or_assumviol_triple p l1 ls wp1 post)) wps ==>
      ((bir_wp_exec_of_block p l ls wps post) = SOME wps') ==>
      (FEVERY (\(l1, wp1).
                (bir_exec_to_labels_or_assumviol_triple p l1 ls wp1 post)) wps')
Proof
REPEAT STRIP_TAC >>
Cases_on `p` >>
Q.RENAME1_TAC `BirProgram bls` >>
FULL_SIMP_TAC std_ss [bir_wp_exec_of_block_def,
                      bir_get_program_block_info_by_label_MEM,
                      LET_DEF] >>
Cases_on `FLOOKUP wps l` >> (
  FULL_SIMP_TAC std_ss []
) >>
subgoal `MEM bl bls` >- (
  METIS_TAC [bir_get_program_block_info_by_label_def,
	     INDEX_FIND_EQ_SOME_0, listTheory.MEM_EL]
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `bl.bb_last_statement` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >| [
  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  rename1 `BStmt_Jmp (BLE_Label l1)` >>
  Cases_on `l1 IN ls` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >| [
    subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls)
	       l ls
	       (bir_wp_exec_stmtsB bl.bb_statements
				   (post l1)
	       ) post` >- (
      ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `l1`,
			   `ls`, `post`]
			  bir_exec_to_labels_or_assumviol_triple_jmp) >>
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
					    (post l1)` >>
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			  FEVERY_FEVERY_DRESTRICT_thm],

    Cases_on `l1 IN FDOM wps` >> Cases_on `FLOOKUP wps l1` >> (
      FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF,
			    finite_mapTheory.FDOM_FUPDATE,
			    pred_setTheory.COMPONENT] >>
      FULL_SIMP_TAC (std_ss++bir_stmt_end_ss++bir_label_exp_ss) []
    ) >>
    subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls)
               l ls
               (bir_wp_exec_stmtsB bl.bb_statements
                                   (wps ' l1)
               ) post` >- (
      ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `l1`,
			   `ls`, `post`]
			  bir_exec_to_labels_or_assumviol_triple_jmp) >>
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
    RW_TAC std_ss [] >>
    Q.ABBREV_TAC `exp1 = bir_wp_exec_stmtsB bl.bb_statements
					    (wps ' l1)` >>
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			  FEVERY_FEVERY_DRESTRICT_thm]
  ],

  Cases_on `b0` >>
  Cases_on `b1` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DEF,
			finite_mapTheory.FDOM_FUPDATE,
			pred_setTheory.COMPONENT] >>
  FULL_SIMP_TAC (std_ss++bir_stmt_end_ss++bir_label_exp_ss) [] >>
  rename1 `BStmt_CJmp b (BLE_Label l1) (BLE_Label b'')` >>
  rename1 `BStmt_CJmp b (BLE_Label l1) (BLE_Label l2)` >>
  rename1 `BStmt_CJmp e (BLE_Label l1) (BLE_Label l2)` >>
  Cases_on `l1 IN ls` >> Cases_on `l2 IN ls` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >| [
    Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
			   (BExp_BinExp BIExp_Or
			     (BExp_UnaryExp BIExp_Not e)
			     (post l1)
			   )
			   (BExp_BinExp BIExp_Or e
						 (post l2)
			   )
			 )` >>
    subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls) l ls
	      (bir_wp_exec_stmtsB bl.bb_statements exp1)
	      post` >- (
      ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `e`, `l1`,
			   `l2`, `ls`, `post`]
		 bir_exec_to_labels_or_assumviol_triple_cjmp) >>
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
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			  FEVERY_FEVERY_DRESTRICT_thm],

    Cases_on `l2 IN FDOM wps` >> (
      FULL_SIMP_TAC std_ss []
    ) >>
    Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
			   (BExp_BinExp BIExp_Or
			     (BExp_UnaryExp BIExp_Not e)
			     (post l1)
			   )
			   (BExp_BinExp BIExp_Or e
						 (wps ' l2)
			   )
			 )` >>
    subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls) l ls
	      (bir_wp_exec_stmtsB bl.bb_statements exp1)
	      post` >- (
      ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `e`, `l1`,
			   `l2`, `ls`, `post`]
		 bir_exec_to_labels_or_assumviol_triple_cjmp) >>
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
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			  FEVERY_FEVERY_DRESTRICT_thm],

    Cases_on `l1 IN FDOM wps` >> (
      FULL_SIMP_TAC std_ss []
    ) >>
    Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
			   (BExp_BinExp BIExp_Or
			     (BExp_UnaryExp BIExp_Not e)
			     (wps ' l1)
			   )
			   (BExp_BinExp BIExp_Or e
						 (post l2)
			   )
			 )` >>
    subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls) l ls
	      (bir_wp_exec_stmtsB bl.bb_statements exp1)
	      post` >- (
      ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `e`, `l1`,
			   `l2`, `ls`, `post`]
		 bir_exec_to_labels_or_assumviol_triple_cjmp) >>
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
    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			  FEVERY_FEVERY_DRESTRICT_thm],


    Cases_on `l1 IN FDOM wps` >> Cases_on `l2 IN FDOM wps` >> (
      FULL_SIMP_TAC std_ss []
    ) >>
    Q.ABBREV_TAC `exp1 = (BExp_BinExp BIExp_And
			   (BExp_BinExp BIExp_Or
			     (BExp_UnaryExp BIExp_Not e)
			     (FAPPLY wps l1)
			   )
			   (BExp_BinExp BIExp_Or e
						 (FAPPLY wps l2)
			   )
			 )` >>
  subgoal `bir_exec_to_labels_or_assumviol_triple (BirProgram bls) l ls
	    (bir_wp_exec_stmtsB bl.bb_statements exp1)
	    post` >- (
    ASSUME_TAC (Q.SPECL [`BirProgram bls`, `l`, `bl`, `e`, `l1`,
			 `l2`, `ls`, `post`]
	       bir_exec_to_labels_or_assumviol_triple_cjmp) >>
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
  FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_FUPDATE,
			FEVERY_FEVERY_DRESTRICT_thm]
  ]
]
QED

Definition bir_bool_wps_map_def:
  bir_bool_wps_map wps =
    (FEVERY (\(l1, wp1). bir_is_bool_exp wp1) wps)
End

Definition bir_sound_wps_map_def:
  bir_sound_wps_map p ls post wps =
    (FEVERY (\(l1, wp1).
              (bir_exec_to_labels_or_assumviol_triple p l1 ls wp1 post)
            ) wps
    )
End

Theorem bir_wp_exec_of_block_bool_exec_thm:
  !p l (ls:bir_label_t->bool) post wps wps'.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_bool_wps_map wps ==>
      ((bir_wp_exec_of_block p l ls wps post) = SOME wps') ==>
      (bir_bool_wps_map wps')
Proof
REWRITE_TAC [bir_bool_wps_map_def] >>
METIS_TAC [bir_wp_exec_of_block_bool_thm]
QED

Theorem bir_wp_exec_of_block_sound_exec_thm:
  !p l ls post wps wps'.
    bir_wp_post_map_contains_bool_exp post ==>
    bir_is_well_typed_program p ==>
    bir_is_valid_program p ==>
    MEM l (bir_labels_of_program p) ==>
    bir_edges_blocks_in_prog_exec p l ==>
    bir_bool_wps_map wps ==>
    bir_sound_wps_map p ls post wps ==>
    ((bir_wp_exec_of_block p l ls wps post) = SOME wps') ==>
    (bir_sound_wps_map p ls post wps')
Proof
REWRITE_TAC [bir_bool_wps_map_def, bir_sound_wps_map_def] >>
  METIS_TAC [bir_is_valid_program_def,
             bir_edges_blocks_in_prog_exec_eq_thm,
             bir_wp_exec_of_block_sound_thm]
QED

Theorem bir_wp_exec_of_block_reusable_thm:
  !p l ls post wps wps'.
      bir_wp_post_map_contains_bool_exp post ==>
      bir_is_well_typed_program p ==>
      bir_is_valid_program p ==>
      MEM l (bir_labels_of_program p) ==>
      bir_edges_blocks_in_prog_exec p l ==>
      ((bir_bool_wps_map wps) /\
       (bir_sound_wps_map p ls post wps)
      ) ==>
      ((bir_wp_exec_of_block p l ls wps post) = SOME wps') ==>
      ((bir_bool_wps_map wps') /\
       (bir_sound_wps_map p ls post wps')
      )
Proof
METIS_TAC [bir_wp_exec_of_block_sound_exec_thm,
           bir_wp_exec_of_block_bool_exec_thm]
QED

(* ============================================================================================= *)

(* TODO: move to bir_exp_equivTheory *)
Theorem bir_eq_var_const_equiv:
  !env bv k.
  (bir_eval_exp
           (BExp_BinPred BIExp_Equal
              (BExp_Den bv)
              (BExp_Const k))
           env
    = SOME bir_val_true) ==>
  (bir_eval_exp (BExp_Den bv) env = SOME (BVal_Imm k))
Proof
REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_env_read_def, bir_env_check_type_def,
      bir_env_lookup_type_def, bir_env_lookup_def, bir_val_true_def] >>
  Cases_on `f (bir_var_name bv)` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `bir_var_type bv = type_of_bir_val x` >- (
    Cases_on `x` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> Cases_on `k` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_val_def]
    )
  ) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem bir_exec_block_jmp_bv_triple_wp_thm:
  !p bl post k bv.
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Exp (BExp_Den bv)))) ==>
      (bl.bb_statements = []) ==>
      (MEM (BL_Address k) (bir_labels_of_program p)) ==>
      (bir_exec_block_jmp_triple p bl
        (BExp_BinExp BIExp_And ((BExp_BinPred BIExp_Equal (BExp_Den bv) (BExp_Const k))) post)
        post (BL_Address k))
Proof
(* Expand definitions *)
SIMP_TAC std_ss [bir_exec_block_jmp_triple_def] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
(* "wp" is the weakest precondition of the block of basic
 * statements. *)
ASSUME_TAC (Q.SPECL [`bl.bb_statements`, `post`]
                    bir_wp_exec_stmtsB_sound_thm
           ) >>
REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def,
                          bir_exec_stmtsB_triple_def, bir_wp_exec_stmtsB_def] >>
(* Start resolving the effects of execution: *)
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
(* "ns" is the new state resulting from execution of the block of
 * basic BIR statements with initial state s. *)
FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def, listTheory.EVERY_DEF] >>


FULL_SIMP_TAC std_ss [LET_DEF] >>
PAT_X_ASSUM ``!x. p``
            (fn thm =>
              ASSUME_TAC (Q.SPECL [`s`] thm
                         )
            ) >>
REV_FULL_SIMP_TAC std_ss
  [bir_vars_are_initialized_block_then_every_stmts_thm] >>
FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def, listTheory.REVERSE_DEF, bir_state_is_terminated_def] >>

(*  *)
  FULL_SIMP_TAC std_ss [GSYM bir_exp_equivTheory.bir_and_equiv] >>

  subgoal `bir_eval_exp (BExp_Den bv) s.bst_environ = SOME (BVal_Imm k)` >- (
    METIS_TAC [bir_eq_var_const_equiv]
  ) >>

(*  *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_def,
                        bir_eval_label_exp_def,
                        bir_exec_stmt_jmp_to_label_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  RW_TAC (srw_ss()) [bir_eval_exp_def, bir_is_valid_status_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_bool_exp_env_def,
       bir_typing_expTheory.bir_eval_exp_IS_SOME_IMPLIES_INIT, bir_is_bool_exp_def]
QED

Theorem bir_ret_block_triple_wp_thm:
  !p bl l k ks bv post.
      (MEM l (bir_labels_of_program p)) ==>
      (SND(THE(bir_get_program_block_info_by_label p l)) = bl) ==>
      (bl.bb_last_statement = (BStmt_Jmp (BLE_Exp (BExp_Den bv)))) ==>
      (bl.bb_statements = []) ==>

      (MEM (BL_Address k) (bir_labels_of_program p)) ==>
      ((BL_Address k) NOTIN ks) ==>

      (bir_exec_to_labels_or_assumviol_triple
           p
           l
           ((BL_Address k) INSERT ks)
           (BExp_BinExp BIExp_And ((BExp_BinPred BIExp_Equal (BExp_Den bv) (BExp_Const k))) post)
           (\l. if l = (BL_Address k) then post else bir_exp_false)
      )
Proof
REWRITE_TAC [bir_exec_to_labels_or_assumviol_triple_def] >>
  REPEAT STRIP_TAC >>

subgoal `(bir_get_current_block p s.bst_pc = SOME bl)` >- (
  FULL_SIMP_TAC std_ss [bir_get_current_block_def,
                        bir_get_program_block_info_by_label_MEM] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
(* Evaluate execution of bir_exec_to_labels using the lemma
 * bir_exec_to_labels_block. *)
IMP_RES_TAC bir_exec_to_labels_block >>
PAT_X_ASSUM ``!ls. p``
            (fn thm => FULL_SIMP_TAC std_ss [Q.SPEC `((BL_Address k) INSERT ks)` thm]) >>
(*
ASSUME_TAC (Q.SPECL [`p`, `bl`, `post`, `k`, `bv`]
                    bir_exec_block_jmp_bv_triple_wp_thm
           ) >>
*)

(* *)
FULL_SIMP_TAC std_ss [GSYM bir_exp_equivTheory.bir_and_equiv] >>
IMP_RES_TAC bir_eq_var_const_equiv >>
REV_FULL_SIMP_TAC (std_ss) [] >>
FULL_SIMP_TAC (std_ss) [bir_exec_block_def, bir_exec_stmtsB_def, LET_DEF] >>
REV_FULL_SIMP_TAC (std_ss) [bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_eval_label_exp_def, bir_exec_stmtsB_def] >>
REV_FULL_SIMP_TAC (std_ss) [bir_exec_block_def, bir_exec_stmtsB_def, LET_DEF, bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_eval_label_exp_def] >>
FULL_SIMP_TAC (std_ss) [bir_state_is_terminated_def] >>
REV_FULL_SIMP_TAC (std_ss) [] >>

(* *)
FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_state_COUNT_PC_def, bir_exec_stmt_jmp_to_label_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_block_pc_def] >>

REV_FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setSimps.PRED_SET_ss) [bir_block_pc_def, listTheory.REVERSE_DEF] >>
(* *)
PAT_X_ASSUM ``BER_Ended A B C D = r`` (fn thm => ASSUME_TAC (GSYM thm)) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_bool_expTheory.bir_is_bool_exp_env_REWRS]
QED


val _ = export_theory();
