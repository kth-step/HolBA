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

val _ = new_theory "bir_wp";

val bir_exec_stmtB_triple_def = Define `
bir_exec_stmtB_triple stmt pre post =
!st st' fe.
  (bir_is_bool_exp pre) /\
  (bir_is_bool_exp post) /\
  (
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_stmtB stmt) ) ==>
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp pre) ) ==>
  (st.bst_status = BST_Running) ==>
  (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==>
  (bir_exec_stmtB stmt st = (fe, st')) ==>
  (bir_env_vars_are_initialised st'.bst_environ (bir_vars_of_exp post) ) /\
  ((st'.bst_status = BST_AssumptionViolated) \/ (
   (st'.bst_status = BST_Running) /\
   (bir_eval_exp post (st'.bst_environ) = bir_val_true)
  )))
`;



val bir_mk_bool_val_true_thm = prove(``!v1.
(bir_mk_bool_val v1 = bir_val_true) = v1``, 
RW_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF, 
	       bir_val_false_def, bir_val_true_def, word1_distinct]
);

(* Theorems to check bir_is_bool_exp_env *)
val bir_is_bool_exp_env_GSYM = prove(``
!env e. bir_is_bool_exp e ==>
 ((bir_env_vars_are_initialised env (bir_vars_of_exp e)) =
 bir_is_bool_exp_env env e)
``, RW_TAC std_ss [bir_is_bool_exp_env_def]
);

val bir_env_vars_are_initialised_INTRO = prove(``
! e ope e1 e2 .bir_env_vars_are_initialised e
        (bir_vars_of_exp (BExp_BinExp ope e1 e2)) ==>
  ((bir_env_vars_are_initialised e (bir_vars_of_exp e1)) /\
   (bir_env_vars_are_initialised e (bir_vars_of_exp e2)))
``,
  REPEAT STRIP_TAC >>
  RW_TAC std_ss [bir_is_bool_exp_env_REWRS,
		bir_is_bool_exp_env_def] >>
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def,
		       bir_env_vars_are_initialised_UNION]
);

(* better use a reweite: eval_exp a /\ b => eval_exp a /\ eval_ecp b *)
(* {P}S{Q} *)
(* (e /\ Q) Assert e {Q} *)
val bir_triple_exec_strmtB_assert_thm = prove(``
  (bir_is_well_typed_stmtB (BStmt_Assert ex)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Assert ex) (BExp_BinExp BIExp_And ex post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def] >>
REPEAT DISCH_TAC >>
REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def,
		      		     BType_Bool_def,
		     GSYM bir_is_bool_exp_def
		     ] >>
(subgoal `bir_is_bool_exp (BExp_BinExp BIExp_And ex post)`) >|
[RW_TAC std_ss [bir_is_bool_exp_REWRS], ALL_TAC] >>
FULL_SIMP_TAC std_ss [] >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
		     bir_exec_stmt_assert_def,
		     bir_vars_of_stmtB_def
		     ] >>
(subgoal `bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp post)`) >|
[METIS_TAC [bir_env_vars_are_initialised_INTRO], ALL_TAC] >>
REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
REV_FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
(subgoal `(bir_eval_bool_exp (BExp_BinExp BIExp_And ex post) st.bst_environ) = 
    (bir_eval_bool_exp ex st.bst_environ) ∧ (bir_eval_bool_exp post st.bst_environ)`) >|
[
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS],
  ALL_TAC
] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_true_thm] >>
REV_FULL_SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF,
			 bir_dest_bool_val_TF] >>
RW_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_ALT_DEF_TF, bir_dest_bool_val_TF]
);



(* {e ==> Q} Assume e {Q} *)
val bir_triple_exec_strmtB_assume_thm = prove(``
  (bir_is_well_typed_stmtB (BStmt_Assume ex)) ==>
  (bir_is_bool_exp post) ==>
  bir_exec_stmtB_triple (BStmt_Assume ex) 
   (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def] >>
REPEAT DISCH_TAC >>
REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def,
		      		     BType_Bool_def,
		     GSYM bir_is_bool_exp_def
		     ] >>
(subgoal `
   (bir_is_bool_exp (BExp_UnaryExp BIExp_Not ex)) /\
   (bir_is_bool_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post))
`) >|
[RW_TAC std_ss [bir_is_bool_exp_REWRS], ALL_TAC] >>
FULL_SIMP_TAC std_ss [] >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
		     bir_exec_stmt_assume_def,
		     bir_vars_of_stmtB_def
		     ] >>
(subgoal `
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp post)) /\
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp (BExp_UnaryExp BIExp_Not ex)))
`) >|
[METIS_TAC [bir_env_vars_are_initialised_INTRO], ALL_TAC] >>
REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
REV_FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
(subgoal `bir_eval_bool_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post) st.bst_environ = 
    (~(bir_eval_bool_exp ex st.bst_environ)) \/ (bir_eval_bool_exp post st.bst_environ)`) >|
[
  FULL_SIMP_TAC std_ss [bir_eval_bool_exp_BExp_BinExp_REWRS,
		       bir_eval_bool_exp_BExp_UnaryExp_REWRS],
  ALL_TAC
] >>
FULL_SIMP_TAC std_ss [] >>
(RULE_ASSUM_TAC (SIMP_RULE std_ss [bir_mk_bool_val_true_thm])) >>
Cases_on `¬bir_eval_bool_exp ex st.bst_environ` >|
[
  FULL_SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF,
			bir_dest_bool_val_TF] >>
  RW_TAC std_ss [],
  FULL_SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF,
			bir_dest_bool_val_TF] >>
  RW_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_ALT_DEF_TF, bir_dest_bool_val_TF]
]
);

(* Add type condition *)
(* eval({e1/var}ex, en) = eval(ex, {eval(e1, en)/var} en)*)
val bir_eval_exp_subst1_env = prove(
``
!ex en var ty e1.
bir_eval_exp ex (BEnv (en |+ (var,ty,SOME (bir_eval_exp e1 (BEnv en))))) =
bir_eval_exp (bir_exp_subst1 (BVar var ty) e1 ex) (BEnv en)
``,
REPEAT GEN_TAC >>
Induct_on `ex` >|
[
    (* Const *)
 GEN_TAC >>
 FULL_SIMP_TAC std_ss [bir_exp_subst1_REWRS, bir_eval_exp_def],
    (* Den *)
 GEN_TAC >>
 FULL_SIMP_TAC std_ss [bir_exp_subst1_REWRS, bir_eval_exp_def] >>
 Cases_on `b = BVar var ty` >|
 [
  RW_TAC std_ss [bir_env_read_def, bir_var_name_def, bir_env_lookup_def] >>
  EVAL_TAC,
  ALL_TAC
 ] >>
 Cases_on `b` >>
 Cases_on `var <> s` >|
 [
  FULL_SIMP_TAC std_ss [bir_eval_exp_def] >>
  EVAL_TAC >>
  FULL_SIMP_TAC std_ss [],
  ALL_TAC
 ] >>
 EVAL_TAC >>
 FULL_SIMP_TAC std_ss [] >>
 RW_TAC std_ss [] >>
 FULL_SIMP_TAC std_ss [bir_eval_exp_def] >>
 EVAL_TAC >>
 cheat,

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],


 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss [],

 REPEAT GEN_TAC >>
 SIMP_TAC std_ss [Once bir_eval_exp_def, Once bir_exp_subst1_REWRS] >>
 SIMP_TAC std_ss [Once bir_eval_exp_def] >>
 FULL_SIMP_TAC std_ss []
]);

(* {{e/v}Q}Assign v:=e {Q} *)
val bir_triple_exec_strmtB_assign_thm = prove(``
  (bir_is_well_typed_stmtB (BStmt_Assign v ex)) ==>
  (bir_is_bool_exp post) ==>
  bir_exec_stmtB_triple (BStmt_Assign v ex) 
   (bir_exp_subst1 v ex post) post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def] >>
REPEAT DISCH_TAC >>
REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtB_def] >>
subgoal `bir_is_bool_exp (bir_exp_subst1 v ex post)` >|
[
 FULL_SIMP_TAC std_ss [bir_is_bool_exp_def,
		      bir_exp_subst1_def] >>
 (let val thm = (SPEC ``(FEMPTY |+ (v:bir_var_t,ex:bir_exp_t)) ``
		   bir_exp_subst_TYPE_EQ) 
      val h = (fst o dest_imp o concl) thm in
      ASSUME_TAC thm >>
      subgoal `^h`
  end) >|
 [
  FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_DEF] >>
  RW_TAC std_ss [] >>
  cheat,
  FULL_SIMP_TAC std_ss []
 ],
 ALL_TAC
] >>

FULL_SIMP_TAC std_ss [] >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
		     bir_exec_stmt_assign_def,
		     bir_env_write_def,
		     bir_vars_of_stmtB_def] >>
FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_INSERT] >>
subgoal `bir_env_var_is_declared st.bst_environ v` >|
[
 FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_weaken],
 ALL_TAC
] >>
FULL_SIMP_TAC std_ss [GEN_ALL bir_env_var_is_declared_ALT_DEF] >>
Cases_on `v` >>
Cases_on `st.bst_environ` >>
FULL_SIMP_TAC std_ss [bir_var_name_def,
		     bir_env_update_def,
		     bir_var_type_def] >>
subgoal `type_of_bir_val (bir_eval_exp ex (BEnv f)) = SOME(b)` >|
[
 FULL_SIMP_TAC std_ss [type_of_bir_exp_THM_with_init_vars],
 ALL_TAC
] >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
RW_TAC std_ss [bir_eval_exp_subst1_env] >>
cheat
);

(* {Q} Observe ex {Q} *)
val bir_triple_exec_strmtB_observe_thm = prove(``
  (bir_is_well_typed_stmtB (BStmt_Observe ec el obf)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Observe ec el obf)
   post post
``,
REWRITE_TAC [bir_exec_stmtB_triple_def] >>
REPEAT DISCH_TAC >>
REPEAT GEN_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_def,
		     bir_exec_stmt_observe_def] >>
(`bir_dest_bool_val (bir_eval_exp ec st.bst_environ) <> NONE` by cheat) >>
Cases_on `bir_dest_bool_val (bir_eval_exp ec st.bst_environ)` >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >|
[
 FULL_SIMP_TAC std_ss [] >>
 RW_TAC std_ss [],
 FULL_SIMP_TAC std_ss [] >>
 RW_TAC std_ss []
]
);

val bir_triple_exec_strmtB_declare_thm = prove(``
  (bir_is_well_typed_stmtB (BStmt_Declare b)) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple (BStmt_Declare b)
   post post
``,
cheat
);

val bir_wp_exec_stmtB_def = Define `
(bir_wp_exec_stmtB (BStmt_Assert ex) post = (BExp_BinExp BIExp_And ex post)) /\
(bir_wp_exec_stmtB (BStmt_Assume ex) post = 
   (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ex) post)) /\
(bir_wp_exec_stmtB (BStmt_Assign v ex) post = (bir_exp_subst1 v ex post)) /\
(bir_wp_exec_stmtB (BStmt_Observe ec el obf) post = post) /\
(bir_wp_exec_stmtB (BStmt_Declare b) post = post)
`;

val bir_wp_exec_stmtB_sound_thm = prove(
``!stm post.
  (bir_is_well_typed_stmtB stm) ==>
  (bir_is_bool_exp post) ==>
bir_exec_stmtB_triple stm (bir_wp_exec_stmtB stm post) post
``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  Cases_on `stm` >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtB_def,
			bir_triple_exec_strmtB_assign_thm,
			bir_triple_exec_strmtB_assert_thm,
			bir_triple_exec_strmtB_assume_thm,
			bir_triple_exec_strmtB_observe_thm,
			bir_triple_exec_strmtB_declare_thm
		       ]
);


val bir_exec_stmtsB_triple_def = Define `
bir_exec_stmtsB_triple stmts pre post =
!st st' fe fe' c c'.
  (bir_is_bool_exp pre) /\
  (bir_is_bool_exp post) /\
(
  (EVERY (\stmt. bir_env_vars_are_initialised st.bst_environ (bir_vars_of_stmtB stmt)) stmts) ==>
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp pre) ) ==>
  (st.bst_status = BST_Running) ==>
  (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==>
  (bir_exec_stmtsB stmts (fe, c, st) = (fe', c', st')) ==>
  ((st'.bst_status = BST_AssumptionViolated) \/ (
   (st'.bst_status = BST_Running) /\
   (bir_eval_exp post (st'.bst_environ) = bir_val_true)
  )))
`;

val bir_wp_exec_stmtsB_def = Define `
(bir_wp_exec_stmtsB [] post = post) /\
(bir_wp_exec_stmtsB (stmt::stmts) post = 
 bir_wp_exec_stmtB stmt (bir_wp_exec_stmtsB stmts post)
)`;

val exec_preserves_initialized_vars_thm = prove(``
(r = bir_exec_stmtB_state (h:'a bir_stmt_basic_t) st) ==>
(EVERY (λstmt:'a bir_stmt_basic_t.
            bir_env_vars_are_initialised st.bst_environ
              (bir_vars_of_stmtB stmt)) stmts) ==>
(EVERY (λstmt.
            bir_env_vars_are_initialised r.bst_environ
              (bir_vars_of_stmtB stmt)) stmts)
``,
REPEAT DISCH_TAC >>
subgoal `!x. 
 (λstmt:'a bir_stmt_basic_t. bir_env_vars_are_initialised st.bst_environ
	 (bir_vars_of_stmtB stmt)) x ==>
 (λstmt. bir_env_vars_are_initialised r.bst_environ
	 (bir_vars_of_stmtB stmt)) x` >|
[
 GEN_TAC >>
 FULL_SIMP_TAC std_ss [] >>
 DISCH_TAC >>     
 MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_env_vars_are_initialised_ORDER) >>
 Q.EXISTS_TAC `st.bst_environ` >>
 ASM_SIMP_TAC std_ss [bir_exec_stmtB_ENV_ORDER],
 ALL_TAC
] >>
ASSUME_TAC (ISPECL [``
  (λstmt : 'a bir_stmt_basic_t . bir_env_vars_are_initialised st.bst_environ
          (bir_vars_of_stmtB stmt))``,
``(λstmt: 'a bir_stmt_basic_t.bir_env_vars_are_initialised r.bst_environ
     (bir_vars_of_stmtB stmt))``]
		   listTheory.EVERY_MONOTONIC) >>
REV_FULL_SIMP_TAC std_ss []
);


val bir_exec_stmtsB_assumption_violated_thm = prove(``
!(q:'a option) fe c r fe' c' st'.
(bir_exec_stmtsB stmts (OPT_CONS q fe,SUC c,r) = (fe',c',st')) ==>
(r.bst_status <> BST_Running) ==>
(st' = r)
``,
  Induct_on `stmts` >|
 [
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def],
  REPEAT GEN_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_def, bir_state_is_terminated_def] >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss []
 ]);
  

val bir_wp_exec_stmtsB_sound_thm = prove(``
  !stmts post.
  (EVERY bir_is_well_typed_stmtB stmts) ==>
  (bir_is_bool_exp post) ==>
  (bir_exec_stmtsB_triple stmts (bir_wp_exec_stmtsB stmts post) post)
``,
  REPEAT GEN_TAC >>
  Induct_on `stmts` >|
  [
    FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def,
			 bir_exec_stmtsB_triple_def,
			 bir_exec_stmtsB_def] >>
    RW_TAC std_ss [],
    ALL_TAC
  ] >>
  GEN_TAC >>
  REPEAT DISCH_TAC >>
  SIMP_TAC std_ss [bir_exec_stmtsB_triple_def,
		   Once bir_wp_exec_stmtsB_def,
		  Once bir_exec_stmtsB_def] >>
  REPEAT GEN_TAC >>
  SIMP_TAC std_ss [bir_state_is_terminated_def] >>
  Q.ABBREV_TAC `st1 = bir_exec_stmtB h st` >>
  Cases_on `st1` >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>

  (* Inductive hyp *)
  FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def,
		       listTheory.EVERY_DEF] >>
  PAT_X_ASSUM ``!st.p`` (fn thm => 
    ASSUME_TAC (SPECL [``r:bir_state_t``, ``st':bir_state_t``,
		      ``OPT_CONS q fe``, ``fe': 'a list``,
		      ``SUC c``, ``c':num``] thm)) >>
  FULL_SIMP_TAC std_ss [] >>

 (* wp' must be a boolean expression *)
  Q.ABBREV_TAC `wp = (bir_wp_exec_stmtsB stmts post)` >>
  FULL_SIMP_TAC std_ss [bir_wp_exec_stmtsB_def] >>
  ASSUME_TAC (SPECL [``h:'a bir_stmt_basic_t``, ``wp:bir_exp_t``]
		   bir_wp_exec_stmtB_sound_thm) >>
  REV_FULL_SIMP_TAC std_ss [bir_exec_stmtB_triple_def] >>
  PAT_X_ASSUM ``!st.p`` (fn thm => 
    ASSUME_TAC (SPECL [``st:bir_state_t``, ``r:bir_state_t``, ``q: 'a option``]
		      thm)) >>
  FULL_SIMP_TAC std_ss [] >>

  (* Enable the hypothesis of wp of h *)
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  subgoal `(bir_exec_stmtB h st = (q,r))` >|
  [UNABBREV_ALL_TAC >> METIS_TAC [], ALL_TAC] >>
  FULL_SIMP_TAC std_ss [] >|
  [
   (* Case assumption violated *)
   ASSUME_TAC (SPECL [
	       ``q:'a option``, ``fe: 'a list``, ``c:num``, ``r:bir_state_t``,
	       ``fe':'a list``, ``c':num``, ``st':bir_state_t``
     ] 
     bir_exec_stmtsB_assumption_violated_thm) >>
   REV_FULL_SIMP_TAC std_ss [] >>
   RW_TAC std_ss [],
   ALL_TAC
  ] >>

  (* case running *)
  (* prove assumptions of inductive case *)
 subgoal `r = bir_exec_stmtB_state h st` >|
 [FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def],ALL_TAC] >>

 ASSUME_TAC exec_preserves_initialized_vars_thm >>
 REV_FULL_SIMP_TAC std_ss [] >>
 FULL_SIMP_TAC std_ss [] 
);

    
val bir_exec_block_jmp_triple_def = Define(`
bir_exec_block_jmp_triple p bl pre post l =
!st l1 c1 st'.
  (bir_is_bool_exp pre) /\
  (bir_is_bool_exp post) /\
(
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_block bl)) ==>
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp pre)) ==>
  (st.bst_status = BST_Running) ==>
  (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==>
  (bir_exec_block p bl st = (l1,c1,st')) ==>
  ((st'.bst_status = BST_AssumptionViolated) \/ (
   (st'.bst_status = BST_Running) /\
   (bir_eval_exp post (st'.bst_environ) = bir_val_true) /\
   (st'.bst_pc = bir_block_pc l)
  )))
`);

val bir_exec_block_jmp_triple_wp_thm = prove(``
  !p bl post l.
  (bir_is_well_typed_block bl) ==>
  (bir_is_bool_exp post) ==>
  (bl.bb_last_statement = (BStmt_Jmp (BLE_Label l))) ==>
  (MEM l (bir_labels_of_program p)) ==>
  (bir_exec_block_jmp_triple p bl 
    (bir_wp_exec_stmtsB bl.bb_statements post) post l)
``,
 REPEAT GEN_TAC >>
 REPEAT DISCH_TAC >>
 SIMP_TAC std_ss [bir_exec_block_jmp_triple_def] >>
 REPEAT GEN_TAC >>
 FULL_SIMP_TAC std_ss [] >>
 ASSUME_TAC (SPECL [``bl.bb_statements``,
		   ``post:bir_exp_t``] bir_wp_exec_stmtsB_sound_thm) >>
 (REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def]) >>
 Q.ABBREV_TAC `wp = bir_wp_exec_stmtsB bl.bb_statements post` >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>
 REPEAT DISCH_TAC >>
 FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
 Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,st)` >>
 pairLib.PairCases_on `ns` >>
 FULL_SIMP_TAC std_ss [LET_DEF] >>
 PAT_X_ASSUM ``!x.p`` (fn thm =>
   ASSUME_TAC (Q.SPECL [`st`, `ns2`, `[]:'a list`, `ns0`, `0:num`, `ns1`]
   thm)) >>
 REV_FULL_SIMP_TAC std_ss [] >>
 subgoal `EVERY
         (λstmt.
            bir_env_vars_are_initialised st.bst_environ
              (bir_vars_of_stmtB stmt)) bl.bb_statements` >-
 (cheat) >>
 Cases_on `(ns2.bst_status = BST_AssumptionViolated)` >-
 (
    FULL_SIMP_TAC std_ss [ bir_state_is_terminated_def] >>
    RW_TAC std_ss [] >>
    subgoal `(ns2 with
  bst_pc := st.bst_pc with bpc_index := st.bst_pc.bpc_index + PRE c1).bst_status = ns2.bst_status` >-
    (RW_TAC (srw_ss()) []) >>
    (FULL_SIMP_TAC std_ss [])
 ) >>
 FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
 Q.ABBREV_TAC `st2 = (bir_exec_stmtE p (BStmt_Jmp (BLE_Label l)) ns2)` >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_jmp_def, bir_eval_label_exp_def, bir_exec_stmt_jmp_to_label_def] >>
 REV_FULL_SIMP_TAC std_ss [Abbr `st2`] >>
 subgoal `(ns2 with bst_pc := bir_block_pc l).bst_status = ns2.bst_status` >-
 (RW_TAC (srw_ss()) []) >>
 FULL_SIMP_TAC std_ss [] >>
 subgoal `(st'.bst_status = ns2.bst_status) /\
          (st'.bst_environ = ns2.bst_environ)` >-
 (RW_TAC (srw_ss()) []) >>
 (FULL_SIMP_TAC std_ss []) >>
 (RW_TAC (srw_ss()) [])

);


val bir_is_bool_exp_eval_true_or_false_thm = prove(``
! e env.
(bir_is_bool_exp_env env e) ==>
(((bir_dest_bool_val (bir_eval_exp e env)) = (SOME T)) \/
 ((bir_dest_bool_val (bir_eval_exp e env)) = (SOME F))
)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_def, bool2b_def,
bir_dest_bool_val_def]
);

val bir_exec_block_cjmp_triple_def = Define(`
bir_exec_block_cjmp_triple p bl pre post1 l1 post2 l2 =
!st l' c1 st'.
  (bir_is_bool_exp pre) /\
  (bir_is_bool_exp post1) /\
  (bir_is_bool_exp post2) /\
(
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_block bl)) ==>
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp pre)) ==>
  (st.bst_status = BST_Running) ==>
  (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==>
  (bir_exec_block p bl st = (l',c1,st')) ==>
  ((st'.bst_status = BST_AssumptionViolated) \/ (
   (st'.bst_status = BST_Running) /\ ((
     (bir_eval_exp post1 (st'.bst_environ) = bir_val_true) /\
     (st'.bst_pc = bir_block_pc l1))
     \/ (
     (bir_eval_exp post2 (st'.bst_environ) = bir_val_true) /\
     (st'.bst_pc = bir_block_pc l2)))
  )))
`);


val bir_exec_block_cjmp_triple_wp_thm = prove(``
  !p bl post1 l1 post2 l2.
  (bir_is_well_typed_block bl) ==>
  (bir_is_bool_exp post1) ==>
  (bir_is_bool_exp post2) ==>
  (bl.bb_last_statement = (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2))) ==>
  (MEM l1 (bir_labels_of_program p)) ==>
  (MEM l2 (bir_labels_of_program p)) ==>

  (bir_exec_block_cjmp_triple p bl 
    (bir_wp_exec_stmtsB bl.bb_statements  (
    (BExp_BinExp BIExp_And 
		  (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e) post1)
		  (BExp_BinExp BIExp_Or e post2)
		 )
    ))
    post1 l1 post2 l2)
``,
 REPEAT GEN_TAC >>
 REPEAT DISCH_TAC >>
 SIMP_TAC std_ss [bir_exec_block_cjmp_triple_def] >>
 REPEAT GEN_TAC >>
 FULL_SIMP_TAC std_ss [] >>

 Q.ABBREV_TAC `q1 = (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e) post1)` >> 
 Q.ABBREV_TAC `q2 = (BExp_BinExp BIExp_Or e post2)` >>
 Q.ABBREV_TAC `post_stmts = (BExp_BinExp BIExp_And q1 q2)` >> 

 ASSUME_TAC (SPECL [``bl.bb_statements``,
		   ``post_stmts:bir_exp_t``] bir_wp_exec_stmtsB_sound_thm) >>
 (REV_FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def]) >>

 subgoal `bir_is_bool_exp post_stmts` >-
 (
  FULL_SIMP_TAC std_ss [Abbr `q1`, Abbr `q2`, Abbr `post_stmts`, bir_is_bool_exp_REWRS,
		 bir_is_well_typed_stmtE_def,
		 BType_Bool_def,
		 GSYM bir_is_bool_exp_def
		]
 ) >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>

 FULL_SIMP_TAC std_ss [bir_exec_block_def] >>
 Q.ABBREV_TAC `ns = bir_exec_stmtsB bl.bb_statements ([],0,st)` >>
 pairLib.PairCases_on `ns` >>
 FULL_SIMP_TAC std_ss [LET_DEF] >>

 PAT_X_ASSUM ``!x.p`` (fn thm =>
   ASSUME_TAC (Q.SPECL [`st`, `ns2`, `[]:'a list`, `ns0`, `0:num`, `ns1`]
   thm)) >>
 FULL_SIMP_TAC std_ss [] >>
 REPEAT DISCH_TAC >>

 subgoal `EVERY
         (λstmt.
            bir_env_vars_are_initialised st.bst_environ
              (bir_vars_of_stmtB stmt)) bl.bb_statements` >-
 (cheat) >>
 (FULL_SIMP_TAC std_ss []) >>

 Cases_on `(ns2.bst_status = BST_AssumptionViolated)` >-
 (
    FULL_SIMP_TAC std_ss [ bir_state_is_terminated_def] >>
    RW_TAC std_ss [] >>
    subgoal `(ns2 with
  bst_pc := st.bst_pc with bpc_index := st.bst_pc.bpc_index + PRE c1).bst_status = ns2.bst_status` >-
    (RW_TAC (srw_ss()) []) >>
    (FULL_SIMP_TAC std_ss [])
 ) >>
 FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
 REV_FULL_SIMP_TAC std_ss [] >>
 Q.ABBREV_TAC `st2 = (bir_exec_stmtE p (BStmt_CJmp e (BLE_Label l1) (BLE_Label l2)) ns2)` >>
 FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, bir_exec_stmt_cjmp_def] >>
 (* to proove that is_bool e *)
 FULL_SIMP_TAC std_ss [bir_is_well_typed_stmtE_def,
		      BType_Bool_def,
		     GSYM bir_is_bool_exp_def] >>
 subgoal `bir_env_vars_are_initialised st.bst_environ
         (bir_vars_of_exp e)` >-
 (cheat) >>
 REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_GSYM] >>
 Cases_on `(bir_dest_bool_val (bir_eval_exp e ns2.bst_environ) = SOME T)` >-
 (
   FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_def,
			bir_eval_label_exp_def,
			bir_exec_stmt_jmp_to_label_def] >>
   REV_FULL_SIMP_TAC std_ss [Abbr `st2`] >>
   subgoal `(ns2 with bst_pc := bir_block_pc l1).bst_status = ns2.bst_status` >-
   (RW_TAC (srw_ss()) []) >>
   FULL_SIMP_TAC std_ss [] >>
   REV_FULL_SIMP_TAC std_ss [] >>
   subgoal `(st'.bst_environ = ns2.bst_environ)` >-
   (RW_TAC (srw_ss()) []) >>
   (FULL_SIMP_TAC std_ss []) >>
   FULL_SIMP_TAC std_ss [Abbr `post_stmts`, Abbr `q1`, Abbr `q2`] >> 
   (* general proof that var_initialized_block /\ var_initialized_wp => var_initialided post *)
   subgoal `bir_is_bool_exp_env ns2.bst_environ
            (BExp_BinExp BIExp_And
               (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e) post1)
               (BExp_BinExp BIExp_Or e post2))` >-
   (cheat) >>
   FULL_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
   FULL_SIMP_TAC std_ss [Once (GEN ``env:bir_var_environment_t`` bir_is_bool_exp_env_REWRS)] >>
   FULL_SIMP_TAC std_ss [Once bir_eval_bool_exp_BExp_BinExp_REWRS] >>
   FULL_SIMP_TAC std_ss [Once (GEN ``env:bir_var_environment_t`` bir_is_bool_exp_env_REWRS)] >>
   FULL_SIMP_TAC std_ss [Once bir_eval_bool_exp_BExp_BinExp_REWRS] >>
   FULL_SIMP_TAC std_ss [Once (GEN ``env:bir_var_environment_t`` bir_is_bool_exp_env_REWRS)] >>
   FULL_SIMP_TAC std_ss [Once bir_eval_bool_exp_BExp_UnaryExp_REWRS] >>
   
   subgoal `bir_eval_bool_exp e ns2.bst_environ` >- (cheat) >>
   FULL_SIMP_TAC std_ss [bir_mk_bool_val_true_thm] >>

   ASM_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO] >>
   FULL_SIMP_TAC std_ss [bir_mk_bool_val_true_thm] >>
   (* Proved that post1 hold *)
   RW_TAC std_ss []
 ) >>
 (* bir_is_bool_exp_eval_true_or_false_thm *)
 cheat
);


val _ = export_theory();















(*

``
(bir_env_vars_are_initialised st.bst_environ
 (bir_vars_of_program p)) ==>
((bir_wp_exec_stmtsB bl.bb_statements post) = wp) ==>
(bir_env_vars_are_initialised st.bst_environ
         (bir_vars_of_exp wp)) ==>
(st.bst_status = BST_Running) ==>
(bir_eval_exp wp st.bst_environ = bir_val_true) ==>
(bir_is_well_typed_program p) ==>
(bir_is_bool_exp post) ==>
(bir_get_current_block p st.bst_pc = SOME bl) ==>
(bl.bb_last_statement = (BStmt_Jmp (BLE_Label l))) ==>
(l ∈ ls) ==>
(? l1 c1 n st1. (bir_exec_to_labels ls p st = (BER_Ended l1 c1 n st1)) /\
  ((st'.bst_status = BST_AssumptionViolated) \/ 
   (bir_eval_exp post (st'.bst_environ) = bir_val_true)
  )
)
``
REPEAT DISCH_TAC >>
ASSUME_TAC (SPECL [``ls:bir_label_t -> bool``, ``p:'a bir_program_t``,
		   ``st:bir_state_t``, ``bl:'a bir_block_t``]
	    bir_exec_to_labels_block
) >>
Q.ABBREV_TAC `e' = (bir_exec_to_labels ls p st =
       (let (l1,c1,st1) = bir_exec_block p bl st
        in
          if
            0 < c1 ∧
            bir_state_COUNT_PC
              (F,(λpc. (pc.bpc_index = 0) ∧ pc.bpc_label ∈ ls)) st1
          then
            BER_Ended l1 c1 1 st1
          else
            case bir_exec_to_labels ls p st1 of
              BER_Ended l2 c2 c2' st2 =>
                BER_Ended (l1 ++ l2) (c1 + c2) c2' st2
            | BER_Looping ll2 =>
                BER_Looping (LAPPEND (fromList l1) ll2)))` >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `r = bir_exec_block p bl st` >>
pairLib.PairCases_on `r` >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
FULL_SIMP_TAC std_ss [bir_exec_block_def] >>

(* This is for the list of internal statements *)
ASSUME_TAC (SPECL [``bl.bb_statements : 'a bir_stmt_basic_t list``,
		   ``post:bir_exp_t``] bir_wp_exec_stmtsB_sound_thm) >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_program_def] >>
subgoal `bir_is_well_typed_block bl` >| [cheat, ALL_TAC] >>
FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def] >>

REV_FULL_SIMP_TAC std_ss [bir_exec_stmtsB_triple_def] >>
PAT_X_ASSUM ``!st:bir_state_t.p`` (fn thm =>
  ASSUME_TAC (SPECL [``st:bir_state_t``, ``st':bir_state_t``,
		     ``[]: 'a list``, ``fe':'a list``,
		     ``0:num``, ``c':num``] thm)) >>
FULL_SIMP_TAC std_ss [] >>



bir_program_blocksTheory.bir_exec_to_labels_block;


  (bir_is_bool_exp pre) /\
   /\
(
  (EVERY (\stmt. bir_env_vars_are_initialised st.bst_environ (bir_vars_of_stmtB stmt)) stmts) ==>
  (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp pre) ) ==>
  (st.bst_status = BST_Running) ==>
  (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==>
  (bir_exec_stmtsB stmts (fe, c, st) = (fe', c', st')) ==>
  ((st'.bst_status = BST_AssumptionViolated) \/ (
   (st'.bst_status = BST_Running) /\
   (bir_eval_exp post (st'.bst_environ) = bir_val_true)
  )))


*)
(* val bir_exec_to_labels_triple_def = Define ` *)
(* bir_exec_to_labels_triple ls lstart p pre post = *)
(* !bs. *)
(*   (bir_eval_exp pre (bs.bst_environ) = bir_val_true) ==> *)
(*   (bs.bst_pc = <| bpc_label := lstart; bpc_index:= 0 |>) ==> *)
(*   ?lo c_st c_addr_labels bs'. *)
(*   (bir_exec_to_labels ls p bs = BER_Ended lo c_st c_addr_labels bs') /\ *)
(*   (~(bs'.bst_status = BST_AssertionViolated)) /\ *)
(*   ((bs'.bst_status = BST_AssumptionViolated) \/ *)
(*    (bir_eval_exp post (bs'.bst_environ) = bir_val_true) *)
(*   ) *)
(* `; *)

(* val bir_exec_block_triple_def = Define ` *)
(* bir_exec_block_triple lstart p pre post = *)
(* !bs bl. *)
(*   (bir_eval_exp pre (bs.bst_environ) = bir_val_true) ==> *)
(*   (bs.bst_pc = <| bpc_label := lstart; bpc_index:= 0 |>) ==> *)
(*   (bir_get_current_block p bs.bst_pc = SOME bl) ==> *)
(*   ?l1,c1,bs'. *)
(*   (bir_exec_block p bl bs = (l1,c1,bs')) /\ *)
(*   (~(bs'.bst_status = BST_AssertionViolated)) /\ *)
(*   ((bs'.bst_status = BST_AssumptionViolated) \/ *)
(*    (bir_eval_exp post (bs'.bst_environ) = bir_val_true) *)
(*   ) *)
(* `; *)



(* val bir_exec_stmtE_triple_def = Define ` *)
(* bir_exec_stmtE_triple p stmt pre post = *)
(* !st st'. *)
(*   (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_stmtE stmt) ) ==> *)
(*   (st.bst_status = BST_Running) ==> *)
(*   (bir_eval_exp pre (st.bst_environ) = bir_val_true) ==> *)
(*   (bir_exec_stmtE p stmt st = st') ==> *)
(*   (~(st'.bst_status = BST_AssertionViolated)) /\ *)
(*   ((st'.bst_status = BST_AssumptionViolated) \/ *)
(*    (bir_eval_exp post (st'.bst_environ) = bir_val_true) *)
(*   ) *)
(* `; *)

(* prove(`` *)
(*   bir_is_well_typed_stmtE c ==> *)
(*   bir_exec_stmtE_triple p (BStmt_Halt ex) post post *)
(* ``, *)
(* REWRITE_TAC [bir_exec_stmtE_triple_def] >> *)
(* DISCH_TAC >> (REPEAT GEN_TAC) >> *)
(* REPEAT DISCH_TAC >> *)
(* FULL_SIMP_TAC std_ss [bir_exec_stmtE_def,bir_exec_stmt_halt_def] >> *)
(* (RW_TAC std_ss []) *)
(* ); *)



(* val bir_wp_exec_stmtE_def = Define ` *)
(* (bir_wp_exec_stmtE p (BStmt_Halt ex) post = post) /\ *)
(* (bir_wp_exec_stmtE p (BStmt_Jmp l) post = post) /\ *)
(* (bir_wp_exec_stmtE p (BStmt_CJmp b b0 b1) post = post) *)
(* `; *)

(* (* Must be cleaned, but htis is the basic idea *) *)
(* prove (`` *)
(* bir_is_well_typed_stmtE c ==> *)
(* bir_exec_stmtE_triple p c *)
(*   (bir_wp_exec_stmtE p c post) post *)
(* ``, *)
(* REPEAT DISCH_TAC >> *)
(* REWRITE_TAC [bir_exec_stmtE_triple_def] >> *)
(* REPEAT GEN_TAC >> *)
(* REPEAT DISCH_TAC >> *)
(* Cases_on `c`  *)
(* >| *)
(* [ *)
(*  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, *)
(* 		       bir_exec_stmt_jmp_def, *)
(* 		       bir_is_well_typed_stmtE_def, *)
(* 		       bir_vars_of_stmtE_def, *)
(* 		       bir_wp_exec_stmtE_def *)
(* 		      ] >> *)
(*  ASSUME_TAC (SPECL [``b:bir_label_exp_t``, ``st.bst_environ``] *)
(* 	    	   bir_eval_label_exp_NEQ_NONE_WF_INITIALISED *)
(* 	    ) >> *)
(*  REV_FULL_SIMP_TAC std_ss [] >> *)
(*  Cases_on `bir_eval_label_exp b st.bst_environ` >> *)
(*  (FULL_SIMP_TAC std_ss []) >> *)
(*  (FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def]) >> *)
(*  (RW_TAC std_ss []), *)

(*  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, *)
(* 		       bir_exec_stmt_cjmp_def, *)
(* 		       bir_exec_stmt_jmp_def, *)
(* 		       bir_is_well_typed_stmtE_def, *)
(* 		       bir_vars_of_stmtE_def, *)
(* 		       bir_wp_exec_stmtE_def *)
(* 		      ] >> *)
(*  ASSUME_TAC (SPECL [``b0:bir_label_exp_t``, ``st.bst_environ``] *)
(* 	    	   bir_eval_label_exp_NEQ_NONE_WF_INITIALISED *)
(* 	    ) >> *)
(*  ASSUME_TAC (SPECL [``b1:bir_label_exp_t``, ``st.bst_environ``] *)
(* 	    	   bir_eval_label_exp_NEQ_NONE_WF_INITIALISED *)
(* 	    ) >> *)
(*  REV_FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >> *)
(*  Cases_on `bir_eval_label_exp b0 st.bst_environ` >> *)
(*  (FULL_SIMP_TAC std_ss []) >> *)
(*  Cases_on `bir_eval_label_exp b1 st.bst_environ` >> *)
(*  (FULL_SIMP_TAC std_ss []) >> *)
(*  (`bir_dest_bool_val (bir_eval_exp b st.bst_environ) <> NONE` by cheat) >> *)
(*  (FULL_SIMP_TAC std_ss [bir_exec_stmt_jmp_to_label_def]) >> *)
(*  Cases_on `(bir_dest_bool_val (bir_eval_exp b st.bst_environ))` >> *)
(*  (FULL_SIMP_TAC std_ss []) >> *)
(*  (RW_TAC std_ss []), *)

(*  FULL_SIMP_TAC std_ss [bir_exec_stmtE_def, *)
(* 		       bir_exec_stmt_halt_def, *)
(* 		       bir_wp_exec_stmtE_def *)
(* 		      ] >> *)
(*  (RW_TAC std_ss []) *)
(* ] *)

(* ); *)
