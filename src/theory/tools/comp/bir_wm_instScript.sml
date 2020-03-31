open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bin_simp_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_program_env_orderTheory;
open bir_exp_equivTheory;
open bir_bool_expTheory;
open bir_typing_expTheory;
(* Most of these added for stuff that should be moved anyway... *)
open bir_valuesTheory;
open bir_expTheory;
open bir_immTheory;
open bir_envTheory;
open bir_exp_immTheory;
open bir_exp_memTheory;
open bir_exp_tautologiesTheory;

open bir_htTheory;

open bin_hoare_logicSimps;
open HolBACoreSimps;

open bir_immSyntax;

val _ = new_theory "bir_wm_inst";

(******************************************************************)
(*                         DEFINITIONS                            *)
(******************************************************************)

(* The transition of the BIR WM *)
val bir_trs_def = Define `
  bir_trs (prog:'a bir_program_t) st =
  let
    (_, _, _, st') = bir_exec_block_n prog st 1
  in
   if ~(bir_state_is_terminated st')
   then SOME st'
   else NONE
`;


(* The weak transition of the BIR WM *)
val bir_weak_trs_def = Define `
  bir_weak_trs ls prog st =
    case (bir_exec_to_labels ls prog st) of
      BER_Ended _ _ _ st' =>
        if ~(bir_state_is_terminated st')
        then SOME st'
        else NONE
    | BER_Looping _ => NONE
`;


(* The BIR WM which is later proven to obey the property
 * "weak_model". *)
val bir_etl_wm_def =
  Define `bir_etl_wm (prog :'a bir_program_t) = <|
    trs  := bir_trs prog;
    weak := (\st ls st'.
	       (bir_weak_trs ls prog st = SOME st')
	    );
    pc   := (\st. st.bst_pc.bpc_label)
  |>`;

(* bir_exec_to_labels_triple_def *)
(* weak_triple_def *)

val bir_exec_to_labels_triple_precond_def = Define `
  bir_exec_to_labels_triple_precond st pre prog =
    (bir_eval_exp pre st.bst_environ = SOME bir_val_true) /\
    (bir_env_vars_are_initialised st.bst_environ
       (bir_vars_of_program prog)) /\
    (st.bst_pc.bpc_index = 0) /\
    (st.bst_status = BST_Running) /\
    (bir_is_bool_exp_env st.bst_environ pre)
`;

(* We don't need the condition that st.bst_pc.bpc_label IN ls here,
 * since we can obtain that result from weak_pc_in_thm. *)
val bir_exec_to_labels_triple_postcond_def = Define `
  bir_exec_to_labels_triple_postcond st post prog =
    (bir_eval_exp (post st.bst_pc.bpc_label) st.bst_environ =
       SOME bir_val_true) /\
    (bir_env_vars_are_initialised st.bst_environ
       (bir_vars_of_program prog)) /\
    (st.bst_pc.bpc_index = 0) /\
    (st.bst_status = BST_Running) /\
    (bir_is_bool_exp_env st.bst_environ (post st.bst_pc.bpc_label))
`;

(* The main BIR triple to be used for composition *)
val bir_triple_def = Define `
  bir_triple prog l ls pre post =
    weak_triple (bir_etl_wm prog) l ls
      (\s. bir_exec_to_labels_triple_precond s pre prog)
      (\s'. bir_exec_to_labels_triple_postcond s' post prog)
`;


(* BIR map triple, mirroring weak_map_triple *)
(* See bir_triple_from_map_triple below for how to get a bir_map_triple from bir_triple *)
val bir_map_triple_def = Define `
  bir_map_triple prog invariant (l:bir_label_t) ls ls' pre post =
    weak_map_triple (bir_etl_wm prog)
      (\s. bir_exec_to_labels_triple_precond s invariant prog)
      l ls ls'
      (\s. bir_exec_to_labels_triple_precond s pre prog)
      (\s'. bir_exec_to_labels_triple_postcond s' post prog)
`;


(******************************************************************)
(*                            LEMMATA                             *)
(******************************************************************)

(******************************)
(* bir_trs + bir_exec_block_n *)

val bir_exec_block_n_to_FUNPOW_OPT_bir_trs =
  store_thm("bir_exec_block_n_to_FUNPOW_OPT_bir_trs",
  ``!prog st m l n c_l' st'.
      (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
      ~(bir_state_is_terminated st') ==>
      (FUNPOW_OPT (bir_trs prog) m st = SOME st')``,

Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
(* 1. Deal with case m = 0. *)
Cases_on `m = 0` >- (
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
  Cases_on `bir_trs prog st''` >- (
    FULL_SIMP_TAC std_ss [bir_trs_def] >>
    REV_FULL_SIMP_TAC std_ss [LET_DEF]
  ) >>
  REV_FULL_SIMP_TAC std_ss [bir_trs_def, LET_DEF]
) >>
Q.PAT_X_ASSUM `m <> 0`
              (fn thm => (subgoal `m > 0` >- (
                            FULL_SIMP_TAC arith_ss [thm]
                          )
                         )
              ) >>
(* 2. Describe case #blocks=1 *)
subgoal `?l' n' c_l'' st''.
           bir_exec_block_n prog st 1 = (l',n',c_l'',st'')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EXISTS]
) >>
(* 2. Describe case #blocks=m *)
subgoal `?l' n' c_l'' st''.
           bir_exec_block_n prog st m = (l',n',c_l'',st'')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EXISTS]
) >>
(* 3. Obtain execution from intermediate state *)
IMP_RES_TAC bir_exec_block_n_inter >>
(* 3. Instantiate universal quantifiers in induction hypothesis *)
QSPECL_X_ASSUM
  ``!prog. _`` [`prog`, `st''`, `l'''`, `n'''`, `c_l''''`, `st'`] >>
FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
subgoal `bir_trs prog st = SOME st''` >- (
  FULL_SIMP_TAC std_ss [bir_trs_def, LET_DEF] >>
  IMP_RES_TAC bir_exec_block_n_block_ls_running_running >>
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC std_ss []
);


val FUNPOW_OPT_bir_trs_to_bir_exec_block_n =
  store_thm("FUNPOW_OPT_bir_trs_to_bir_exec_block_n",
  ``!prog st m st'.
      (FUNPOW_OPT (bir_trs prog) m st = SOME st') ==>
      ?l n c_l'.
      (bir_exec_block_n prog st m = (l,n,c_l',st'))``,

Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
Cases_on `bir_trs prog st` >- (
  FULL_SIMP_TAC std_ss []
) >>
QSPECL_X_ASSUM
  ``!prog. _`` [`prog`, `x`, `st'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.ADD1] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add, bir_trs_def, LET_DEF] >>
Cases_on `x.bst_status = BST_Running` >> (
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `bir_exec_block_n prog st 1` >> Cases_on `r` >>
  Cases_on `r'` >>
  FULL_SIMP_TAC std_ss [LET_DEF]
)
);


(***********)
(* bir_trs *)

val bir_trs_term =
  store_thm("bir_trs_term",
  ``!prog st.
    bir_state_is_terminated st ==>
    (bir_trs prog st = NONE)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_trs_def] >>
IMP_RES_TAC bir_exec_block_n_REWR_TERMINATED >>
QSPECL_X_ASSUM ``!p n. _``
	       [`prog`, `1`] >>
FULL_SIMP_TAC std_ss [bir_state_is_terminated_def, LET_DEF]
);


val bir_trs_FUNPOW_term =
  store_thm("bir_trs_FUNPOW_term",
  ``!prog n st.
    bir_state_is_terminated st ==>
    n > 0 ==>
    (FUNPOW_OPT (bir_trs prog) n st = NONE)``,

REPEAT STRIP_TAC >>
Cases_on `n` >| [
  FULL_SIMP_TAC arith_ss [],

  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS, bir_trs_term]
]
);


val FUNPOW_OPT_bir_trs_running_invar =
  store_thm("FUNPOW_OPT_bir_trs_running_invar",
  ``!prog st m st'.
      (FUNPOW_OPT (bir_trs prog) m st = SOME st') ==>
      ~(bir_state_is_terminated st) ==>
      ~(bir_state_is_terminated st')``,

Induct_on `m` >> (
  REV_FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_trs_def, LET_DEF] >>
Cases_on `bir_exec_block_n prog st 1` >> Cases_on `r` >>
Cases_on `r'` >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `~bir_state_is_terminated r` >> (
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC []
)
);


val FUNPOW_OPT_bir_trs_running =
  store_thm("FUNPOW_OPT_bir_trs_running",
  ``!prog n st st'.
    (FUNPOW_OPT (bir_trs prog) n st = SOME st') ==>
    n > 0 ==>
    ~(bir_state_is_terminated st')``,

REPEAT STRIP_TAC >>
Cases_on `st.bst_status = BST_Running` >- (
  IMP_RES_TAC FUNPOW_OPT_bir_trs_running_invar >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `n` >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [FUNPOW_OPT_REWRS],

  FULL_SIMP_TAC (std_ss++holBACore_ss) [FUNPOW_OPT_REWRS,
                                        bir_trs_term]
]
);


val bir_weak_trs_EQ = store_thm("bir_weak_trs_EQ",
  ``!ls prog st st'.
    (bir_weak_trs ls prog st = SOME st') <=>
       (?l n n0.
       bir_exec_to_labels ls prog st =
         BER_Ended l n n0 st') /\
    ~bir_state_is_terminated st' /\
    (st'.bst_pc.bpc_index = 0) /\ st'.bst_pc.bpc_label IN ls
``,

REPEAT STRIP_TAC >>
EQ_TAC >| [
  DISCH_TAC >>
  FULL_SIMP_TAC std_ss [bir_weak_trs_def] >>
  Cases_on `bir_exec_to_labels ls prog st` >> ( 
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  IMP_RES_TAC bir_exec_to_labels_ended_running >>
  RW_TAC std_ss [],

  DISCH_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def]
]
);


(******************************************************************)
(*             Proof BIR instantiates weak model                  *)
(******************************************************************)

val bir_model_is_weak = store_thm("bir_model_is_weak",
  ``!(prog: 'a bir_program_t).
      weak_model (bir_etl_wm prog)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [weak_model_def, bir_etl_wm_def] >>
FULL_SIMP_TAC std_ss [bir_weak_trs_def, LET_DEF] >>
(* Need to show that bir_exec_to_labels is equivalent to some
 * non-zero application of bir_trs, where label set is touched in
 * last state, and last state only.
 * Note that bir_trs only gives SOME result for Running final
 * states. *)
REPEAT STRIP_TAC >>
CASE_TAC >| [
  (* Case 1: Result of bir_exec_to_labels is Ended - regular case *)
  CASE_TAC >| [
    (* Case 1A: Ended + Final state has status Running - regular
     *          case *)
    subgoal `?m c_l'. (m > 0) /\ (bir_exec_block_n prog ms m = (l,n,c_l',b))` >- (
      FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
      IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
      Q.EXISTS_TAC `m` >>
      Q.EXISTS_TAC `c_l'` >>
      FULL_SIMP_TAC arith_ss []
    ) >>
    IMP_RES_TAC bir_exec_to_labels_ended_running >>
    rename1 `bir_exec_block_n prog st m = (l,n,c_l',b)` >>
    rename1 `bir_exec_block_n prog st m = (l,n,c_l',st'')` >>
    EQ_TAC >| [
      (* Case 1AI *)
      (* Clean-up *)
      REPEAT DISCH_TAC >>
      rename1 `st'' = st'` >>
      Q.PAT_X_ASSUM `st'' = st'`
                    (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      EXISTS_TAC ``m:num`` >>
      FULL_SIMP_TAC arith_ss [] >>
      (* Prove first conjunct using
       * bir_exec_block_n_to_FUNPOW_OPT_bir_trs *)
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      REPEAT STRIP_TAC >>
      (* Prove new first conjunct using
       * bir_exec_block_n_to_FUNPOW_OPT_bir_trs *)
      rename1 `m' < m` >>
      ASSUME_TAC (Q.SPECL [`prog`, `st`, `m'`]
                          bir_exec_block_n_EXISTS) >>
      FULL_SIMP_TAC std_ss [] >>
      Q.EXISTS_TAC `st''` >>
      subgoal `~bir_state_is_terminated st''` >- (
	IMP_RES_TAC bir_exec_block_n_block_ls_running_running
      ) >>
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      (* Finally, use bir_exec_to_labels_block_n_notin_ls *)
      IMP_RES_TAC bir_exec_to_labels_block_n_notin_ls >>
      FULL_SIMP_TAC arith_ss [],

      (* Case 1AII: Assuming bir_trs plays nice, show that
       * b = st' (translate from bir_trs to block_n) *)
      (* Clean-up *)
      REPEAT STRIP_TAC >>
      IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
      rename1 `bir_exec_block_n prog st m' = (l',n'',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',st')` >>
      (* Prove that n = n' using the original hypothesis of the
       * goal *)
      subgoal `n = n'` >- (
	subgoal `~(n' < n)` >- (
	  IMP_RES_TAC bir_exec_to_labels_reached_ls
	) >>
	Cases_on `n < n'` >- (
	  (* This would mean that state b has crossed less than
           * m' blocks. Which entails, together with init
           * assumption, that PC label of b is not in ls (with
           * bir_exec_block_n_to_FUNPOW_OPT_bir_trs) *)
	  subgoal `m < m'` >- (
	    IMP_RES_TAC bir_exec_block_n_step_ls
	  ) >>
	  QSPECL_X_ASSUM
	    ``!n'.
	       n' < m' /\ n' > 0 ==>
	       ?ms''.
		   (FUNPOW_OPT (bir_trs prog) n' st = SOME ms'') /\
		   ms''.bst_pc.bpc_label NOTIN ls`` [`m`] >>
	  REV_FULL_SIMP_TAC arith_ss [] >>
	  IMP_RES_TAC bir_exec_block_n_to_FUNPOW_OPT_bir_trs >>
	  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
	  FULL_SIMP_TAC (std_ss++holBACore_ss) []
	) >>
        FULL_SIMP_TAC arith_ss []
      ) >>
      (* bir_exec_block_n_step_eq_running now gives us that the
       * number of block-steps are equal, so the block executions
       * must evaluate to the same state, which proves the goal. *)
      subgoal `m = m'` >- (
        subgoal `~bir_state_is_terminated st'` >- (
	  IMP_RES_TAC bir_exec_block_n_step_eq >>
	  REV_FULL_SIMP_TAC arith_ss []
        ) >>
        IMP_RES_TAC bir_exec_block_n_step_eq_running
      ) >>
      FULL_SIMP_TAC std_ss []
    ],

    (* Case 1B *)
    (* This means that Ended must have been reached by termination
     * somewhere. *)
    (* Repeated block execution can never have reached the label set
     * ls. Case 0 steps is forbidden, and for lower than the number
     * of block steps required to reach BER_Ended (which implicitly
     * has ended with termination) ls can't have been encountered,
     * or bir_exec_to_labels would have ended at that point before
     * termination. Meanwhile, at or after termination we can't
     * reach ls since we can't change PC label (and in any case
     * value of FUNPOW_OPT (bir_trs prog) would be NONE). *)
    FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
    REPEAT STRIP_TAC >>
    DISJ1_TAC >>
    rename1 `FUNPOW_OPT (bir_trs prog) n' st = SOME ms'` >>
    rename1 `FUNPOW_OPT (bir_trs prog) n' st = SOME st''` >>
    rename1
      `bir_exec_to_labels ls prog st = BER_Ended l n n0 st'` >>
    DISCH_TAC >>
    rename1 `m' > 0` >>
    DISCH_TAC >>
    rename1
      `bir_exec_to_labels ls prog st = BER_Ended l' n n0 st'` >>
    rename1
      `bir_exec_to_labels ls prog st = BER_Ended l' n' n0 st'` >>
    Cases_on `bir_state_is_terminated st` >- (
      IMP_RES_TAC bir_trs_FUNPOW_term >>
      FULL_SIMP_TAC std_ss []
    ) >>
    (* Translate to block-steps: *)
    (* If bir_exec_to_labels ended through termination, then we know
     * that the least number of necessary block-steps to get there
     * is some SUC m. *)
    subgoal
      `?m.
       ?c_l' l''' n''' c_l''' st'''.
       (bir_exec_block_n prog st (SUC m) = (l',n',c_l',st')) /\
       (bir_exec_block_n prog st m = (l''',n''',c_l''',st''')) /\
       ~(bir_state_is_terminated st''')` >- (
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC bir_exec_to_labels_bir_exec_block_n_term >>
      Q.EXISTS_TAC `m` >>
      FULL_SIMP_TAC std_ss []
    ) >>
    IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
    rename1
      `bir_exec_block_n prog st m' = (l'',n,c_l'',st'')` >>
    rename1
      `bir_exec_block_n prog st m' = (l'',n'',c_l'',st'')` >>
    (* Prove contradiction using negation of goal among
     * assumptions *)
    CCONTR_TAC >>
    FULL_SIMP_TAC std_ss [] >>
    subgoal `~bir_state_is_terminated st''` >- (
      IMP_RES_TAC FUNPOW_OPT_bir_trs_running
    ) >>
    subgoal `~(m' < (SUC m))` >- (
      IMP_RES_TAC bir_exec_to_labels_term_ls
    ) >>
    IMP_RES_TAC FUNPOW_OPT_bir_trs_running >>
    IMP_RES_TAC bir_exec_block_n_not_running_block_ge >>
    FULL_SIMP_TAC (arith_ss++holBACore_ss) []
  ],

  (* Case 2: Result of bir_exec_to_labels is Looping *)
  (* First, some clean-up *)
  FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
  REPEAT STRIP_TAC >>
  Cases_on `~(n > 0)` >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  rename1 `m > 0` >>
  DISJ1_TAC >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
  rename1 `bir_exec_block_n prog st m = (l',n,c_l',ms')` >>
  rename1 `bir_exec_block_n prog st m = (l',n,c_l',st')` >>
  (* Then, bir_exec_to_labels_looping_not_reached_ls gives us
   * contradiction on label set membership *)
  IMP_RES_TAC bir_exec_to_labels_looping_not_reached_ls >>
  REV_FULL_SIMP_TAC arith_ss []
]
);


(* Obtaining a bir_triple (weak_triple instantiation)
 * from a bir_exec_to_labels_triple *)
val bir_label_ht_impl_weak_ht =
  store_thm("bir_label_ht_impl_weak_ht",
  ``!prog l ls pre post.
    bir_exec_to_labels_triple prog l ls pre post ==>
    bir_triple prog l ls pre post``,

FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [bir_triple_def, weak_triple_def, bir_etl_wm_def,
               bir_exec_to_labels_triple_def,
               bir_exec_to_labels_triple_precond_def,
               bir_exec_to_labels_triple_postcond_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `s'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def,
                                      bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_ENV_ORDER >>
IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_ORDER
);


(* TODO: This actually combines two rules: Postcondition weakening and
 * precondition strenghtening *)
val bir_consequence_rule_thm =
  store_thm("bir_consequence_rule_thm",
  ``!prog l ls pre1 pre2 post1 post2.
    (!st. (st.bst_pc.bpc_label = l) ==>
          (bir_exec_to_labels_triple_precond st pre2 prog) ==>
          (bir_exec_to_labels_triple_precond st pre1 prog)
    ) ==>
    (!st. (st.bst_pc.bpc_label IN ls) ==>
          (bir_exec_to_labels_triple_postcond st post1 prog) ==>
          (bir_exec_to_labels_triple_postcond st post2 prog)
    ) ==>
    bir_triple prog l ls pre1 post1 ==>
    bir_triple prog l ls pre2 post2
  ``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_triple_def] >>
irule weak_weakening_rule_thm >>
REPEAT STRIP_TAC >- (
  METIS_TAC [bir_model_is_weak]
) >>
Q.EXISTS_TAC `\st. (bir_exec_to_labels_triple_postcond st post1 prog)` >>
Q.EXISTS_TAC `\st. (bir_exec_to_labels_triple_precond st pre1 prog)` >>
REPEAT STRIP_TAC >| [
  QSPECL_X_ASSUM ``!st. (st.bst_pc.bpc_label = l) ==> _`` [`ms`] >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def],

  QSPECL_X_ASSUM ``!st. (st.bst_pc.bpc_label IN ls) ==> _`` [`ms`] >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def],

  FULL_SIMP_TAC std_ss []
]
);

(* Precondition strengthening rule for use with bir_exp_is_taut *)
val bir_taut_pre_str_rule_thm = store_thm("bir_taut_pre_str_rule_thm",
  ``!pre pre' prog l ls post.
    ((bir_vars_of_exp pre') SUBSET (bir_vars_of_program prog)) ==>
    ((bir_vars_of_exp pre) SUBSET (bir_vars_of_program prog)) ==>
    bir_triple prog l ls pre post ==>
    bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre) ==>
    bir_triple prog l ls pre' post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_triple_def, weak_triple_def, bir_exec_to_labels_triple_precond_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `(bir_vars_of_exp pre' = bir_vars_of_exp pre) ==>
         !s.
             bir_is_bool_exp_env s.bst_environ pre' <=>
             bir_is_bool_exp_env s.bst_environ pre` >- (
  IMP_RES_TAC bir_exp_is_taut_same_vars_both_bool
) >>

FULL_SIMP_TAC std_ss [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
PAT_X_ASSUM ``!env. _`` (fn thm => ASSUME_TAC (Q.SPEC `s.bst_environ` thm)) >>
subgoal `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_exp
              (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre))` >- (
  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >> 
ASSUME_TAC (Q.SPECL [`s.bst_environ`, `pre'`, `pre`]  bir_exp_equivTheory.bir_impl_equiv) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp_env s.bst_environ pre` >- (
  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_is_bool_exp_REWRS,
                        bir_typing_expTheory.bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
                        bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
METIS_TAC []
);

(* Postcondition weakening rule for use with bir_exp_is_taut *)
val bir_taut_post_weak_rule_thm = store_thm("bir_taut_post_weak_rule_thm",
  ``!pre prog l ls l2 post post'.
    ((bir_vars_of_exp (post l2)) SUBSET (bir_vars_of_program prog)) ==>
    ((bir_vars_of_exp (post' l2)) SUBSET (bir_vars_of_program prog)) ==>
    (!l'. (l' <> l2) ==> (post l' = post' l')) ==>
    bir_triple prog l ls pre post ==>
    bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (post l2)) (post' l2)) ==>
    bir_triple prog l ls pre post'``,

FULL_SIMP_TAC std_ss [bir_triple_def, weak_triple_def, bir_exec_to_labels_triple_postcond_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.EXISTS_TAC `s'` >>
Cases_on `s'.bst_pc.bpc_label <> l2` >- (
  METIS_TAC []
) >>
Q.ABBREV_TAC `env' = s'.bst_environ` >>

subgoal `bir_env_vars_are_initialised env' (bir_vars_of_exp
                  (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (post l2))
                     (post' l2)))` >- (
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET]
) >>

IMP_RES_TAC bir_exp_tautologiesTheory.bir_exp_is_taut_def >>

subgoal `bir_is_bool_exp_env s'.bst_environ (post' l2)` >- (
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
                        bir_is_bool_exp_REWRS]
) >>

METIS_TAC [bir_exp_equivTheory.bir_impl_equiv, bir_exp_tautologiesTheory.bir_exp_is_taut_def]
);


(* bir_exec_to_labels_triple_precond can be swapped for
 * bir_exec_to_labels_triple_postcond *)
val bir_weak_triple_post_pre = store_thm("bir_weak_triple_post_pre",
  ``!prog ls1 ls2 post.
    (!l1. l1 IN ls1 ==> weak_triple (bir_etl_wm prog) l1 ls2
                          (\s'.
                             bir_exec_to_labels_triple_precond s' (post l1) prog
                          )
                          (\s'.
                             bir_exec_to_labels_triple_postcond s' post prog
                          )
    ) ==>
    (!l1. l1 IN ls1 ==> weak_triple (bir_etl_wm prog) l1 ls2
                          (\s'.
                             bir_exec_to_labels_triple_postcond s' post prog
                          )
                          (\s'.
                             bir_exec_to_labels_triple_postcond s' post prog
                          )
     )``,

REPEAT STRIP_TAC >>
ASSUME_TAC (Q.SPEC `prog` bir_model_is_weak) >>
QSPECL_X_ASSUM ``!l1'. _`` [`l1`] >>
REV_FULL_SIMP_TAC std_ss [weak_triple_def,
                          bir_exec_to_labels_triple_precond_def,
                          bir_exec_to_labels_triple_postcond_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!s'. _`` [`s'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.SUBGOAL_THEN `s'.bst_pc.bpc_label = l1` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def]
)
);


(* Main sequential composition theorem for bir_triples *)
val bir_seq_rule_thm = store_thm("bir_seq_rule_thm",
  ``!prog l ls1 ls2 pre post.
    bir_triple prog l (ls1 UNION ls2) pre post ==>
    (!l1. (l1 IN ls1) ==>
          bir_triple prog l1 ls2 (post l1) post) ==>
    bir_triple prog l ls2 pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_triple_def] >>
IMP_RES_TAC bir_weak_triple_post_pre >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
IMP_RES_TAC weak_seq_rule_thm
);


(* TODO: Why isn't bir_loop_contract defined in terms directly of weak_loop_contract?
(* Two requirements for this to be possible: Either x is of option type,
 * or var is also a function of x, to some inequality type. *)

(* Solution sketch: *)
val bir_loop_variant_value_def = Define `
  bir_loop_variant_value v st =
    if (bir_env_vars_are_initialised st.bst_environ (bir_vars_of_exp v))
    then let
           (* x computed here *)
         in
           SOME x
         end
    else NONE
`;
val bir_loop_contract_def = Define `
  bir_loop_contract prog (l:bir_label_t) le invariant C1 variant =
    (bir_vars_of_exp v) SUBSET (bir_vars_of_prog prog) /\
    weak_loop_contract (bir_etl_wm prog) (l:bir_label_t) le
      (\s. bir_exec_to_labels_triple_precond s invariant prog)
      (\s. bir_exec_to_labels_triple_precond s C1 prog)
      (\s. bir_loop_variant_value s variant)
`;

 *)
val bir_loop_contract_def = Define `
  bir_loop_contract prog l le invariant C1 variant =
    (~(l IN le)) /\
    (!x. (bir_triple prog l ({l} UNION le)
           (* (\ms. (invariant ms) /\ (C1 ms) /\ ((var ms) = x:num)) *)
           (BExp_BinExp BIExp_And invariant
             (BExp_BinExp BIExp_And
               C1
               (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 x)))
             )
           )
           (* (\ms.(((m.pc ms)=l) /\ (invariant ms) /\ ((var ms) < x) /\ ((var ms) >= 0)))) *)
	   (\l'. if l' = l then (BExp_BinExp BIExp_And invariant
		   		  (BExp_BinExp BIExp_And
				    (BExp_BinPred BIExp_LessThan variant (BExp_Const (Imm64 x)))
				    (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0w)) variant)
                                  )
			        )
                            else bir_exp_false
	   )
         )
    )
`;

val bir_signed_loop_contract_def = Define `
  bir_signed_loop_contract prog l le invariant C1 variant =
    (~(l IN le)) /\
    (!x. (bir_triple prog l ({l} UNION le)
           (* (\ms. (invariant ms) /\ (C1 ms) /\ ((var ms) = x:num)) *)
           (* TODO: Variant greater than 0 here? *)
           (BExp_BinExp BIExp_And invariant
             (BExp_BinExp BIExp_And
               C1
               (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 x)))
             )
           )
           (* (\ms.(((m.pc ms)=l) /\ (invariant ms) /\ ((var ms) < x) /\ ((var ms) >= 0)))) *)
	   (\l'. if l' = l then (BExp_BinExp BIExp_And invariant
		   		  (BExp_BinExp BIExp_And
				    (BExp_BinPred BIExp_SignedLessThan
                                      variant (BExp_Const (Imm64 x))
                                    )
				    (BExp_BinPred BIExp_SignedLessOrEqual
                                      (BExp_Const (Imm64 0w)) variant
                                    )
                                  )
			        )
                            else bir_exp_false
	   )
         )
    )
`;

(* TODO: Very ugly little critter... *)
val iv2i_def = Define `
    iv2i (BVal_Imm i) = i
`;


(* TODO: Check all theorems containing antecedents on initialization in the entirety of HolBA
 * to see if they can be resolved by new theorem giving variable initialisation... *)
(* Also booleanity and bir_eval_TF_is_bool *)

val bir_weak_triple_loop = store_thm("bir_weak_triple_loop",
  ``!prog l le invariant variant C1.
    (* Note: Due to the method of obtaining a number from the variant,
     * we need these two antecedents to prove
     * bir_eval_exp variant st.bst_environ = SOME (BVal_Imm (Imm64 w)) *)
    (type_of_bir_exp variant = SOME (BType_Imm Bit64)) ==>
    (bir_vars_of_exp variant) SUBSET (bir_vars_of_program prog) ==>
    (l NOTIN le) ==>
    (!x. weak_triple (bir_etl_wm prog) l ({l} UNION le)
      (\st. bir_exec_to_labels_triple_precond st
             (BExp_BinExp BIExp_And invariant
               (BExp_BinExp BIExp_And
                 C1
                 (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 (n2w x))))
               )
             )
             prog
      )
      (\st'. bir_exec_to_labels_triple_postcond st' 
               (\l'.
		  if l' = l then
		    BExp_BinExp BIExp_And invariant
		      (BExp_BinExp BIExp_And
			 (BExp_BinPred BIExp_LessThan variant
			    (BExp_Const (Imm64 (n2w x))))
			 (BExp_BinPred BIExp_LessOrEqual
			    (BExp_Const (Imm64 0w)) variant))
		  else bir_exp_false
               ) prog
      )
    ) ==>
    weak_loop_contract (bir_etl_wm prog) l le
      (\st. bir_exec_to_labels_triple_precond st invariant prog)
      (\st. bir_eval_exp C1 st.bst_environ = SOME bir_val_true)
      (\st. b2n (iv2i (THE (bir_eval_exp variant st.bst_environ))))``,

FULL_SIMP_TAC std_ss [weak_loop_contract_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_triple_def] >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!x st. _`` [`x`, `st`] >>

(* This is needed for both steps below *)
subgoal `bir_eval_exp variant st.bst_environ = SOME (BVal_Imm (Imm64 (n2w x)))` >- (
  IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  Q.SUBGOAL_THEN `va = (BVal_Imm (Imm64 (n2w x)))` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    IMP_RES_TAC (el 5 (CONJUNCTS bir_eval_imm_types)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    RW_TAC std_ss [wordsTheory.n2w_w2n, iv2i_def, bir_immTheory.b2n_def]
  )
) >>

(* Prove precondition of the weak triple using precondition of the weak loop contract *)
Q.SUBGOAL_THEN `bir_exec_to_labels_triple_precond st
		  (BExp_BinExp BIExp_And invariant
		     (BExp_BinExp BIExp_And C1
			(BExp_BinPred BIExp_Equal variant
			   (BExp_Const (Imm64 (n2w x)))))) prog`
  (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, GSYM bir_and_equiv,
                   bir_is_bool_exp_env_REWRS] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
     bir_vars_of_exp_def, bir_val_true_def, bir_is_bool_exp_env_def] >>
  subgoal `type_of_bir_val (BVal_Imm (Imm1 1w)) = BType_Imm Bit1` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET, bir_is_bool_exp_def,
             bir_eval_exp_IS_SOME_IMPLIES_INIT, bir_eval_exp_IS_SOME_IMPLIES_TYPE]
) >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_postcond_def] >>

(* Prove the postcondition of the weak loop contract using the postcondition of the weak triple *)
Q.EXISTS_TAC `st'` >>
Cases_on `st'.bst_pc.bpc_label <> l` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_exp_TF, bir_val_TF_dist]
) >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
  [bir_is_bool_exp_env_REWRS,
   bir_etl_wm_def, bir_weak_trs_EQ, GSYM bir_and_equiv] >>
subgoal `b2n (iv2i (THE (bir_eval_exp variant st'.bst_environ))) < x` >- (
  subgoal `?x'. bir_eval_exp variant st'.bst_environ =
                  SOME (BVal_Imm (Imm64 x'))` >- (
    subgoal `?va. (bir_eval_exp variant st'.bst_environ = SOME va) /\
                   (type_of_bir_val va = (BType_Imm it'))` >- (
      METIS_TAC [type_of_bir_exp_THM_with_init_vars]
    ) >>
    METIS_TAC [bir_eval_imm_types]
  ) >>
  `bir_imm_word_lo (bir_eval_exp variant st'.bst_environ)
                     (bir_eval_exp (BExp_Const (Imm64 (n2w x))) st'.bst_environ)` suffices_by (
     FULL_SIMP_TAC (arith_ss++holBACore_ss) [bir_imm_word_lo_def, wordsTheory.WORD_LO,
                                             wordsTheory.w2n_n2w, iv2i_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lessthan_equiv, bir_imm_word_lo_def, bir_val_true_def]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

val bir_weak_triple_signed_loop = store_thm("bir_weak_triple_signed_loop",
  ``!prog l le invariant variant C1.
    (* Note: Due to the method of obtaining a number from the variant,
     * we need these two antecedents to prove
     * bir_eval_exp variant st.bst_environ = SOME (BVal_Imm (Imm64 w)) *)
    (type_of_bir_exp variant = SOME (BType_Imm Bit64)) ==>
    (bir_vars_of_exp variant) SUBSET (bir_vars_of_program prog) ==>
    (l NOTIN le) ==>
    (!x. weak_triple (bir_etl_wm prog) l ({l} UNION le)
      (\st. bir_exec_to_labels_triple_precond st
             (BExp_BinExp BIExp_And invariant
               (BExp_BinExp BIExp_And
                 C1
                 (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 (n2w x))))
               )
             )
             prog
      )
      (\st'. bir_exec_to_labels_triple_postcond st' 
               (\l'.
		  if l' = l then
		    BExp_BinExp BIExp_And invariant
		      (BExp_BinExp BIExp_And
			 (BExp_BinPred BIExp_SignedLessThan variant
			    (BExp_Const (Imm64 (n2w x))))
			 (BExp_BinPred BIExp_SignedLessOrEqual
			    (BExp_Const (Imm64 0w)) variant))
		  else bir_exp_false
               ) prog
      )
    ) ==>
    weak_loop_contract (bir_etl_wm prog) l le
      (\st. bir_exec_to_labels_triple_precond st invariant prog)
      (\st. bir_eval_exp C1 st.bst_environ = SOME bir_val_true)
      (\st. b2n (iv2i (THE (bir_eval_exp variant st.bst_environ))))``,

FULL_SIMP_TAC std_ss [weak_loop_contract_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [weak_triple_def] >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!x st. _`` [`x`, `st`] >>

(* This is needed for both steps below *)
subgoal `bir_eval_exp variant st.bst_environ = SOME (BVal_Imm (Imm64 (n2w x)))` >- (
  IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  Q.SUBGOAL_THEN `va = (BVal_Imm (Imm64 (n2w x)))` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    IMP_RES_TAC (el 5 (CONJUNCTS bir_eval_imm_types)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    RW_TAC std_ss [wordsTheory.n2w_w2n, iv2i_def, bir_immTheory.b2n_def]
  )
) >>

(* Prove precondition of the weak triple using precondition of the weak loop contract *)
Q.SUBGOAL_THEN `bir_exec_to_labels_triple_precond st
		  (BExp_BinExp BIExp_And invariant
		     (BExp_BinExp BIExp_And C1
			(BExp_BinPred BIExp_Equal variant
			   (BExp_Const (Imm64 (n2w x)))))) prog`
  (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, GSYM bir_and_equiv,
                   bir_is_bool_exp_env_REWRS] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
     bir_vars_of_exp_def, bir_val_true_def, bir_is_bool_exp_env_def] >>
  subgoal `type_of_bir_val (BVal_Imm (Imm1 1w)) = BType_Imm Bit1` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET, bir_is_bool_exp_def,
             bir_eval_exp_IS_SOME_IMPLIES_INIT, bir_eval_exp_IS_SOME_IMPLIES_TYPE]
) >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_postcond_def] >>

(* Prove the postcondition of the weak loop contract using the postcondition of the weak triple *)
Q.EXISTS_TAC `st'` >>
Cases_on `st'.bst_pc.bpc_label <> l` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_exp_TF, bir_val_TF_dist]
) >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
  [bir_is_bool_exp_env_REWRS,
   bir_etl_wm_def, bir_weak_trs_EQ, GSYM bir_and_equiv] >>
subgoal `b2n (iv2i (THE (bir_eval_exp variant st'.bst_environ))) < x` >- (
  subgoal `?x'. bir_eval_exp variant st'.bst_environ =
                  SOME (BVal_Imm (Imm64 x'))` >- (
    subgoal `?va. (bir_eval_exp variant st'.bst_environ = SOME va) /\
                   (type_of_bir_val va = (BType_Imm it'))` >- (
      METIS_TAC [type_of_bir_exp_THM_with_init_vars]
    ) >>
    METIS_TAC [bir_eval_imm_types]
  ) >>
  `bir_imm_word_lt (bir_eval_exp variant st'.bst_environ)
                     (bir_eval_exp (BExp_Const (Imm64 (n2w x))) st'.bst_environ)` suffices_by (
     FULL_SIMP_TAC (arith_ss++holBACore_ss++wordsLib.WORD_ss)
       [bir_imm_word_lt_def, wordsTheory.WORD_LT,
        iv2i_def, wordsTheory.WORD_LE,
        bir_val_true_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_slessthan_equiv, bir_imm_word_lt_def, bir_val_true_def]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
);


(* This should be used to instantiate weak_while_rule_thm *)
val bir_weak_triple_precond_conj = store_thm("bir_weak_triple_precond_conj",
  ``!prog l le invariant C1 post.
    weak_triple (bir_etl_wm prog) l le
      (\s.
	   bir_exec_to_labels_triple_precond s
	     (BExp_BinExp BIExp_And invariant
		(BExp_UnaryExp BIExp_Not C1)) prog)
      (\s'. bir_exec_to_labels_triple_postcond s' post prog) ==>
    weak_triple (bir_etl_wm prog) l le
      (\s. (bir_exec_to_labels_triple_precond s invariant prog) /\
           (* All the precondition stuff here as well, but we only need booleanity of C1 *)
           (bir_exec_to_labels_triple_precond s (BExp_UnaryExp BIExp_Not C1) prog)
      )
      (\s'. bir_exec_to_labels_triple_postcond s' post prog)``,

FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def,
                      bir_exec_to_labels_triple_postcond_def,
                      weak_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
REV_FULL_SIMP_TAC std_ss [GSYM bir_and_equiv, bir_not_equiv, 
                          bir_is_bool_exp_env_REWRS] >>
Q.EXISTS_TAC `s'` >>
FULL_SIMP_TAC std_ss []
);

(* Likewise, use weak_invariant_rule_thm to prove the BIR version of it.
 * Called bir_while_rule_thm to distinguish from bir_do_while_rule_thm *)
val bir_while_rule_thm = store_thm("bir_while_rule_thm",
  ``!prog l le invariant C1 var post.
    (* Compute in place using proof procedures: *)
    (*   These two needed to use bir_weak_triple_loop *)
    (type_of_bir_exp var = SOME (BType_Imm Bit64)) ==>
    bir_vars_of_exp var SUBSET bir_vars_of_program prog ==>
    (*   These two needed to prove bir_is_bool_exp_env ms.bst_environ C1 *)
    bir_is_bool_exp C1 ==>
    (bir_vars_of_exp C1) SUBSET (bir_vars_of_program prog) ==>
    (* Obtain bir_loop contract through some rule: *)
    bir_loop_contract prog l le
      invariant
      C1 var ==>
    bir_triple prog l le
      (BExp_BinExp BIExp_And
        invariant
        (BExp_UnaryExp BIExp_Not C1)
      ) post ==>
    bir_triple prog l le
      invariant
      post``,

FULL_SIMP_TAC std_ss [bir_triple_def, bir_loop_contract_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
(* 1. Somehow obtain the (correct) weak_loop_contract from bir_loop_contract *)
subgoal `weak_loop_contract (bir_etl_wm prog) l le
           (\st. bir_exec_to_labels_triple_precond st invariant prog)
           (\st. bir_eval_exp C1 st.bst_environ = SOME bir_val_true)
           (\st. b2n (iv2i (THE (bir_eval_exp var st.bst_environ))))` >- (
  IMP_RES_TAC bir_weak_triple_loop >>
  QSPECL_X_ASSUM ``!invariant. _`` [`invariant`] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
(* Delete used-up assumptions *)
Q.PAT_X_ASSUM `!x. _` (fn thm => ALL_TAC) >>
Q.PAT_X_ASSUM `l NOTIN ls` (fn thm => ALL_TAC) >>
(* 2. Change the BIR conjunction to a HOL conjunction *)
subgoal `weak_triple (bir_etl_wm prog) l le
	   (\ms.
	      (\s. bir_exec_to_labels_triple_precond s invariant prog) ms /\
	      ~(\s. bir_eval_exp C1 s.bst_environ = SOME bir_val_true) ms)
	      (\s. bir_exec_to_labels_triple_postcond s post prog)` >- (
  IMP_RES_TAC bir_weak_triple_precond_conj >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  REPEAT STRIP_TAC >>
  subgoal `bir_is_bool_exp_env ms.bst_environ C1` >- (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_exec_to_labels_triple_precond_def] >>
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET
  ) >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  IMP_RES_TAC bir_not_equiv >>
  REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS, bir_exec_to_labels_triple_precond_def]
) >>
(* 3. Use weak_invariant_rule_thm *)
IMP_RES_TAC weak_invariant_rule_thm
);

(* Signed version of the above *)
val bir_signed_while_rule_thm = store_thm("bir_signed_while_rule_thm",
  ``!prog l le invariant C1 var post.
    (* Compute in place using proof procedures: *)
    (*   These two needed to use bir_weak_triple_loop *)
    (type_of_bir_exp var = SOME (BType_Imm Bit64)) ==>
    bir_vars_of_exp var SUBSET bir_vars_of_program prog ==>
    (*   These two needed to prove bir_is_bool_exp_env ms.bst_environ C1 *)
    bir_is_bool_exp C1 ==>
    (bir_vars_of_exp C1) SUBSET (bir_vars_of_program prog) ==>
    (* Obtain bir_loop contract through some rule: *)
    bir_signed_loop_contract prog l le
      invariant
      C1 var ==>
    bir_triple prog l le
      (BExp_BinExp BIExp_And
        invariant
        (BExp_UnaryExp BIExp_Not C1)
      ) post ==>
    bir_triple prog l le
      invariant
      post``,

FULL_SIMP_TAC std_ss [bir_triple_def, bir_signed_loop_contract_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
(* 1. Somehow obtain the (correct) weak_loop_contract from bir_loop_contract *)
subgoal `weak_loop_contract (bir_etl_wm prog) l le
           (\st. bir_exec_to_labels_triple_precond st invariant prog)
           (\st. bir_eval_exp C1 st.bst_environ = SOME bir_val_true)
           (\st. b2n (iv2i (THE (bir_eval_exp var st.bst_environ))))` >- (
  IMP_RES_TAC bir_weak_triple_signed_loop >>
  QSPECL_X_ASSUM ``!invariant. _`` [`invariant`] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
(* Delete used-up assumptions *)
Q.PAT_X_ASSUM `!x. _` (fn thm => ALL_TAC) >>
Q.PAT_X_ASSUM `l NOTIN ls` (fn thm => ALL_TAC) >>
(* 2. Change the BIR conjunction to a HOL conjunction *)
subgoal `weak_triple (bir_etl_wm prog) l le
	   (\ms.
	      (\s. bir_exec_to_labels_triple_precond s invariant prog) ms /\
	      ~(\s. bir_eval_exp C1 s.bst_environ = SOME bir_val_true) ms)
	      (\s. bir_exec_to_labels_triple_postcond s post prog)` >- (
  IMP_RES_TAC bir_weak_triple_precond_conj >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  REPEAT STRIP_TAC >>
  subgoal `bir_is_bool_exp_env ms.bst_environ C1` >- (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_exec_to_labels_triple_precond_def] >>
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET
  ) >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  IMP_RES_TAC bir_not_equiv >>
  REV_FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS, bir_exec_to_labels_triple_precond_def]
) >>
(* 3. Use weak_invariant_rule_thm *)
IMP_RES_TAC weak_invariant_rule_thm
);

(*****************************************************)
(* BIR map triple theorems                           *)
(*****************************************************)

(* How to obtain a bir_map_triple from a bir_triple: *)
val bir_triple_equiv_map_triple = store_thm("bir_triple_equiv_map_triple",
  ``!prog invariant l ls ls' pre post.
    bir_map_triple prog invariant l ls ls' pre post <=>
      (((ls INTER ls') = EMPTY) /\
       (bir_triple prog l (ls UNION ls')
		   (BExp_BinExp BIExp_And pre invariant)
		   (\label. if (label IN ls)
			    then (BExp_BinExp BIExp_And (post label) invariant)
			    else bir_exp_false
		   )
       )
      )
  ``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_triple_def, bir_map_triple_def, weak_map_triple_def] >>
EQ_TAC >> (
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss []
) >| [
  (* bir_map_triple -> bir_triple *)
  subgoal `bir_exec_to_labels_triple_precond s pre prog /\
           bir_exec_to_labels_triple_precond s invariant prog` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, bir_is_bool_exp_env_REWRS,
                          GSYM bir_and_equiv]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
  Cases_on `s'.bst_pc.bpc_label IN ls` >| [
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS, GSYM bir_and_equiv,
                          bir_exec_to_labels_triple_precond_def],

    (* We know that s'.pc NOTIN ls', but also that ls INTER ls' = {}, s'.bst_status = BST_Running and
     * that (bir_etl_wm prog).weak s (ls UNION ls') s'. Ergo, s'.pc must be in ls. *)
    (*FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def, bir_eval_exp_TF,
                                         bir_val_TF_dist]*)
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def] >>
    `s'.bst_pc.bpc_label IN (ls UNION ls')` suffices_by
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
    FULL_SIMP_TAC std_ss [bir_weak_trs_EQ]
  ],

  (* bir_triple -> bir_map_triple *)
  subgoal `bir_exec_to_labels_triple_precond s
             (BExp_BinExp BIExp_And pre invariant) prog` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, bir_is_bool_exp_env_REWRS,
                          GSYM bir_and_equiv]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
  Cases_on `s'.bst_pc.bpc_label IN ls` >| [
    (* What needs to be added is similar to cheated case above... *)
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_is_bool_exp_env_REWRS, GSYM bir_and_equiv,
                                       bir_exec_to_labels_triple_precond_def, bir_etl_wm_def,
                                       bir_weak_trs_EQ] >>
    METIS_TAC [INTER_EMPTY_IN_NOT_IN_thm],

    FULL_SIMP_TAC std_ss [bir_eval_exp_TF, bir_val_TF_dist]
  ]
]
);

val bir_triple_equiv_map_triple_alt = store_thm("bir_triple_equiv_map_triple_alt",
  ``!prog invariant l ls ls' pre post.
    bir_map_triple prog invariant l ls ls' pre post <=>
      (((ls INTER ls') = EMPTY) /\
       (bir_triple prog l (ls UNION ls')
		   (BExp_BinExp BIExp_And pre invariant)
		   (\label. if (label IN ls')
			    then bir_exp_false
			    else (BExp_BinExp BIExp_And (post label) invariant)
		   )
       )
      )
  ``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_triple_def, bir_map_triple_def, weak_map_triple_def] >>
EQ_TAC >> (
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss []
) >| [
  (* bir_map_triple -> bir_triple *)
  subgoal `bir_exec_to_labels_triple_precond s pre prog /\
           bir_exec_to_labels_triple_precond s invariant prog` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, bir_is_bool_exp_env_REWRS,
                          GSYM bir_and_equiv]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
  Cases_on `s'.bst_pc.bpc_label IN ls'` >| [
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def],

    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS, GSYM bir_and_equiv,
                          bir_exec_to_labels_triple_precond_def]
  ],

  (* bir_triple -> bir_map_triple *)
  subgoal `bir_exec_to_labels_triple_precond s
             (BExp_BinExp BIExp_And pre invariant) prog` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, bir_is_bool_exp_env_REWRS,
                          GSYM bir_and_equiv]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
  Cases_on `s'.bst_pc.bpc_label IN ls'` >| [
    FULL_SIMP_TAC std_ss [bir_eval_exp_TF, bir_val_TF_dist],

    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_is_bool_exp_env_REWRS, GSYM bir_and_equiv,
                                       bir_exec_to_labels_triple_precond_def, bir_etl_wm_def]
  ]
]
);



(* bir_map_triples are all generated from bir_triples, which have no explicit notion
 * of blacklist. This theorem moves ending labels which are implicitly
 * blacklisted by the postcondition from the whitelist of a bir_map_triple to the blacklist. *)
val bir_map_triple_move_to_blacklist = store_thm("bir_map_triple_move_to_blacklist",
  ``!prog inv l wlist blist pre post elabel.
    bir_map_triple prog inv l wlist blist pre post ==>
    elabel IN wlist ==>
    (post elabel = bir_exp_false) ==>
    bir_map_triple prog inv l (wlist DELETE elabel) (elabel INSERT blist) pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
irule weak_map_move_to_blacklist >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
FULL_SIMP_TAC std_ss [] >>
GEN_TAC >> DISCH_TAC >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def, bir_eval_exp_TF, bir_val_TF_dist]
);

val bir_map_triple_move_set_to_blacklist = store_thm("bir_map_triple_move_set_to_blacklist",
  ``!prog inv l wlist blist pre post elabels.
    bir_map_triple prog inv l wlist blist pre post ==>
    FINITE elabels ==>
    elabels SUBSET wlist ==>
    (!elabel. elabel IN elabels ==> (post elabel = bir_exp_false)) ==>
    bir_map_triple prog inv l (wlist DIFF elabels) (elabels UNION blist) pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def, pred_setTheory.UNION_COMM] >>
irule weak_map_move_set_to_blacklist >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
FULL_SIMP_TAC std_ss [] >>
NTAC 2 STRIP_TAC >>
QSPECL_X_ASSUM ``!prog. _`` [`(bir_etl_wm prog).pc ms`] >>
SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def] >>
FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def, bir_eval_exp_TF, bir_val_TF_dist]
);


(* Shrinking the Ending label set is possible if the corresponding postcondition never holds. *)
val bir_subset_rule_thm =
 store_thm("bir_subset_rule_thm",
  ``!prog l ls1 ls2 pre post .
    (!st. (bir_eval_exp (post st.bst_pc.bpc_label) st.bst_environ = SOME bir_val_true) ==>
          (~(st.bst_pc.bpc_label IN ls2))
    ) ==>
    bir_triple prog l (ls1 UNION ls2) pre post ==>
    bir_triple prog l ls1 pre post``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [bir_triple_def, weak_triple_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
ASSUME_TAC (SPECL [``prog:'a bir_program_t``] bir_model_is_weak) >>
REV_FULL_SIMP_TAC std_ss [] >>
IMP_RES_TAC weak_union_pc_not_in_thm >>
QSPECL_X_ASSUM ``!st. _`` [`s'`] >>
subgoal `bir_eval_exp (post s'.bst_pc.bpc_label) s'.bst_environ =
          SOME bir_val_true` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def]
) >>
FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def]
);


val bir_map_weakening_rule_thm = store_thm("bir_map_weakening_rule_thm",
  ``!prog invariant l ls ls' pre post1 post2.
    (!st.
     st.bst_pc.bpc_label IN ls ==>
     (bir_eval_exp (post1 st.bst_pc.bpc_label) st.bst_environ = SOME bir_val_true) ==>
     (bir_eval_exp (post2 st.bst_pc.bpc_label) st.bst_environ = SOME bir_val_true)
    ) ==>
    bir_map_triple prog invariant l ls ls' pre post1 ==>
    bir_map_triple prog invariant l ls ls' pre post2``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
irule weak_map_weakening_rule_thm >>
REPEAT STRIP_TAC >- (
  METIS_TAC [bir_model_is_weak]
) >>
Q.EXISTS_TAC `\s'. bir_exec_to_labels_triple_postcond s' post1 prog` >>
REPEAT STRIP_TAC >| [
  QSPECL_X_ASSUM ``!st. _`` [`ms`] >>
  Q.SUBGOAL_THEN `ms.bst_pc.bpc_label IN ls` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def]
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def, bir_is_bool_exp_env_def,
                        bir_val_true_def] >>
  METIS_TAC [bir_eval_TF_is_bool, bir_eval_exp_IS_SOME_IMPLIES_INIT],

  FULL_SIMP_TAC std_ss []
]
);


val bir_taut_map_pre_str_rule_thm = store_thm("bir_taut_map_pre_str_rule_thm",
  ``!prog invariant l ls ls' pre1 pre2 post.
    ((bir_vars_of_exp pre2) SUBSET (bir_vars_of_program prog)) ==>
    ((bir_vars_of_exp pre1) SUBSET (bir_vars_of_program prog)) ==>
    bir_exp_is_taut
      (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre2) pre1) ==>
    bir_map_triple prog invariant l ls ls' pre1 post ==>
    bir_map_triple prog invariant l ls ls' pre2 post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def, weak_map_triple_def, weak_triple_def,
                      bir_exec_to_labels_triple_precond_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `(bir_vars_of_exp pre2 = bir_vars_of_exp pre1) ==>
         !s.
             bir_is_bool_exp_env s.bst_environ pre2 <=>
             bir_is_bool_exp_env s.bst_environ pre1` >- (
  IMP_RES_TAC bir_exp_is_taut_same_vars_both_bool
) >>
FULL_SIMP_TAC std_ss [bir_exp_is_taut_def] >>
PAT_X_ASSUM ``!env. _`` (fn thm => ASSUME_TAC (Q.SPEC `s.bst_environ` thm)) >>
subgoal `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_exp
              (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre2) pre1))` >- (
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >> 
ASSUME_TAC (Q.SPECL [`s.bst_environ`, `pre2`, `pre1`]  bir_exp_equivTheory.bir_impl_equiv) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp_env s.bst_environ pre1` >- (
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS, bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
                        bir_is_bool_exp_env_def]
) >>
METIS_TAC []
);


val bir_taut_map_post_weak_rule_thm = store_thm("bir_taut_map_post_weak_rule_thm",
  ``!prog invariant l ls l2 ls' pre post1 post2.
    ((bir_vars_of_exp (post1 l2)) SUBSET (bir_vars_of_program prog)) ==>
    ((bir_vars_of_exp (post2 l2)) SUBSET (bir_vars_of_program prog)) ==>
    (!l'. (l' <> l2) ==> (post1 l' = post2 l')) ==>
    bir_exp_is_taut
      (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (post1 l2)) (post2 l2)) ==>
    bir_map_triple prog invariant l ls ls' pre post1 ==>
    bir_map_triple prog invariant l ls ls' pre post2``,

FULL_SIMP_TAC std_ss [bir_map_triple_def, weak_map_triple_def, weak_triple_def,
                      bir_exec_to_labels_triple_postcond_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.EXISTS_TAC `s'` >>
Cases_on `s'.bst_pc.bpc_label <> l2` >- (
  METIS_TAC []
) >>
Q.ABBREV_TAC `env' = s'.bst_environ` >>
FULL_SIMP_TAC std_ss [] >>

subgoal `bir_env_vars_are_initialised env' (bir_vars_of_exp
                  (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (post1 l2))
                     (post2 l2)))` >- (
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET]
) >>

IMP_RES_TAC bir_exp_tautologiesTheory.bir_exp_is_taut_def >>

subgoal `bir_is_bool_exp_env s'.bst_environ (post2 l2)` >- (
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
                        bir_is_bool_exp_REWRS]
) >>

METIS_TAC [bir_exp_equivTheory.bir_impl_equiv, bir_exp_tautologiesTheory.bir_exp_is_taut_def]
);


val bir_map_std_seq_comp_thm =
  store_thm("bir_map_std_seq_comp_thm",
  ``!prog ls1 ls1' ls2 ls2' invariant l pre1 post1 post2.
    ls1' SUBSET ls2 ==>
    (ls1 INTER ls1' = EMPTY) ==>
    (ls1' INTER ls2' = EMPTY) ==>
    bir_map_triple prog invariant l ls1 ls2 pre1 post1 ==>
    (!l1. (l1 IN ls1) ==> (bir_map_triple prog invariant l1 ls1' ls2' (post1 l1) post2)) ==>
    bir_map_triple prog invariant l ls1' (ls2 INTER ls2') pre1 post2``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
irule weak_map_std_seq_comp_thm >>
REPEAT STRIP_TAC >- (
  METIS_TAC [bir_model_is_weak]
) >> (
  FULL_SIMP_TAC std_ss []
) >>
Q.EXISTS_TAC `ls1` >>
Q.EXISTS_TAC `\s. bir_exec_to_labels_triple_precond s (post1 ((bir_etl_wm prog).pc s)) prog` >>
REPEAT STRIP_TAC >> (
  FULL_SIMP_TAC std_ss []
) >| [
  QSPECL_X_ASSUM ``!l1. _`` [`l1`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def, weak_triple_def,
                        bir_exec_to_labels_triple_precond_def],

  FULL_SIMP_TAC (std_ss++bir_wm_SS) [weak_map_triple_def,
                                     bir_exec_to_labels_triple_precond_def,
                                     bir_exec_to_labels_triple_postcond_def,
                                     bir_etl_wm_def]
]
);


val _ = export_theory();
