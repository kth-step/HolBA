open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_program_env_orderTheory;
open bir_exp_equivTheory;
open bir_bool_expTheory;
open bir_typing_expTheory;
open bir_subprogramTheory;
open bir_program_valid_stateTheory;
open bir_typing_progTheory;
open bir_exp_tautologiesTheory;
open bir_htTheory;

open abstract_hoare_logicTheory;
open abstract_simp_hoare_logicTheory;

open abstract_hoare_logicSimps;
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
    ((bir_eval_exp pre st.bst_environ = SOME bir_val_true) /\
    (bir_env_vars_are_initialised st.bst_environ
       (bir_vars_of_program prog)) /\
    (st.bst_pc.bpc_index = 0) /\
    (st.bst_status = BST_Running) /\
    (bir_is_bool_exp_env st.bst_environ pre))
`;

(* We don't need the condition that st.bst_pc.bpc_label IN ls here,
 * since we can obtain that result from weak_pc_in_thm. *)
val bir_exec_to_labels_triple_postcond_def = Define `
  bir_exec_to_labels_triple_postcond st post prog =
    ((bir_eval_exp (post st.bst_pc.bpc_label) st.bst_environ =
       SOME bir_val_true) /\
    (bir_env_vars_are_initialised st.bst_environ
       (bir_vars_of_program prog)) /\
    (st.bst_pc.bpc_index = 0) /\
    (st.bst_status = BST_Running) /\
    (bir_is_bool_exp_env st.bst_environ (post st.bst_pc.bpc_label)))
`;


(* BIR map triple, mirroring weak_map_triple *)
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

(*****************************************************)
(* BIR map triple theorems                           *)
(*****************************************************)

(* Obtaining a bir_map_triple from a bir_exec_to_labels_triple *)
val bir_label_ht_impl_weak_ht =
  store_thm("bir_label_ht_impl_weak_ht",
  ``!prog l ls pre post.
    ls <> {} ==>
    bir_exec_to_labels_triple prog l ls pre post ==>
    bir_map_triple prog bir_exp_true l ls {} pre post``,

FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [bir_map_triple_def, weak_map_triple_def,
               weak_triple_def, bir_etl_wm_def,
               bir_exec_to_labels_triple_def,
               bir_exec_to_labels_triple_precond_def,
               bir_exec_to_labels_triple_postcond_def] >>
REPEAT STRIP_TAC >> (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `s'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_weak_trs_def,
				      bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_ENV_ORDER >>
IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_ORDER >>
ASM_SIMP_TAC std_ss [bir_eval_exp_TF, bir_is_bool_exp_env_REWRS]
);

(* This theorem moves ending labels which are implicitly
 * blacklisted by the postcondition from the whitelist of a bir_map_triple to the blacklist. *)
val bir_map_triple_move_to_blacklist = store_thm("bir_map_triple_move_to_blacklist",
  ``!prog inv l wlist blist pre post elabel.
    bir_map_triple prog inv l wlist blist pre post ==>
    elabel IN wlist ==>
    wlist DELETE elabel <> {} ==>
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
    elabels PSUBSET wlist ==>
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


val iv2i_def = Define `
    iv2i (BVal_Imm i) = i
`;

val bir_map_signed_loop_thm = store_thm("bir_map_signed_loop_thm",
  ``!prog l wl bl invariant C1 variant post.
    (* Compute in place using proof procedures: *)
    (*   These two needed to use weak_map_loop_thm *)
    (type_of_bir_exp variant = SOME (BType_Imm Bit64)) ==>
    bir_vars_of_exp variant SUBSET bir_vars_of_program prog ==>
    (*   These two needed to prove bir_is_bool_exp_env ms.bst_environ C1 *)
    bir_is_bool_exp C1 ==>
    (bir_vars_of_exp C1) SUBSET (bir_vars_of_program prog) ==>
    (* Extra for weak_map_loop_thm *)
    l NOTIN wl ==>
    l NOTIN bl ==>
    (wl INTER bl = {}) ==>
    (* Obtain bir_loop contract through some rule: *)
    (!x.
     bir_map_triple prog invariant l ({l} UNION wl) bl
       (BExp_BinExp BIExp_And C1
	  (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 x)))
       )
       (\l'.
	    if l' = l then
	      (BExp_BinExp BIExp_And
		 (BExp_BinPred BIExp_SignedLessThan variant
		    (BExp_Const (Imm64 x)))
		 (BExp_BinPred BIExp_SignedLessOrEqual
		    (BExp_Const (Imm64 0w)) variant))
	    else bir_exp_false)
    ) ==>
    bir_map_triple prog bir_exp_true l wl bl
      (BExp_BinExp BIExp_And invariant (BExp_UnaryExp BIExp_Not C1)) post ==>
    bir_map_triple prog bir_exp_true l wl bl
      invariant
      post``,

FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
(* 1. Use weak_map_loop_thm *)
Q.SUBGOAL_THEN `weak_map_triple (bir_etl_wm prog)
     (\s. bir_exec_to_labels_triple_precond s bir_exp_true prog) l wl bl
     (\s. bir_exec_to_labels_triple_precond s invariant prog)
     (\s'. bir_exec_to_labels_triple_postcond s' post prog) <=>
  weak_map_triple (bir_etl_wm prog)
     (\s. T) l wl bl
     (\s. bir_exec_to_labels_triple_precond s invariant prog)
     (\s'. bir_exec_to_labels_triple_postcond s' post prog)`
  (fn thm => SIMP_TAC std_ss [thm]) >- (
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
  SIMP_TAC std_ss [weak_triple_def] >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    QSPECL_X_ASSUM ``!s. _`` [`s`] >>
    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_TF, bir_is_bool_exp_env_REWRS] >>
    Q.EXISTS_TAC `s'` >>
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def]
  )
) >>
irule weak_map_loop_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `\s. bir_eval_exp C1 s.bst_environ = SOME bir_val_true` >>
Q.EXISTS_TAC `\s. b2n (iv2i (THE (bir_eval_exp variant s.bst_environ)))` >>
STRIP_TAC >| [
  GEN_TAC >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
  (* Remove unnecessary assumption *)
  Q.PAT_X_ASSUM `weak_triple a b c d e` (fn thm => ALL_TAC) >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!x. _`` [`n2w x`] >>
  FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* Obtain explicit form for evaluation of variant *)
  subgoal `bir_eval_exp variant s.bst_environ = SOME (BVal_Imm (Imm64 (n2w x)))` >- (
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
    IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
    Q.SUBGOAL_THEN `va = (BVal_Imm (Imm64 (n2w x)))` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
      IMP_RES_TAC (el 5 (CONJUNCTS bir_eval_imm_types)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      RW_TAC std_ss [wordsTheory.n2w_w2n, iv2i_def, bir_immTheory.b2n_def]
    )
  ) >>

  (* Prove precondition of the antecedent judgment *)
  Q.SUBGOAL_THEN `bir_exec_to_labels_triple_precond s
		    (BExp_BinExp BIExp_And C1
		       (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 (n2w x)))))
		    prog /\ bir_exec_to_labels_triple_precond s invariant prog`
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

  (* Prove the postcondition of the goal using the postcondition of the assumption *)
  Q.EXISTS_TAC `s'` >>
  Cases_on `s'.bst_pc.bpc_label <> l` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_exp_TF, bir_val_TF_dist]
  ) >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS)
    [bir_is_bool_exp_env_REWRS,
     bir_etl_wm_def, bir_weak_trs_EQ, GSYM bir_and_equiv] >>
  subgoal `b2n (iv2i (THE (bir_eval_exp variant s'.bst_environ))) < x` >- (
    subgoal `?x'. bir_eval_exp variant s'.bst_environ =
		    SOME (BVal_Imm (Imm64 x'))` >- (
      subgoal `?va. (bir_eval_exp variant s'.bst_environ = SOME va) /\
		     (type_of_bir_val va = (BType_Imm it'))` >- (
	METIS_TAC [type_of_bir_exp_THM_with_init_vars]
      ) >>
      METIS_TAC [bir_eval_imm_types]
    ) >>
    `bir_imm_word_lt (bir_eval_exp variant s'.bst_environ)
		       (bir_eval_exp (BExp_Const (Imm64 (n2w x))) s'.bst_environ)` suffices_by (
       FULL_SIMP_TAC (arith_ss++holBACore_ss++wordsLib.WORD_ss)
	 [bir_imm_word_lt_def, wordsTheory.WORD_LT,
	  iv2i_def, wordsTheory.WORD_LE,
	  bir_val_true_def]
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_slessthan_equiv, bir_imm_word_lt_def, bir_val_true_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_precond_def],

  (* Remove unnecessary assumption *)
  Q.PAT_X_ASSUM `!x. _` (fn thm => ALL_TAC) >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def, weak_triple_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, GSYM bir_and_equiv] >>
  subgoal `bir_is_bool_exp_env ms.bst_environ C1` >- (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def] >>
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET
  ) >>
  IMP_RES_TAC bir_not_equiv >>
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS] >>
  REV_FULL_SIMP_TAC std_ss [bir_eval_exp_TF] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss []
]
);


val bir_map_unsigned_loop_thm = store_thm("bir_map_unsigned_loop_thm",
  ``!prog l wl bl invariant C1 variant post.
    (* Compute in place using proof procedures: *)
    (*   These two needed to use weak_map_loop_thm *)
    (type_of_bir_exp variant = SOME (BType_Imm Bit64)) ==>
    bir_vars_of_exp variant SUBSET bir_vars_of_program prog ==>
    (*   These two needed to prove bir_is_bool_exp_env ms.bst_environ C1 *)
    bir_is_bool_exp C1 ==>
    (bir_vars_of_exp C1) SUBSET (bir_vars_of_program prog) ==>
    (* Extra for weak_map_loop_thm *)
    l NOTIN wl ==>
    l NOTIN bl ==>
    (wl INTER bl = {}) ==>
    (* Obtain bir_loop contract through some rule: *)
    (!x.
     bir_map_triple prog invariant l ({l} UNION wl) bl
       (BExp_BinExp BIExp_And C1
	  (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 x)))
       )
       (\l'.
	    if l' = l then
	      (BExp_BinExp BIExp_And
		 (BExp_BinPred BIExp_LessThan variant
		    (BExp_Const (Imm64 x)))
		 (BExp_BinPred BIExp_LessOrEqual
		    (BExp_Const (Imm64 0w)) variant))
	    else bir_exp_false)
    ) ==>
    bir_map_triple prog bir_exp_true l wl bl
      (BExp_BinExp BIExp_And invariant (BExp_UnaryExp BIExp_Not C1)) post ==>
    bir_map_triple prog bir_exp_true l wl bl
      invariant
      post``,


FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC bir_model_is_weak >>
QSPECL_X_ASSUM ``!prog. _`` [`prog`] >>
(* 1. Use weak_map_loop_thm *)
Q.SUBGOAL_THEN `weak_map_triple (bir_etl_wm prog)
     (\s. bir_exec_to_labels_triple_precond s bir_exp_true prog) l wl bl
     (\s. bir_exec_to_labels_triple_precond s invariant prog)
     (\s'. bir_exec_to_labels_triple_postcond s' post prog) <=>
  weak_map_triple (bir_etl_wm prog)
     (\s. T) l wl bl
     (\s. bir_exec_to_labels_triple_precond s invariant prog)
     (\s'. bir_exec_to_labels_triple_postcond s' post prog)`
  (fn thm => SIMP_TAC std_ss [thm]) >- (
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
  SIMP_TAC std_ss [weak_triple_def] >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    QSPECL_X_ASSUM ``!s. _`` [`s`] >>
    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_TF, bir_is_bool_exp_env_REWRS] >>
    Q.EXISTS_TAC `s'` >>
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def]
  )
) >>
irule weak_map_loop_thm >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `\s. bir_eval_exp C1 s.bst_environ = SOME bir_val_true` >>
Q.EXISTS_TAC `\s. b2n (iv2i (THE (bir_eval_exp variant s.bst_environ)))` >>
STRIP_TAC >| [
  GEN_TAC >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
  (* Remove unnecessary assumption *)
  Q.PAT_X_ASSUM `weak_triple a b c d e` (fn thm => ALL_TAC) >>
  FULL_SIMP_TAC std_ss [weak_triple_def] >>
  SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!x. _`` [`n2w x`] >>
  FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* Obtain explicit form for evaluation of variant *)
  subgoal `bir_eval_exp variant s.bst_environ = SOME (BVal_Imm (Imm64 (n2w x)))` >- (
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
    IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
    Q.SUBGOAL_THEN `va = (BVal_Imm (Imm64 (n2w x)))` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
      IMP_RES_TAC (el 5 (CONJUNCTS bir_eval_imm_types)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      RW_TAC std_ss [wordsTheory.n2w_w2n, iv2i_def, bir_immTheory.b2n_def]
    )
  ) >>

  (* Prove precondition of the antecedent judgment *)
  Q.SUBGOAL_THEN `bir_exec_to_labels_triple_precond s
		    (BExp_BinExp BIExp_And C1
		       (BExp_BinPred BIExp_Equal variant (BExp_Const (Imm64 (n2w x)))))
		    prog /\ bir_exec_to_labels_triple_precond s invariant prog`
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

  (* Prove the postcondition of the goal using the postcondition of the assumption *)
  Q.EXISTS_TAC `s'` >>
  Cases_on `s'.bst_pc.bpc_label <> l` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_exp_TF, bir_val_TF_dist]
  ) >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS)
    [bir_is_bool_exp_env_REWRS,
     bir_etl_wm_def, bir_weak_trs_EQ, GSYM bir_and_equiv] >>
  subgoal `b2n (iv2i (THE (bir_eval_exp variant s'.bst_environ))) < x` >- (
    subgoal `?x'. bir_eval_exp variant s'.bst_environ =
		    SOME (BVal_Imm (Imm64 x'))` >- (
      subgoal `?va. (bir_eval_exp variant s'.bst_environ = SOME va) /\
		     (type_of_bir_val va = (BType_Imm it'))` >- (
	METIS_TAC [type_of_bir_exp_THM_with_init_vars]
      ) >>
      METIS_TAC [bir_eval_imm_types]
    ) >>
    `bir_imm_word_lo (bir_eval_exp variant s'.bst_environ)
		       (bir_eval_exp (BExp_Const (Imm64 (n2w x))) s'.bst_environ)` suffices_by (
       FULL_SIMP_TAC (arith_ss++holBACore_ss)[bir_imm_word_lo_def, wordsTheory.WORD_LO,
                                              wordsTheory.w2n_n2w, iv2i_def]
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lessthan_equiv, bir_imm_word_lo_def, bir_val_true_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_precond_def],

  (* Remove unnecessary assumption *)
  Q.PAT_X_ASSUM `!x. _` (fn thm => ALL_TAC) >>
  FULL_SIMP_TAC std_ss [weak_map_triple_def, weak_triple_def] >>
  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!s. _`` [`ms`] >>
  REV_FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_precond_def, GSYM bir_and_equiv] >>
  subgoal `bir_is_bool_exp_env ms.bst_environ C1` >- (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def] >>
    IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET
  ) >>
  IMP_RES_TAC bir_not_equiv >>
  FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_REWRS] >>
  REV_FULL_SIMP_TAC std_ss [bir_eval_exp_TF] >>
  Q.EXISTS_TAC `s'` >>
  FULL_SIMP_TAC std_ss []
]
);

(* Shrinking the whitelist is possible if the corresponding
 * postcondition never holds. *)
val bir_map_subset_rule_thm =
 store_thm("bir_map_subset_rule_thm",
  ``!prog l ls1 ls2 pre post.
    ls1 <> {} ==>
    (!st. (bir_eval_exp (post st.bst_pc.bpc_label) st.bst_environ = SOME bir_val_true) ==>
          (~(st.bst_pc.bpc_label IN ls2))
    ) ==>
    bir_map_triple prog bir_exp_true l (ls1 UNION ls2) {} pre post ==>
    bir_map_triple prog bir_exp_true l ls1 {} pre post``,

REPEAT STRIP_TAC >>
REV_FULL_SIMP_TAC std_ss [bir_map_triple_def, weak_map_triple_def,
                          weak_triple_def] >>
REPEAT STRIP_TAC >> (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >> (
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  ASSUME_TAC (SPECL [``prog:'a bir_program_t``] bir_model_is_weak) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC weak_union_pc_not_in_thm >>
  QSPECL_X_ASSUM ``!st. _`` [`s''`] >>
  subgoal `bir_eval_exp (post s''.bst_pc.bpc_label) s''.bst_environ =
	    SOME bir_val_true` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_triple_postcond_def]
  ) >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def]
)
);

val bir_map_subset_blacklist_rule_thm =
  store_thm("bir_map_subset_blacklist_rule_thm",
  ``!prog invariant l wl bl bl' pre post.
    bl' SUBSET bl ==>
    bir_map_triple prog invariant l wl bl pre post ==>
    bir_map_triple prog invariant l wl bl' pre post``,

METIS_TAC [bir_map_triple_def, bir_model_is_weak,
           weak_map_subset_blacklist_rule_thm]
);

val bir_exec_to_labels_triple_precond_subprogram =
  store_thm("bir_exec_to_labels_triple_precond_subprogram",
  ``!prog1 prog2 s pre.
    bir_is_subprogram prog1 prog2 ==>
    bir_exec_to_labels_triple_precond s pre prog2 ==>
    bir_exec_to_labels_triple_precond s pre prog1``,

METIS_TAC [bir_exec_to_labels_triple_precond_def,
           bir_env_vars_are_initialised_SUBPROGRAM]
);

val bir_is_valid_pc_exec =
  store_thm("bir_is_valid_pc_exec",
  ``!s pre prog ls l' n n0 s'.
    (bir_exec_to_labels ls prog s = BER_Ended l' n n0 s') ==>
    (* TODO: Why is this assumption required? *)
    bir_exec_to_labels_triple_precond s pre prog ==>
    ~bir_state_is_terminated s' ==>
    bir_is_valid_pc prog s.bst_pc``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def] >>
subgoal `~bir_state_is_terminated s` >- (
  CCONTR_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
                                        bir_exec_steps_GEN_REWR_TERMINATED] >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
IMP_RES_TAC bir_exec_steps_GEN_REWR_STEP >> 
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_def] >>
Cases_on `bir_get_current_statement prog s.bst_pc` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_state_set_failed_def] >>
  subgoal `bir_state_is_terminated (s with bst_status := BST_Failed)` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  IMP_RES_TAC bir_exec_steps_GEN_REWR_TERMINATED >>
  QSPECL_X_ASSUM ``!pc_cond p max_steps. _``
    [`(F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls))`,
     `prog`,
     `(if
	bir_state_COUNT_PC
	  (F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls))
	  (s with bst_status := BST_Failed)
       then
	 OPT_NUM_PRE (SOME 1)
       else SOME 1)`] >>
  (* !!! *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
FULL_SIMP_TAC std_ss [GSYM bir_get_current_statement_IS_SOME]
);

val bir_map_prog_comp_thm =
  store_thm("bir_map_prog_comp_thm",
  ``!prog1 prog2 invariant wl bl l pre post.
    bir_is_subprogram prog1 prog2 ==>
    bir_is_valid_labels prog2 ==>
    bir_map_triple prog1 invariant l wl bl pre post ==>
    bir_map_triple prog2 invariant l wl bl pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def, weak_map_triple_def] >>
FULL_SIMP_TAC (std_ss++bir_wm_SS) [weak_triple_def,
				   bir_etl_wm_def, bir_weak_trs_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!s. _`` [`s`] >>
IMP_RES_TAC bir_exec_to_labels_triple_precond_subprogram >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_exec_to_labels (wl UNION bl) prog1 s` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Q.PAT_X_ASSUM `b = s'` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
subgoal `bir_is_valid_pc prog1 s.bst_pc` >- (
  METIS_TAC [bir_is_valid_pc_exec]
) >>
subgoal `(!l.
	    (s'.bst_status = BST_JumpOutside l) ==>
	    ~MEM l (bir_labels_of_program prog2))` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_precond_def]
) >>
IMP_RES_TAC bir_exec_to_labels_TERMINATES_SUBPROGRAM_EQ >>
Q.EXISTS_TAC `s'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF] >>
CONJ_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_postcond_def,
					bir_exec_to_labels_triple_precond_def] >>
  irule bir_env_oldTheory.bir_env_vars_are_initialised_ORDER >>
  Q.EXISTS_TAC `s.bst_environ` >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
  METIS_TAC [bir_program_env_orderTheory.bir_exec_to_labels_n_ENV_ORDER]
)
);

(* Sketch for alternative proof using weak_map_model_comp_rule_thm
val bir_map_prog_comp_alt_thm =
  store_thm("bir_map_prog_comp_alt_thm",
  ``!prog1 prog2 invariant wl bl l pre post.
    bir_is_subprogram prog1 prog2 ==>
    bir_is_valid_labels prog2 ==>
    bir_map_triple prog1 invariant l wl bl pre post ==>
    bir_map_triple prog2 invariant l wl bl pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_map_triple_def] >>
irule weak_map_model_comp_rule_thm >>
FULL_SIMP_TAC std_ss [bir_model_is_weak] >>
Q.EXISTS_TAC `bir_etl_wm prog1` >>
REPEAT STRIP_TAC >| [
  (* (bir_etl_wm prog1).pc ms = (bir_etl_wm prog2).pc ms *)
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def],

  (* (bir_etl_wm prog2).weak ms ls ms' *)
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [bir_etl_wm_def, bir_weak_trs_def, weak_map_triple_def] >>
  Cases_on `bir_exec_to_labels ls prog2 ms` >> Cases_on `bir_exec_to_labels ls prog1 ms` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    Q.PAT_X_ASSUM `b' = ms'` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    subgoal `bir_is_valid_pc prog1 ms.bst_pc` >- (
      cheat >>
      (* TODO: Why does bir_is_valid_pc_exec require precondition? *)
      METIS_TAC [bir_is_valid_pc_exec]
    ) >>
    subgoal `(!l.
		(ms'.bst_status = BST_JumpOutside l) ==>
		~MEM l (bir_labels_of_program prog2))` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
    ) >>
    IMP_RES_TAC bir_exec_to_labels_TERMINATES_SUBPROGRAM_EQ >>
    (* This should work out... *)
    cheat
  ),

  FULL_SIMP_TAC std_ss [bir_model_is_weak],

  FULL_SIMP_TAC std_ss [weak_map_triple_def] >>
  FULL_SIMP_TAC (std_ss++bir_wm_SS) [weak_triple_def,
				     bir_etl_wm_def, bir_weak_trs_def] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC bir_exec_to_labels_triple_precond_subprogram >>
  QSPECL_X_ASSUM ``!s. _`` [`s`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_triple_postcond_def,
					bir_exec_to_labels_triple_precond_def] >>
  irule bir_env_oldTheory.bir_env_vars_are_initialised_ORDER >>
  Q.EXISTS_TAC `s.bst_environ` >>
  Cases_on `bir_exec_to_labels (wl UNION bl) prog1 s` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
  METIS_TAC [bir_program_env_orderTheory.bir_exec_to_labels_n_ENV_ORDER]
]
);
*)

val _ = export_theory();
