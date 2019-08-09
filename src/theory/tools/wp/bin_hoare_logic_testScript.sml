open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;

open bin_hoare_logicLib;

open HolBACoreSimps;

val _ = new_theory "bin_hoare_logic_test";

(* TODO: Check usage of "bir_exec_block_n_block_ls_running" *)
(* Cheats in:

bir_exec_to_labels_n_ended_not_running

*)

(******************************************************************)
(*                         DEFINITIONS                            *)
(******************************************************************)

val bir_trs_def = Define `
  bir_trs (prog:'a bir_program_t) ms =
  let
    (_, _, _, st) = bir_exec_block_n prog ms 1
  in
   if st.bst_status = BST_Running
   then SOME st
   else NONE
`;

val bir_weak_trs_def = Define `
  bir_weak_trs ls prog ms =
    case (bir_exec_to_labels ls prog ms) of
      BER_Ended _ _ _ bir_state =>
        if bir_state.bst_status = BST_Running
        then SOME bir_state
        else NONE
    | BER_Looping _ => NONE
`;

(* 1. Instantiate a new weak model *)
val bir_etl_wm_def =
  Define `bir_etl_wm (prog :'a bir_program_t) = <|
    trs  := bir_trs prog;
    weak := (\ms ls ms'.
	       (bir_weak_trs ls prog ms = SOME ms')
	    );
    pc   := (\ms. ms.bst_pc.bpc_label)
  |>`;

val wm_type = mk_thy_type {Tyop="bin_model_t",
                           Thy="bin_hoare_logic",
                           Args=[``:bir_state_t``,
                                 ``:bir_label_t``]
                          };

val bir_wm_SS = rewrites (flatten (map type_rws [wm_type]));

(******************************************************************)
(*                            LEMMATA                             *)
(******************************************************************)

(* TODO: Convenient? Currently only used once... Please decide if
 * this is useful... *)
val NUM_LSONE_EQZ =
  store_thm("NUM_LSONE_EQZ",
  ``!(n:num). (n < 1) <=> (n = 0)``,

FULL_SIMP_TAC arith_ss []
);

(* TODO: Move elsewhere... *)
val bir_exec_block_n_EXISTS_prev =
  store_thm("bir_exec_block_n_EXISTS_prev",
  ``!prog ms m m' l n c_l' ms'.
      (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
      1 <= m ==>
      m' < m ==>
      ?l' n' c_l'' ms''.
        bir_exec_block_n prog ms m' = (l', n', c_l'', ms'')``,

REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated ms` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_TERMINATED]
) >>
Induct_on `m'` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC arith_ss [] >>

SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                 bir_exec_steps_GEN_def, LET_DEF] >>
Cases_on `bir_exec_infinite_steps_COUNT_STEPS (F,(\pc. pc.bpc_index = 0))
            (SOME (SUC m')) prog ms` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
  QSPECL_X_ASSUM ``!(i:num). _`` [`n`] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                        bir_exec_steps_GEN_def, LET_DEF] >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS
              (F,(\pc. pc.bpc_index = 0))
              (SOME m) prog ms` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  Q.PAT_X_ASSUM `x = n` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  FULL_SIMP_TAC std_ss
                [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >- (
    QSPECL_X_ASSUM
      ``!n. ~bir_state_is_terminated
            (bir_exec_infinite_steps_fun prog ms n)`` [`n`] >>
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

(* TODO: Not currently used, but still nice to have.
 *       Move elsewhere... *)
val bir_get_current_statement_NONE_stmt =
  store_thm("bir_get_current_statement_NONE_stmt",
  ``!prog pc.
      (bir_get_current_statement prog pc = NONE) ==>
      (bir_get_current_block prog pc = NONE)
    ``,

FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_get_current_block_def,
               bir_get_current_statement_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_get_program_block_info_by_label
            prog pc.bpc_label` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >>
Cases_on `0 = LENGTH r.bb_statements` >>
Cases_on `0 < LENGTH r.bb_statements` >> (
FULL_SIMP_TAC arith_ss []
)
);

val bir_exec_block_Z =
  store_thm("bir_exec_block_Z",
  ``!prog ms m l n c_l' ms'.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (n = 0) ==>
    (ms' = ms)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended,
                      bir_exec_infinite_steps_fun_REWRS]
);

val bir_exec_block_n_block_nz_init_running =
  store_thm("bir_exec_block_n_block_nz_init_running",
  ``!prog ms m l n c_l' ms'.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (0 < m) ==>
    (ms.bst_status = BST_Running) ==>
    0 < n``,

REPEAT STRIP_TAC >>
Cases_on `n <> 0` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC arith_ss [] >>
IMP_RES_TAC bir_exec_block_Z >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
FULL_SIMP_TAC (arith_ss++holBACore_ss)
              [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF]
);

val bir_exec_block_n_block_nz_final_running =
  store_thm("bir_exec_block_n_block_nz_final_running",
  ``!prog ms m l n c_l' ms'.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (0 < m) ==>
    (ms'.bst_status = BST_Running) ==>
    (ms'.bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
Cases_on `c_l' < m` >- (
  FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
) >>
subgoal `c_l' = m` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
	      [bir_state_COUNT_PC_def]
);

val bir_exec_block_n_block_nz_final_running =
  store_thm("bir_exec_block_n_block_nz_final_running",
  ``!prog ms m l n c_l' ms'.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (0 < m) ==>
    (ms'.bst_status = BST_Running) ==>
    (ms'.bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
Cases_on `c_l' < m` >- (
  FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
) >>
subgoal `c_l' = m` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
	      [bir_state_COUNT_PC_def]
);

val bir_exec_block_n_running =
  store_thm("bir_exec_block_n_running",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (ms'.bst_status = BST_Running) ==>
    (ms.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
Cases_on `n = 0` >- (
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
subgoal `n > 0` >- (
  FULL_SIMP_TAC arith_ss []
) >>
QSPECL_X_ASSUM ``!n'.
             n' < n ==>
             ~bir_state_is_terminated
               (bir_exec_infinite_steps_fun prog ms n')``
               [`0`] >>
  REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def,
                              bir_exec_infinite_steps_fun_REWRS]
);

val bir_exec_block_n_step_ls =
  store_thm("bir_exec_block_n_step_ls",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' < n) ==>
    m' < m``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
QSPECL_X_ASSUM ``!n'.
             n' < n ==>
             bir_exec_infinite_steps_fun_COUNT_PCs
               (F,(\pc. pc.bpc_index = 0)) prog ms n' < m``
               [`n'`] >>
QSPECL_X_ASSUM ``!n'.
             n' < n ==>
             ~bir_state_is_terminated
               (bir_exec_infinite_steps_fun prog ms n')``
               [`n'`] >>
PAT_ASSUM ``(n':num) < n``
          (fn  thm => FULL_SIMP_TAC arith_ss [thm])
);

val bir_exec_block_n_block_ls =
  store_thm("bir_exec_block_n_block_ls",
  ``!prog ms l l' n n' c_l' c_l'' ms' m m' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (m' < m) ==>
    ~(n < n')``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_ls >>
FULL_SIMP_TAC arith_ss []
);

val bir_exec_block_n_step_ls_running =
  store_thm("bir_exec_block_n_step_ls_running",
  ``!prog ms l l' n n' c_l' c_l'' ms' m m' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' < n) ==>
    (ms'.bst_status = BST_Running) ==>
    (ms''.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_steps_GEN_SOME_EQ_Ended] >>
QSPECL_X_ASSUM ``!n'.
    n' < n ==>
    ~bir_state_is_terminated
      (bir_exec_infinite_steps_fun prog ms n')`` [`n'`] >>
REV_FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
);

val bir_exec_block_n_step_eq =
  store_thm("bir_exec_block_n_step_eq",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' = n) ==>
    (ms' = ms'')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_steps_GEN_SOME_EQ_Ended]
);

(* TODO *)
val bir_exec_block_n_not_running_block_gt =
  store_thm("bir_exec_block_n_not_running_block_gt",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (ms'.bst_status <> BST_Running) ==>
    (m' > m) ==>
    (ms' = ms'')``,

REPEAT STRIP_TAC >>
subgoal `~(n' < n)` >- (
  IMP_RES_TAC bir_exec_block_n_block_ls >>
  REV_FULL_SIMP_TAC arith_ss []
) >>
Cases_on `n' = n` >- (
  METIS_TAC [bir_exec_block_n_step_eq]
) >>
subgoal `n' > n` >- (
  FULL_SIMP_TAC arith_ss []
) >>
subgoal `!n.
         n < n' ==>
         ~bir_state_is_terminated
           (bir_exec_infinite_steps_fun prog ms n)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                        bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
subgoal `ms' = bir_exec_infinite_steps_fun prog ms n` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                        bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
QSPECL_X_ASSUM ``!n. _`` [`n`] >>
REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def] >>
FULL_SIMP_TAC std_ss []
);

val bir_exec_block_n_step_eq_running =
  store_thm("bir_exec_block_n_step_eq_running",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' = n) ==>
    (* Note: arbitrary choice between ms' and ms'' Running. *)
    (ms'.bst_status = BST_Running) ==>
    (m' = m)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_eq >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_steps_GEN_SOME_EQ_Ended] >>
Cases_on `c_l' < m` >- (
  METIS_TAC [bir_state_is_terminated_def]
) >>
Cases_on `c_l'' < m'` >- (
  METIS_TAC [bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC arith_ss []
);

val bir_exec_block_n_block_ls_running_running =
  store_thm("bir_exec_block_n_block_ls_running_running",
  ``!prog ms l l' n n' c_l' c_l'' ms' m m' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (m' < m) ==>
    (ms'.bst_status = BST_Running) ==>
    (ms''.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
Cases_on `n' = n` >- (
  IMP_RES_TAC bir_exec_block_n_step_eq_running >>
  FULL_SIMP_TAC arith_ss []
) >>
Cases_on `n < n'` >- (
  METIS_TAC [bir_exec_block_n_block_ls]
) >>
subgoal `n' < n` >- (
  FULL_SIMP_TAC arith_ss []
) >>
IMP_RES_TAC bir_exec_block_n_step_ls_running
);

val bir_exec_block_n_step_eq_block_ls_not_running =
  store_thm("bir_exec_block_n_step_eq_block_ls_not_running",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' = n) ==>
    (m' < m) ==>
    (ms''.bst_status <> BST_Running)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_eq >>
Q.PAT_X_ASSUM `ms' = ms''` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
IMP_RES_TAC bir_exec_block_n_step_eq_running >>
FULL_SIMP_TAC arith_ss []
);

val bir_exec_block_n_block_ls_running_step_ls =
  store_thm("bir_exec_block_n_block_ls_running_step_ls",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (m' < m) ==>
    (ms''.bst_status = BST_Running) ==>
    n' < n``,

REPEAT STRIP_TAC >>
Cases_on `n' = n` >- (
  IMP_RES_TAC bir_exec_block_n_step_eq_block_ls_not_running
) >>
Cases_on `n < n'` >- (
  IMP_RES_TAC bir_exec_block_n_block_ls
) >>
FULL_SIMP_TAC arith_ss []
);

val bir_exec_block_n_inter =
  store_thm("bir_exec_block_n_inter",
  ``!prog ms m (l':'a list) l''' n n'' c_l' c_l''' ms' ms''.
    (bir_exec_block_n prog ms (SUC m) = (l''', n'', c_l''', ms'')) ==>
    (bir_exec_block_n prog ms 1 = (l',n,c_l',ms')) ==>
    (m > 0) ==>
    ?l'' n'' c_l''.
    (bir_exec_block_n prog ms' m = (l'',n'',c_l'',ms''))``,


REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [arithmeticTheory.ADD1] >>
Q.PAT_X_ASSUM
  `bir_exec_block_n prog ms (m + 1) = (l''',n'',c_l''',ms'')`
  (fn thm =>
    (subgoal `bir_exec_block_n prog ms (1 + m) =
                (l''',n'',c_l''',ms'')`
             >- (FULL_SIMP_TAC arith_ss [thm])
    )
  ) >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add] >>
REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `bir_exec_block_n prog ms' m` >> Cases_on `r` >>
  Cases_on `r'` >>
FULL_SIMP_TAC std_ss []
);

(*****************************************)
(* bir_exec_block_n + FUNPOW_OPT bir_trs *)

(* TODO: Used 4 times. Correct for additional antecedent *)
val bir_exec_block_n_to_FUNPOW_OPT_bir_trs =
  store_thm("bir_exec_block_n_to_FUNPOW_OPT_bir_trs",
  ``!prog ms m l n c_l' ms'.
      (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
      (ms'.bst_status = BST_Running) ==>
      (FUNPOW_OPT (bir_trs prog) m ms = SOME ms')``,

Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
(* 1. Deal with case m = 0. *)
Cases_on `m = 0` >- (
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
  Cases_on `bir_trs prog ms''` >- (
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
subgoal `?l' n' c_l'' ms''.
           bir_exec_block_n prog ms 1 = (l',n',c_l'',ms'')` >- (
  IMP_RES_TAC bir_exec_block_n_EXISTS_prev >>
  FULL_SIMP_TAC arith_ss []
) >>
(* 2. Describe case #blocks=m *)
subgoal `?l' n' c_l'' ms''.
           bir_exec_block_n prog ms m = (l',n',c_l'',ms'')` >- (
  IMP_RES_TAC bir_exec_block_n_EXISTS_prev >>
  FULL_SIMP_TAC arith_ss []
) >>
(* 3. Obtain execution from intermediate state *)
IMP_RES_TAC bir_exec_block_n_inter >>
(* 3. Instantiate universal quantifiers in induction hypothesis *)
QSPECL_X_ASSUM
  ``!prog. _`` [`prog`, `ms''`, `l'''`, `n'''`, `c_l''''`, `ms'`] >>
FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
subgoal `bir_trs prog ms = SOME ms''` >- (
  FULL_SIMP_TAC std_ss [bir_trs_def, LET_DEF] >>
  IMP_RES_TAC bir_exec_block_n_block_ls_running_running >>
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC std_ss []
);

(* TODO: Used 5 times. *)
val FUNPOW_OPT_bir_trs_to_bir_exec_block_n =
  store_thm("FUNPOW_OPT_bir_trs_to_bir_exec_block_n",
  ``!prog ms m ms'.
      (FUNPOW_OPT (bir_trs prog) m ms = SOME ms') ==>
      ?l n c_l'.
      (bir_exec_block_n prog ms m = (l,n,c_l',ms'))``,

Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
Cases_on `bir_trs prog ms` >- (
  FULL_SIMP_TAC std_ss []
) >>
QSPECL_X_ASSUM
  ``!prog. _`` [`prog`, `x`, `ms'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.ADD1] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add, bir_trs_def, LET_DEF] >>
Cases_on `x.bst_status = BST_Running` >> (
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `bir_exec_block_n prog ms 1` >> Cases_on `r` >>
  Cases_on `r'` >>
  FULL_SIMP_TAC std_ss [LET_DEF]
)
);

val FUNPOW_OPT_bir_trs_running =
  store_thm("FUNPOW_OPT_bir_trs_running",
  ``!prog ms m ms'.
      (FUNPOW_OPT (bir_trs prog) m ms = SOME ms') ==>
      (ms.bst_status = BST_Running) ==>
      (ms'.bst_status = BST_Running)``,

Induct_on `m` >> (
  REV_FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_trs_def, LET_DEF] >>
Cases_on `bir_exec_block_n prog ms 1` >> Cases_on `r` >>
Cases_on `r'` >>
FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `r.bst_status = BST_Running` >> (
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC []
)
);


(************************)
(* bir_exec_to_labels_n *)

val bir_exec_to_labels_n_ended_running =
  store_thm("bir_exec_to_labels_n_ended_running",
  ``!ls prog ms l n c_l' ms'.
    (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n c_l' ms') ==>
    (ms'.bst_status = BST_Running) ==>
    ((ms'.bst_pc.bpc_index = 0) /\ ms'.bst_pc.bpc_label IN ls)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >> (
  Cases_on `c_l' < 1` >- (
    FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
  ) >>
  subgoal `c_l' = 1` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_COUNT_PC_def]
)
);

val test_lemma = store_thm("test_lemma",
  ``!prog ms n ls.
    (~bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog ms n)) ==>
    ((bir_exec_infinite_steps_fun prog ms n).bst_pc.bpc_label
       NOTIN ls) ==>
    (bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog ms (SUC n))) ==>
    ((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc.bpc_label
       NOTIN ls)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
Cases_on `ms` >>
FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_SUC,
                      bir_exec_step_state_def, bir_exec_step_def] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_get_current_statement prog
            (FUNPOW (bir_exec_step_state prog) n ms).bst_pc` >- (
  Cases_on `ms` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_set_failed_def, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >| [
  (* BStmt *)
(*
  bir_exec_stmtB_state_def

*)
  FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >>
  Cases_on `b` >| [
    cheat,

    FULL_SIMP_TAC std_ss [bir_exec_stmtB_def, bir_exec_stmt_assign_def] >>

  ]

  (* EStmt *)
]
);

val bir_exec_to_labels_n_ended_not_running =
  store_thm("bir_exec_to_labels_n_ended_not_running",
  ``!ls prog ms l n c_l' ms'.
    (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n c_l' ms') ==>
    (ms'.bst_status <> BST_Running) ==>
    (ms'.bst_pc.bpc_label NOTIN ls)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
(* TODO: Missing antecedent? *)
subgoal `(ms.bst_pc.bpc_label NOTIN ls)` >- (
  cheat
) >>
(* Case: Ended reached by PC count. *)
Cases_on `c_l' = 1` >- (
  FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def] >>
  Cases_on `(bir_exec_infinite_steps_fun prog ms n).bst_status` >| [
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    (* TODO: Case: JumpOutside *)
    (* If jumped outside, then PC label is equal to previous one,
     * from n-1 steps. But this can't have been in ls, or we would
     * have reached Ended before doing so through JumpOutside. *)
    (* This would necessitate lengthy reasoning about all the
     * possible things that could happen from n-1 steps... *)
(*
(~bir_state_is_terminated
   (bir_exec_infinite_steps_fun prog ms n)) ==>
((bir_exec_infinite_steps_fun prog ms n).bst_pc_pc_label
   NOTIN ls) ==>
(bir_state_is_terminated
   (bir_exec_infinite_steps_fun prog ms (SUC n))) ==>
((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc_pc_label
   NOTIN ls)
*)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    cheat
  ]
) >>
subgoal `c_l' = 0` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
Cases_on `n = 0` >- (
  subgoal `ms = ms'` >- (
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
  ) >>
  FULL_SIMP_TAC std_ss []
) >>
subgoal `0 < n` >- (
 FULL_SIMP_TAC arith_ss []
) >>
QSPECL_X_ASSUM ``!j.
     j < n ==>
     ~bir_state_COUNT_PC
       (F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls))
       (bir_exec_infinite_steps_fun prog ms (SUC j))`` [`PRE n`] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.SUC_PRE] >>
REV_FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def] >>
subgoal `PRE n < n` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC arith_ss [] >>
Cases_on `(bir_exec_infinite_steps_fun prog ms n).bst_status` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    (* TODO: Separate lemma for this... *)
    (* Since termination can never happen immediately after a
     * change of pc label, and we know that for n-1 steps pc label
     * is not in ls, then for n steps pc label cannot be in ls. *)
(*
(~bir_state_is_terminated
   (bir_exec_infinite_steps_fun prog ms n)) ==>
((bir_exec_infinite_steps_fun prog ms n).bst_pc_pc_label
   NOTIN ls) ==>
(bir_state_is_terminated
   (bir_exec_infinite_steps_fun prog ms (SUC n))) ==>
((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc_pc_label
   NOTIN ls)
*)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    cheat,

    (* TODO: Separate lemma for this... *)
    (* Since termination can never happen immediately after a
     * change of pc label, and we know that for n-1 steps pc label
     * is not in ls, then for n steps pc label cannot be in ls. *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    cheat,

    (* TODO: Separate lemma for this... *)
    (* Since termination can never happen immediately after a
     * change of pc label, and we know that for n-1 steps pc label
     * is not in ls, then for n steps pc label cannot be in ls. *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    cheat,

    (* TODO: Separate lemma for this... *)
    (* Since termination can never happen immediately after a
     * change of pc label, and we know that for n-1 steps pc label
     * is not in ls, then for n steps pc label cannot be in ls. *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    cheat,

    (* TODO: Separate lemma for this... *)
    (* Since termination can never happen immediately after a
     * change of pc label, and we know that for n-1 steps pc label
     * is not in ls, then for n steps pc label cannot be in ls. *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >> (
      cheat
    )
]
);

(*******************************************)
(* bir_exec_to_labels_n + bir_exec_block_n *)

(* TODO: Try to phrase as much as possible only in terms of
 * bir_exec_block_n... *)

val bir_exec_to_labels_n_block_n_eq =
  store_thm("bir_exec_to_labels_n_block_n_eq",
  ``!ls prog ms l l' n c_l' c_l'' ms' m ms''.
    (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n c_l' ms') ==>
    (bir_exec_block_n prog ms m = (l',n,c_l'',ms'')) ==>
    (ms' = ms'')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
		      bir_exec_block_n_TO_steps_GEN,
                      bir_exec_steps_GEN_SOME_EQ_Ended]
);

val bir_exec_to_labels_n_block_n_ls_running =
  store_thm("bir_exec_to_labels_n_block_n_ls_running",
  ``!ls prog ms l l' n n' c_l' n0 ms' m' ms''.
    (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n n0 ms') ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l',ms'')) ==>
    (n' < n) ==>
    (ms''.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
subgoal `!n'.
             n' < n ==>
             ~bir_state_is_terminated
               (bir_exec_infinite_steps_fun prog ms n')` >- (
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `ms'' = bir_exec_infinite_steps_fun prog ms n'` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
			bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
);

val bir_exec_to_labels_n_block_n_notin_ls =
  store_thm("bir_exec_to_labels_n_block_n_notin_ls",
  ``!ls prog ms l l' n n' n0 c_l' c_l'' m m' ms' ms''.
  (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n n0 ms') ==>
  (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
(* TODO: Can choose the below three: *)
  (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
  (m' < m) ==>
  (0 < m') ==>
(* Or these: *)
(*
  (n' < n) ==>
  (0 < n') ==>
*)
(* Which is more elegant? *)
  (ms''.bst_status = BST_Running) ==>
  ms''.bst_pc.bpc_label NOTIN ls``,

REPEAT STRIP_TAC >>
subgoal `n' < n` >- (
  METIS_TAC [bir_exec_block_n_block_ls_running_step_ls]
) >>
subgoal `ms.bst_status = BST_Running` >- (
  METIS_TAC [bir_exec_block_n_running]
) >>
subgoal `0 < n'` >- (
  IMP_RES_TAC bir_exec_block_n_block_nz_init_running >>
  REV_FULL_SIMP_TAC arith_ss []
) >>
subgoal
  `!n'.
     n' < n ==>
     bir_exec_infinite_steps_fun_COUNT_PCs
       (F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN ls))
       prog ms n' < 1` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
REV_FULL_SIMP_TAC std_ss [NUM_LSONE_EQZ] >>
FULL_SIMP_TAC std_ss
  [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
REV_FULL_SIMP_TAC arith_ss [] >>
QSPECL_X_ASSUM ``!(j:num). _`` [`PRE n'`] >>
REV_FULL_SIMP_TAC arith_ss [arithmeticTheory.SUC_PRE,
			    bir_state_COUNT_PC_def] >>
subgoal `bir_exec_infinite_steps_fun prog ms n' = ms''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
			bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
METIS_TAC [arithmeticTheory.SUC_PRE,
           bir_exec_block_n_block_nz_final_running]
);


(* 2. Prove that weak_model bir_etl_wm *)
val bir_model_is_weak = store_thm("bir_model_is_weak",
  ``!(prog: 'a bir_program_t).
      weak_model (bir_etl_wm prog)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [weak_model_def, bir_etl_wm_def] >>
FULL_SIMP_TAC std_ss [bir_weak_trs_def, LET_DEF] >>
REPEAT STRIP_TAC >>
CASE_TAC >| [
  (* Case 1: Result of bir_exec_to_labels is Ended *)
  CASE_TAC >| [
    (* Case 1A: Ended + Final state has status Running *)
    (* TODO: Move this to before CASE... *)
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
    IMP_RES_TAC bir_exec_to_labels_n_ended_running >>
    (* TODO: Add more common stuff here... *)
    EQ_TAC >| [
      (* Case 1AI: Assuming b = ms', show bir_trs plays nice *)
      (* First part is just removing trivial stuff in goal... *)
      REPEAT DISCH_TAC >>
      (* subsume b... *)
      Q.PAT_X_ASSUM `b = ms'`
                    (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      EXISTS_TAC ``m:num`` >>
      FULL_SIMP_TAC arith_ss [] >>
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      REPEAT STRIP_TAC >>
      rename1 `m' < m` >>
      IMP_RES_TAC (Q.SPECL [`prog`, `ms`, `m`, `m'`]
                           bir_exec_block_n_EXISTS_prev) >>
      rename1 `bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')` >>
      Q.EXISTS_TAC `ms''` >>
      subgoal `ms''.bst_status = BST_Running` >- (
	IMP_RES_TAC bir_exec_block_n_block_ls_running_running
      ) >>
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      (* Use bir_exec_to_labels_n_block_n_notin_ls *)
      IMP_RES_TAC bir_exec_to_labels_n_block_n_notin_ls >>
      FULL_SIMP_TAC arith_ss [],

      (* Case 1AII: Assuming bir_trs plays nice, show that
       * b = ms' *)
      REPEAT STRIP_TAC >>
      IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
      rename1 `bir_exec_block_n prog ms m' = (l',n'',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog ms m' = (l',n',c_l'',ms')` >>
      (* Here, n < n' as well as n' < n leads to contradiction, so
       * only remaining posssibility is n = n', which proves the
       * goal. *)
      Cases_on `n' < n` >- (
        (* This would mean that ms' does not have PC with label in
         * ls and pointing to instruction 0, which is a
         * contradiction. *)
        (* Step 1: Prove m' < m *)
	subgoal `m' < m` >- (
	  METIS_TAC [bir_exec_block_n_step_ls]
	) >>
        (* Step 2: Prove ms'.bst_status = BST_Running *)
        subgoal `ms'.bst_status = BST_Running` >- (
          IMP_RES_TAC bir_exec_block_n_step_ls_running
        ) >>
        (* Step 3: Use bir_exec_to_labels_n_block_n_notin_ls *)
        IMP_RES_TAC bir_exec_to_labels_n_block_n_notin_ls >>
        REV_FULL_SIMP_TAC arith_ss []
      ) >>
      Cases_on `n < n'` >- (
        (* Slightly more complex case: This would mean that state b
         * has crossed less that m' blocks. This would mean,
         * together with init assumption, that PC label of b is not
         * in ls (with bir_exec_block_n_to_FUNPOW_OPT_bir_trs) *)
        subgoal `m < m'` >- (
          IMP_RES_TAC bir_exec_block_n_step_ls
        ) >>
        (* Use initial assumption *)
        QSPECL_X_ASSUM ``!n'.
             n' < m' /\ n' > 0 ==>
             ?ms''.
                 (FUNPOW_OPT (bir_trs prog) n' ms = SOME ms'') /\
                 ms''.bst_pc.bpc_label NOTIN ls``
             [`m`] >>
        REV_FULL_SIMP_TAC arith_ss [] >>
        IMP_RES_TAC bir_exec_to_labels_n_ended_running >>
        IMP_RES_TAC bir_exec_block_n_to_FUNPOW_OPT_bir_trs >>
        REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
        FULL_SIMP_TAC (std_ss++holBACore_ss) [] 
      ) >>
      (* Since ~(n < n') and ~(n' < n), n = n' ... *)
      subgoal `n = n'` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      subgoal `m = m'` >- (
        subgoal `ms'.bst_status = BST_Running` >- (
	  IMP_RES_TAC bir_exec_block_n_step_eq >>
	  REV_FULL_SIMP_TAC arith_ss []
        ) >>
        IMP_RES_TAC bir_exec_block_n_step_eq_running
      ) >>
      FULL_SIMP_TAC arith_ss []
    ],

    (* Case 1B: Ended + b is not Running. *)
    FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
    REPEAT STRIP_TAC >>
    rename1 `FUNPOW_OPT (bir_trs prog) n' ms = SOME ms''` >>
    Cases_on `~(n' > 0)` >- (
      FULL_SIMP_TAC std_ss []
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    rename1 `m' > 0` >>
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
    rename1 `bir_exec_block_n prog ms m = (l,n,c_l',ms')` >>
    Cases_on `m' < m` >| [
      DISJ1_TAC >>
      REPEAT STRIP_TAC >>
      IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
      IMP_RES_TAC bir_exec_to_labels_n_ended_not_running >>
      Cases_on `n' = n` >- (
        subgoal `ms'' = ms'` >- (
          IMP_RES_TAC bir_exec_block_n_step_eq >>
          FULL_SIMP_TAC std_ss []
        ) >>
        FULL_SIMP_TAC std_ss []
      ) >>
      subgoal `n' < n` >- (
	IMP_RES_TAC bir_exec_block_n_block_ls >>
	FULL_SIMP_TAC arith_ss []
      ) >>
      subgoal `ms''.bst_status = BST_Running` >- (
	METIS_TAC [bir_exec_to_labels_n_block_n_ls_running]
      ) >>
      IMP_RES_TAC bir_exec_to_labels_n_block_n_notin_ls >>
      REV_FULL_SIMP_TAC arith_ss [],

      Cases_on `m' = m` >- (
        DISJ1_TAC >>
        REPEAT STRIP_TAC >>
        IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
        subgoal `ms'.bst_pc.bpc_label NOTIN ls` >- (
	  IMP_RES_TAC bir_exec_to_labels_n_ended_not_running
        ) >>
        subgoal `n' = n` >- (
          REV_FULL_SIMP_TAC std_ss []
        ) >>
        METIS_TAC [bir_exec_to_labels_n_block_n_eq]
      ) >>
      subgoal `m' > m` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      DISJ1_TAC >>
      REPEAT STRIP_TAC >>
      IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
      IMP_RES_TAC bir_exec_to_labels_n_ended_not_running >>
      IMP_RES_TAC bir_exec_block_n_not_running_block_gt >>
      FULL_SIMP_TAC std_ss []
    ]
  ],

  (* Case 2: Result of bir_exec_to_labels is Looping *)
  FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
  REPEAT STRIP_TAC >>
  Cases_on `~(n > 0)` >- (
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
			bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_1_EQ_Looping] >>
  rename1 `m > 0` >>
  DISJ1_TAC >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
  rename1 `bir_exec_block_n prog ms m = (l',n,c_l',ms')` >>
  QSPECL_X_ASSUM ``!(n:num). (0 < n) ==> _`` [`n`] >>
  (* Since m is larger than zero, n has to be as well...
   * if ms is Running *)
  subgoal `ms.bst_status = BST_Running` >- (
    QSPECL_X_ASSUM ``!(n:num). _`` [`0`] >>
    FULL_SIMP_TAC std_ss [bir_state_is_terminated_def,
                          bir_exec_infinite_steps_fun_REWRS]
  ) >>
  subgoal `0 < n` >- (
    IMP_RES_TAC bir_exec_block_n_block_nz_init_running >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC arith_ss [bir_state_COUNT_PC_def] >>
  QSPECL_X_ASSUM ``!(n:num). _`` [`n`] >>
  subgoal `bir_exec_infinite_steps_fun prog ms n = ms'` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
			  bir_exec_steps_GEN_SOME_EQ_Ended]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
		[bir_state_is_terminated_def] >| [
    IMP_RES_TAC bir_exec_block_n_block_nz_final_running >>
    REV_FULL_SIMP_TAC arith_ss [],

    IMP_RES_TAC bir_exec_block_n_to_FUNPOW_OPT_bir_trs >>
    FULL_SIMP_TAC std_ss [] >>
    Cases_on `ms'' = ms'` >> (
      FULL_SIMP_TAC std_ss []
    )
  ]
]
);

(* These could be useful: *)
(* bir_exec_steps_GEN_SOME_EQ_Ended *)
(* bir_exec_steps_GEN_EQ_Ended *)
(* bir_exec_steps_GEN_change_cond_Ended_SOME *)
(* bir_exec_steps_GEN_1_EQ_Ended *)
(* bir_exec_to_labels_n_TO_bir_exec_block_n *)
(* bir_exec_block_n_TO_steps_GEN *)

val _ = export_theory();
