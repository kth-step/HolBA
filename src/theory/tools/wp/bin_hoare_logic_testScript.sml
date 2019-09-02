open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;

open bin_hoare_logicLib;

open bin_hoare_logicSimps;
open HolBACoreSimps;

val _ = new_theory "bin_hoare_logic_test";

(* TODO: Check usage of "bir_exec_block_n_block_ls_running" *)
(* TODO: Use bir_exec_block_n_EQ_THM where appropriate *)
(* TODO: Use bir_state_is_terminated where appropriate *)

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

(******************************************************************)
(*                            LEMMATA                             *)
(******************************************************************)

(* TODO: Replace this with subgoal using arith_ss *)
val NUM_LSONE_EQZ =
  store_thm("NUM_LSONE_EQZ",
  ``!(n:num). (n < 1) <=> (n = 0)``,

FULL_SIMP_TAC arith_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
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
Cases_on
  `bir_exec_infinite_steps_COUNT_STEPS (F,(\pc. pc.bpc_index = 0))
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

(* TODO: Move to bir_program_blocksTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_0_steps =
  store_thm("bir_exec_block_n_0_steps",
  ``!prog ms m l n c_l' ms'.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (n = 0) ==>
    (ms' = ms)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended,
                      bir_exec_infinite_steps_fun_REWRS]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
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
IMP_RES_TAC bir_exec_block_n_0_steps >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
FULL_SIMP_TAC (arith_ss++holBACore_ss)
              [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_not_running_block_ge =
  store_thm("bir_exec_block_n_not_running_block_ge",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (ms'.bst_status <> BST_Running) ==>
    (m' >= m) ==>
    (ms' = ms'')``,

REPEAT STRIP_TAC >>
Cases_on `m' = m` >- (
  FULL_SIMP_TAC std_ss []
) >>
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_eq_running =
  store_thm("bir_exec_block_n_step_eq_running",
  ``!prog ms m m' l n c_l' ms' l' n' c_l'' ms''.
    (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
    (n' = n) ==>
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_inter =
  store_thm("bir_exec_block_n_inter",
  ``!prog ms m (l':'a list) l''' n n'' c_l' c_l''' ms' ms''.
    (bir_exec_block_n prog ms (SUC m) =
       (l''', n'', c_l''', ms'')) ==>
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

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_eq_block_gt =
  store_thm("bir_exec_block_n_step_eq_block_gt",
  ``!prog ms m m' l' n' c_l' ms' l'' n'' c_l'' ms'' l''' n'''
    c_l''' ms'''.
    (bir_exec_block_n prog ms (SUC m) = (l',n',c_l',ms')) ==>
    (bir_exec_block_n prog ms m' = (l'',n'',c_l'',ms'')) ==>
    (bir_exec_block_n prog ms m = (l''',n''',c_l''',ms''')) ==>
    (ms'.bst_status <> BST_Running) ==>
    (ms'''.bst_status = BST_Running) ==>
    (n'' = n') ==>
    (m' >= SUC m)``,

REPEAT STRIP_TAC >>
Cases_on `n'' = n'''` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_exec_block_n_TO_steps_GEN,
     bir_exec_steps_GEN_SOME_EQ_Ended] >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `n'' < n'''` >- (
  subgoal `!n.
	   n < n''' ==>
	   ~bir_state_is_terminated
	     (bir_exec_infinite_steps_fun prog ms n)` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
			  bir_exec_steps_GEN_SOME_EQ_Ended]
  ) >>
  QSPECL_X_ASSUM ``!n. _`` [`n''`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_is_terminated_def, bir_exec_block_n_TO_steps_GEN,
     bir_exec_steps_GEN_SOME_EQ_Ended] >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
subgoal `n''' < n''` >- (
  FULL_SIMP_TAC arith_ss []
) >>
subgoal `m < m'` >- (
  IMP_RES_TAC bir_exec_block_n_step_ls
) >>
FULL_SIMP_TAC arith_ss []
);


(*****************************************)
(* bir_exec_block_n + FUNPOW_OPT bir_trs *)

(* TODO: Should stay in this file. *)
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

(* TODO: Should stay in this file. *)
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

(* TODO: Should stay in this file. *)
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

(* TODO: Move to bir_program_multistep_propsTheory *)
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

(* TODO: Rename this lemma? *)
(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_block_n_block_ALT2 =
  store_thm ("bir_exec_block_n_block_ALT2",
  ``!p st m l' n'' c_l'' st''.
    (bir_exec_block_n p st (SUC m) = (l',n'',c_l'',st'')) ==>
    (?l n c_l st' l' n' c_l'.
     (bir_exec_block_n p st m = (l,n,c_l,st')) /\
     (bir_exec_block_n p st' 1 = (l',n',c_l',st'')))``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `SUC m = m + 1`
  (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  DECIDE_TAC
) >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add] >>
(* TODO: bir_exec_block_n_EXISTS? *)
`?l1 c1 c_bl1 st1. bir_exec_block_n p st m = (l1, c1, c_bl1, st1)` by METIS_TAC[pairTheory.PAIR] >>
`?l2 c2 c_bl2 st2. bir_exec_block_n p st1 1 = (l2, c2, c_bl2, st2)` by METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [LET_DEF]
);

(* TODO: What to do with this? Maybe discard and use subgoals
 * instead? *)
(* Similar to bir_exec_stmtsB_pc_unchanged in
 * bir_program_blocksTheory but without abuse of PC equality *)
val bir_exec_stmtsB_pc_invar =
  store_thm ("bir_exec_stmtsB_pc_invar",
  ``!bstmts st l c st'.
    (bir_exec_stmtsB bstmts ([],0,st) = (l,c,st')) ==>
    (st'.bst_pc.bpc_label = st.bst_pc.bpc_label)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_stmtsB_pc_unchanged >>
FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

(*******************************************)
(* bir_exec_to_labels_n + bir_exec_block_n *)

(* TODO: Try to phrase as much as possible only in terms of
 * bir_exec_block_n... *)
(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term =
  store_thm("bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term",
  ``!ls prog ms l' n' n0 ms' b.
    (bir_exec_to_labels ls prog ms = BER_Ended l' n' n0 ms') ==>
    (ms.bst_status = BST_Running) ==>
    (ms'.bst_status = BST_JumpOutside b) ==>
    ((bir_block_pc b).bpc_index = 0) ==>
    ?m.
    (bir_exec_block_n prog ms (SUC m) = (l',n',SUC m,ms'))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
Cases_on `n'` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_n_REWR_0]
) >>
rename1 `bir_exec_step_n prog ms (SUC n') = (l',SUC n',ms')` >>
IMP_RES_TAC bir_program_terminationTheory.bir_exec_step_n_status_jumped >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
(* Translate both to bir_exec_steps_GEN? *)
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_step_n_TO_steps_GEN] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_SOME_EQ_Ended] >>
subgoal `bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
     (bir_exec_infinite_steps_fun prog ms (SUC n'))` >- (
  ASM_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_COUNT_PC_def, LET_DEF]
) >>
Cases_on `c_l'` >- (
  FULL_SIMP_TAC arith_ss
    [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF, LET_DEF]
) >>
Q.EXISTS_TAC `n` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
(* Proof at this point: there is a PC count at SUC n'. There is also
 * an order on the bir_exec_infinite_steps_fun_COUNT_PCs function,
 * where increasing execution steps can never decrease return
 * value. *)
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss
  [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF] >>
subgoal `n'' <= n'` >- (
  FULL_SIMP_TAC arith_ss []
) >>
subgoal
  `bir_exec_infinite_steps_fun_COUNT_PCs
     (F,(\pc. pc.bpc_index = 0)) prog ms n'' <=
     bir_exec_infinite_steps_fun_COUNT_PCs
       (F,(\pc. pc.bpc_index = 0)) prog ms n'` >- (
  IMP_RES_TAC bir_exec_infinite_steps_fun_COUNT_PCs_MONO >>
    FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC arith_ss [LET_DEF]
);

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_TO_bir_exec_block_n_SUC_term =
  store_thm("bir_exec_to_labels_TO_bir_exec_block_n_SUC_term",
  ``!ls prog ms l' n' n0 ms'.
    (bir_exec_to_labels ls prog ms = BER_Ended l' n' n0 ms') ==>
    (ms'.bst_status <> BST_Running) ==>
    ?m.
    (bir_exec_block_n prog ms (SUC m) = (l',n',m,ms'))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
FULL_SIMP_TAC arith_ss [] >>
FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
REPEAT STRIP_TAC >>
subgoal
  `bir_exec_infinite_steps_fun_COUNT_PCs
     (F,(\pc. pc.bpc_index = 0)) prog ms n'' <=
     bir_exec_infinite_steps_fun_COUNT_PCs
       (F,(\pc. pc.bpc_index = 0)) prog ms n'` >- (
  subgoal `n'' <= n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  IMP_RES_TAC bir_exec_infinite_steps_fun_COUNT_PCs_MONO >>
   FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC arith_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory *)
(* TODO: Lemmatize this properly *)
val bir_exec_to_labels_bir_exec_block_n_term =
  store_thm("bir_exec_to_labels_bir_exec_block_n_term",
  ``!ls prog ms l' n' c_l' ms'.
    (bir_exec_to_labels ls prog ms =
       BER_Ended l' n' c_l' ms') ==>
    (ms.bst_status = BST_Running) ==>
    (ms'.bst_status <> BST_Running) ==>
    ?m m'.
    ?l''' n'''  ms'''.
    (bir_exec_block_n prog ms (SUC m) = (l', n', m', ms')) /\
    (bir_exec_block_n prog ms m = (l''', n''', m, ms''')) /\
    (ms'''.bst_status = BST_Running)``,

REPEAT STRIP_TAC >>
Cases_on `!b. ms'.bst_status <> BST_JumpOutside b` >- (
  IMP_RES_TAC bir_exec_to_labels_TO_bir_exec_block_n_SUC_term >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `m` >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bir_exec_block_n_block_ALT2 >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog ms m = (l,n,c_l,ms'')` >>
  Q.EXISTS_TAC `ms''` >>
  subgoal `~(n' < n)` >- (
    subgoal `m < SUC m` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>
    IMP_RES_TAC bir_exec_block_n_block_ls
  ) >>
  Cases_on `n = n'` >- (
    (* If SUC m steps of block execution encountered m blocks before
     * termination, then m steps of block execution must have
     * encountered m blocks also *)
    subgoal `c_l = m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `c_l = m` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    (* This gives that ms' = ms''. But from the m block-step execution
     * we have that bir_state_COUNT_PC is fulfilled in ms''. This
     * gives contradiction among assumptions in all cases but
     * JumpedOutside. *)
    subgoal `ms' = ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `ms' = ms''`
      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    subgoal `0 < m ==>
	     bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
	       (bir_exec_infinite_steps_fun prog ms n)` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0]
    ) >>
    FULL_SIMP_TAC arith_ss [bir_state_COUNT_PC_def] >>
    subgoal `bir_exec_infinite_steps_fun prog ms n = ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    Cases_on `ms''.bst_status` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    )
  ) >>
  subgoal `n < n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `c_l = m` >- (
    subgoal `~bir_state_is_terminated ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `c_l < m` >- (
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC arith_ss
      [bir_exec_block_n_EQ_THM]
  ) >>
  subgoal `(!n.
	    n < n' ==>
	    ~bir_state_is_terminated
              (bir_exec_infinite_steps_fun prog ms n))` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!(n:num). n < n' ==> _`` [`n`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM,
			bir_state_is_terminated_def]
) >>
(* Case JumpOutside: *)
FULL_SIMP_TAC std_ss [] >>
Cases_on `(bir_block_pc b).bpc_index = 0` >| [
  (* Block outside program fulfils PC count *)
  IMP_RES_TAC
    bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term >>
  IMP_RES_TAC bir_exec_block_n_block_ALT2 >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `SUC m` >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog ms m = (l,n,c_l,ms'')` >>
  Q.EXISTS_TAC `ms''` >>
  subgoal `~(n' < n)` >- (
    subgoal `m < SUC m` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>
    IMP_RES_TAC bir_exec_block_n_block_ls
  ) >>
  Cases_on `n = n'` >- (
    (* If SUC m steps of block execution encountered m blocks before
     * termination, then m steps of block execution must have
     * encountered m blocks also *)
    subgoal `c_l = SUC m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `n < n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `c_l = m` >- (
    subgoal `~bir_state_is_terminated ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `c_l < m` >- (
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC arith_ss
      [bir_exec_block_n_EQ_THM]
  ) >>
  subgoal `(!n.
	       n < n' ==>
	       ~bir_state_is_terminated
		 (bir_exec_infinite_steps_fun prog ms n))` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!(n:num). n < n' ==> _`` [`n`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM,
			bir_state_is_terminated_def],

  (* Block outside program does not fulfil PC count *)
  (* TODO: This is just the exact same procedure as for the regular
   * case. Make lemma? *)
  IMP_RES_TAC bir_exec_to_labels_TO_bir_exec_block_n_SUC_term >>
  IMP_RES_TAC bir_exec_block_n_block_ALT2 >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog ms m = (l,n,c_l,ms'')` >>
  Q.EXISTS_TAC `ms''` >>
  subgoal `~(n' < n)` >- (
    subgoal `m < SUC m` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>
    IMP_RES_TAC bir_exec_block_n_block_ls
  ) >>
  Cases_on `n = n'` >- (
    (* If SUC m steps of block execution encountered m blocks before
     * termination, then m steps of block execution must have
     * encountered m blocks also *)
    subgoal `c_l = m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `c_l = m`
      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    (* This gives that ms' = ms''. But from the m block-step
     * execution
     * we have that bir_state_COUNT_PC is fulfilled in ms''. This
     * gives contradiction among assumptions in all cases but
     * JumpedOutside. *)
    subgoal `ms' = ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `ms' = ms''`
      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    subgoal `0 < m ==>
	     bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
	       (bir_exec_infinite_steps_fun prog ms n)` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0]
    ) >>
    FULL_SIMP_TAC arith_ss [bir_state_COUNT_PC_def] >>
    subgoal `bir_exec_infinite_steps_fun prog ms n = ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  subgoal `n < n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `c_l = m` >- (
    subgoal `~bir_state_is_terminated ms''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `c_l < m` >- (
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC arith_ss
      [bir_exec_block_n_EQ_THM]
  ) >>
  subgoal `(!n.
	       n < n' ==>
	       ~bir_state_is_terminated
		 (bir_exec_infinite_steps_fun prog ms n))` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!(n:num). n < n' ==> _`` [`n`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM,
			bir_state_is_terminated_def]
]
);

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_n_block_n_notin_ls =
  store_thm("bir_exec_to_labels_n_block_n_notin_ls",
  ``!ls prog ms l l' n n' n0 c_l' c_l'' m m' ms' ms''.
  (bir_exec_to_labels_n ls prog ms 1 = BER_Ended l n n0 ms') ==>
  (bir_exec_block_n prog ms m' = (l',n',c_l'',ms'')) ==>
  (bir_exec_block_n prog ms m = (l,n,c_l',ms')) ==>
  (m' < m) ==>
  (0 < m') ==>
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

val bir_trs_term =
  store_thm("bir_trs_term",
  ``!prog n ms.
    bir_state_is_terminated ms ==>
    (bir_trs prog ms = NONE)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_trs_def] >>
IMP_RES_TAC bir_exec_block_n_REWR_TERMINATED >>
QSPECL_X_ASSUM ``!p n. _``
	       [`prog`, `1`] >>
FULL_SIMP_TAC std_ss [bir_state_is_terminated_def, LET_DEF]
);

val bir_trs_FUNPOW_term =
  store_thm("bir_trs_FUNPOW_term",
  ``!prog n ms.
    bir_state_is_terminated ms ==>
    n > 0 ==>
    (FUNPOW_OPT (bir_trs prog) n ms = NONE)``,

REPEAT STRIP_TAC >>
Cases_on `n` >| [
  FULL_SIMP_TAC arith_ss [],

  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS, bir_trs_term]
]
);

val bir_trs_FUNPOW_running =
  store_thm("bir_trs_FUNPOW_running",
  ``!prog n ms ms'.
    (FUNPOW_OPT (bir_trs prog) n ms = SOME ms') ==>
    n > 0 ==>
    ~(bir_state_is_terminated ms')``,

REPEAT STRIP_TAC >>
Cases_on `ms.bst_status = BST_Running` >- (
  IMP_RES_TAC FUNPOW_OPT_bir_trs_running >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `n` >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [FUNPOW_OPT_REWRS],

  FULL_SIMP_TAC (std_ss++holBACore_ss) [FUNPOW_OPT_REWRS,
                                        bir_trs_term]
]
);

(* 2. Prove that weak_model bir_etl_wm *)
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
    (* TODO: Move this to before CASE... *)
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
    IMP_RES_TAC bir_exec_to_labels_n_ended_running >>
    (* TODO: Add more common stuff here... *)
    EQ_TAC >| [
      (* Case 1AI: Assuming resulting states are equal, show
       * bir_trs plays nice (translate from block_n to bir_trs) *)
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
       * b = ms' (translate from bir_trs to block_n) *)
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
         * has crossed less than m' blocks. This would mean,
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

    (* TODO *)
    (* Case 1B: Ended + b is not Running. *)
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
    rename1 `FUNPOW_OPT (bir_trs prog) n' ms = SOME ms''` >>
    DISCH_TAC >>
    rename1 `m' > 0` >>
    DISCH_TAC >>
    rename1
      `bir_exec_to_labels ls prog ms = BER_Ended l n n0 ms'` >>
    rename1
      `bir_exec_to_labels ls prog ms = BER_Ended l' n n0 ms'` >>
    rename1
      `bir_exec_to_labels ls prog ms = BER_Ended l' n' n0 ms'` >>
    Cases_on `ms.bst_status <> BST_Running` >- (
      FULL_SIMP_TAC std_ss [GSYM bir_state_is_terminated_def] >>
      IMP_RES_TAC bir_trs_FUNPOW_term >>
      FULL_SIMP_TAC std_ss []
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    (* Translate to block-steps: *)
    (* If bir_exec_to_labels ended through termination, then we know
     * that the least number of necessary block-steps to get there
     * is some SUC m. *)
    subgoal
      `?m.
       ?c_l' l''' n''' c_l''' ms'''.
       (bir_exec_block_n prog ms (SUC m) = (l',n',c_l',ms')) /\
       (bir_exec_block_n prog ms m = (l''',n''',c_l''',ms''')) /\
       (ms'''.bst_status = BST_Running)` >- (
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC bir_exec_to_labels_bir_exec_block_n_term >>
      Q.EXISTS_TAC `m` >>
      Q.EXISTS_TAC `m''` >>
      Q.EXISTS_TAC `l'''` >>
      Q.EXISTS_TAC `n'''` >>
      Q.EXISTS_TAC `m` >>
      Q.EXISTS_TAC `ms'''` >>
      FULL_SIMP_TAC std_ss []
    ) >>
    IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
    rename1
      `bir_exec_block_n prog ms m' = (l'',n,c_l'',ms'')` >>
    rename1
      `bir_exec_block_n prog ms m' = (l'',n'',c_l'',ms'')` >>
    Cases_on `m' < (SUC m)` >| [
      (* If m' is less than SUC m, then ms'' is the result of less
       * than or equal the amount of statement-steps of
       * bir_exec_block_n. If the number of statement-steps n'' and
       * n' is equal, then we must also have
       * that m' >= SUC m (since termination occurs at exactly SUC m
       * block-steps), which contradicts the case. *)
      Cases_on `n'' = n'` >- (
	subgoal `m' >= SUC m` >- (
	  IMP_RES_TAC bir_exec_block_n_step_eq_block_gt
	) >>
        FULL_SIMP_TAC arith_ss []
      ) >>
      (* If n'' < n', then we have that either PC index of ms'' is
       * non-zero or PC label is not in ls (by bir_exec_to_labels
       * definition and bir_exec_steps_GEN_1_EQ_Ended). Since we
       * also know that status is Running for all block-steps less
       * than SUC m, the result of m' block-steps will always
       * have index zero (contradiction in assumptions), and so
       * PC label must not be in ls, which was the goal. *)
      Cases_on `n'' < n'` >- (
	subgoal `ms''.bst_status = BST_Running` >- (
	  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
                                bir_exec_to_labels_n_def,
				bir_exec_steps_GEN_1_EQ_Ended] >>
          QSPECL_X_ASSUM ``!(n:num). n < n' ==> _``
                         [`n''`] >>
          REV_FULL_SIMP_TAC arith_ss [] >>
          FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_is_terminated_def] >>
	    FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
				  bir_exec_steps_GEN_SOME_EQ_Ended]
	) >>
        subgoal `ms''.bst_pc.bpc_label NOTIN ls \/
                 ms''.bst_pc.bpc_index <> 0` >- (
	  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
                                bir_exec_to_labels_n_def,
				bir_exec_steps_GEN_1_EQ_Ended] >>
          subgoal `0 < n''` >- (
            subgoal `0 < m'` >- (
              FULL_SIMP_TAC arith_ss []
            ) >>
            IMP_RES_TAC bir_exec_block_n_block_nz_init_running
          ) >>
          QSPECL_X_ASSUM ``!(n:num). 0 < n /\ n < n' ==> _``
                         [`n''`] >>
          REV_FULL_SIMP_TAC arith_ss [] >>
          FULL_SIMP_TAC (std_ss++holBACore_ss)
            [bir_state_is_terminated_def,
             bir_state_COUNT_PC_def] >>
	  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
				bir_exec_steps_GEN_SOME_EQ_Ended] >>
          REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >> (
            FULL_SIMP_TAC std_ss []
          )
        ) >>
	FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
		              bir_exec_steps_GEN_SOME_EQ_Ended] >>
        REV_FULL_SIMP_TAC arith_ss [] >>
        Cases_on
          `bir_exec_infinite_steps_fun_COUNT_PCs
             (F,(\pc. pc.bpc_index = 0)) prog ms n'' < m'` >- (
          FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
        ) >>
        subgoal
          `bir_exec_infinite_steps_fun_COUNT_PCs
             (F,(\pc. pc.bpc_index = 0)) prog ms n'' = m'` >- (
          FULL_SIMP_TAC arith_ss []
        ) >>
        FULL_SIMP_TAC (std_ss++holBACore_ss)
          [bir_state_COUNT_PC_def]
      ) >>
      subgoal `n'' > n'` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      (* If n'' > n', then we can obtain that ms' is Running,
       * which means a contradiction among assumptions. *)
      FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
			    bir_exec_steps_GEN_SOME_EQ_Ended] >>
      QSPECL_X_ASSUM ``!n.
                       n < n'' ==>
                       ~bir_state_is_terminated
                         (bir_exec_infinite_steps_fun prog ms n)``
		     [`n'`] >>
      REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def],

      (* If m' is equal to or greater than SUC m, then the status
       * of ms'' must be terminated. But this means that the return
       * value of FUNPOW_OPT (bir_trs prog) m' ms must be NONE,
       * which is a contradiction among assumptions. *)
      subgoal `m' >= SUC m` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      IMP_RES_TAC bir_trs_FUNPOW_running >>
      IMP_RES_TAC bir_exec_block_n_not_running_block_ge >>
      FULL_SIMP_TAC (std_ss++holBACore_ss)
        [bir_state_is_terminated_def]
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

(****************************************************)
(* OLD BUT POTENTIALLY USEFUL STUFF: MOVE ELSEWHERE *)

(* TODO: Move to bir_programTheory? *)
val bir_exec_stmtB_pc =
  store_thm("bir_exec_stmtB_pc",
  ``!stmt st fe st'.
    (bir_exec_stmtB stmt st = (fe,st')) ==>
    (st.bst_pc.bpc_label = st'.bst_pc.bpc_label) /\
    (st.bst_pc.bpc_index <= st'.bst_pc.bpc_index)``,

Cases_on `st` >> Cases_on `st'` >>
Cases_on `b` >> Cases_on `b'` >>
rename1 `(bir_programcounter_t l2 n')` >>
rename1 `(bir_programcounter_t l2 i2)` >>
rename1 `(bir_programcounter_t l1 n)` >>
rename1 `(bir_programcounter_t l1 i1)` >>
REPEAT STRIP_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  Cases_on `stmt` >> FULL_SIMP_TAC std_ss [bir_exec_stmtB_def] >| [
    (* TODO: Lemmata about possible effects of executing the
     * different statements to avoid manual case splitting? *)
    FULL_SIMP_TAC std_ss [bir_exec_stmt_declare_def, LET_DEF] >>
    Cases_on
      `bir_env_varname_is_bound
	 (bir_state_t
           (bir_programcounter_t l1 i1) b0 b1).bst_environ
	 (bir_var_name b)` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates],

      Cases_on `bir_env_update (bir_var_name b)
		  (bir_declare_initial_value (bir_var_type b))
		  (bir_var_type b) b0` >> (
	FULL_SIMP_TAC (std_ss++holBACore_ss)
	  [bir_state_set_failed_def, bir_state_t_fn_updates]
      )
    ],

    FULL_SIMP_TAC std_ss [bir_exec_stmt_assign_def, LET_DEF] >>
    Cases_on
      `bir_env_write b
	 (bir_eval_exp b0''
	   (bir_state_t
             (bir_programcounter_t l1 i1) b0 b1).bst_environ
	 )
	 (bir_state_t
	   (bir_programcounter_t l1 i1) b0 b1
	 ).bst_environ` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates]
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_assert_def, LET_DEF] >>
    Cases_on
      `bir_dest_bool_val
	 (bir_eval_exp b
	   (bir_state_t
             (bir_programcounter_t l1 i1) b0 b1).bst_environ
	 )` >- (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `x` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates]
      )
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_assume_def, LET_DEF] >>
    Cases_on
      `bir_dest_bool_val
	 (bir_eval_exp b
	    (bir_state_t (bir_programcounter_t l1 i1) b0 b1
	 ).bst_environ)` >- (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	 [bir_state_set_failed_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `x` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates]
      )
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_observe_def, LET_DEF] >>
    Cases_on
      `bir_dest_bool_val
	 (bir_eval_exp b
	   (bir_state_t
	     (bir_programcounter_t l1 i1) b0 b1).bst_environ
	 )` >- (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	 [bir_state_set_failed_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `x` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates]
      )
    )
  ]
)
);

(* TODO: Move to bir_programTheory? *)
val bir_exec_stmtE_terminated_pc_unchanged =
  store_thm("bir_exec_stmtE_terminated_pc_unchanged",
  ``!prog stmt st st'.
    (bir_exec_stmtE prog stmt st = st') ==>
    ~bir_state_is_terminated st ==>
    bir_state_is_terminated st' ==>
    (st.bst_pc = st'.bst_pc)``,

REPEAT STRIP_TAC >>
Cases_on `st` >> Cases_on `st'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 `pc1 = b'` >>
rename1 `pc1 = pc2` >>
Cases_on `stmt` >> FULL_SIMP_TAC std_ss [bir_exec_stmtE_def] >| [
  (* Jmp *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
  Cases_on `bir_eval_label_exp b b0` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_failed_def, bir_state_t_fn_updates],

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_stmt_jmp_to_label_def] >>
    Cases_on `MEM x (bir_labels_of_program prog)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_t_fn_updates,
                   bir_state_is_terminated_def]
    ) 
  ],

  (* CJmp *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_cjmp_def] >>
  Cases_on `bir_dest_bool_val (bir_eval_exp b b0)` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_failed_def, bir_state_t_fn_updates]
  ) >> Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
    rename1 `bir_eval_label_exp b0'' b0` >>
    Cases_on `bir_eval_label_exp b0'' b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_exec_stmt_jmp_to_label_def] >>
      Cases_on `MEM x (bir_labels_of_program prog)` >> (
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_t_fn_updates,
		     bir_state_is_terminated_def]
      )
    ]
  ),

  (* Halt *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_halt_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_is_terminated_def, bir_state_t_fn_updates]
]
);

(* TODO: Move to bir_programTheory? *)
val bir_exec_stmtE_terminated_pc_changed =
  store_thm("bir_exec_stmtE_terminated_pc_changed",
  ``!prog stmt st st'.
    (bir_exec_stmtE prog stmt st = st') ==>
    ~bir_state_is_terminated st ==>
    ~bir_state_is_terminated st' ==>
    (st'.bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
Cases_on `st` >> Cases_on `st'` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
rename1 `pc2.bpc_index = 0` >>
rename1 `bir_state_t pc1 b0 b1` >>
Cases_on `stmt` >> FULL_SIMP_TAC std_ss [bir_exec_stmtE_def] >| [
  (* Jmp *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
  Cases_on `bir_eval_label_exp b b0` >| [
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_failed_def, bir_state_t_fn_updates,
       bir_state_is_terminated_def],

    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_stmt_jmp_to_label_def] >>
    Cases_on `MEM x (bir_labels_of_program prog)` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_state_t_fn_updates, bir_block_pc_def,
                   bir_state_is_terminated_def] >>
      RW_TAC std_ss []
    ) 
  ],

  (* CJmp *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_cjmp_def] >>
  Cases_on `bir_dest_bool_val (bir_eval_exp b b0)` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_failed_def, bir_state_t_fn_updates,
       bir_state_is_terminated_def]
  ) >> Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
    rename1 `bir_eval_label_exp b0'' b0` >>
    Cases_on `bir_eval_label_exp b0'' b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_failed_def, bir_state_t_fn_updates,
         bir_state_is_terminated_def],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_exec_stmt_jmp_to_label_def] >>
      Cases_on `MEM x (bir_labels_of_program prog)` >> (
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_t_fn_updates, bir_block_pc_def,
		     bir_state_is_terminated_def] >>
	RW_TAC std_ss []
      )
    ]
  ),

  (* Halt *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_halt_def,
                                        bir_state_is_terminated_def,
                                        bir_state_t_fn_updates]
]
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
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [
  (* BStmt *)
  FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >>
  Cases_on
    `bir_exec_stmtB b (FUNPOW (bir_exec_step_state prog) n ms)` >>
  Cases_on `bir_state_is_terminated r` >- (
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    IMP_RES_TAC bir_exec_stmtB_pc >>
    FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_state_is_terminated_def],

  (* EStmt *)
  Cases_on
    `bir_exec_stmtE prog b
       (FUNPOW (bir_exec_step_state prog) n ms)` >>
  IMP_RES_TAC bir_exec_stmtE_terminated_pc_unchanged >>
    FULL_SIMP_TAC std_ss []
]
);

val test_lemma4 = store_thm("test_lemma4",
  ``!prog ms n.
    (~bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog ms n)) ==>
    ((bir_exec_infinite_steps_fun prog ms n).bst_pc.bpc_index
       <> 0) ==>
    (bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog ms (SUC n))) ==>
    ((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc.bpc_index
       <> 0)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
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
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [
  (* BStmt *)
  (* TODO: Make lemma *)
  (* Contradiction: Can't execute from a BStmt at index nonzero
   * and reach index zero. *)
  Q.ABBREV_TAC `ms' = FUNPOW (bir_exec_step_state prog) n ms` >>
  Cases_on `bir_exec_stmtB b ms'` >>
  IMP_RES_TAC bir_exec_stmtB_pc >>
  Cases_on `bir_state_is_terminated r` >- (
    FULL_SIMP_TAC std_ss [LET_DEF] >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_state_is_terminated_def],

  (* EStmt *)
  (* TODO: Make lemma *)
  Q.ABBREV_TAC `ms' = FUNPOW (bir_exec_step_state prog) n ms` >>
  Cases_on `bir_exec_stmtE prog b ms'` >>
  IMP_RES_TAC bir_exec_stmtE_terminated_pc_unchanged >>
  FULL_SIMP_TAC std_ss []
]
);

val test_lemma3 =
  store_thm("test_lemma3",
  ``!prog ms n ls.
    ((bir_exec_infinite_steps_fun prog ms n).bst_pc.bpc_index <> 0) ==>
    ((bir_exec_infinite_steps_fun prog ms n).bst_pc.bpc_label NOTIN ls) ==>
    ((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc.bpc_label IN ls) ==>
    ((bir_exec_infinite_steps_fun prog ms (SUC n)).bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
Q.ABBREV_TAC `ms' = bir_exec_infinite_steps_fun prog ms n` >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2,
                          bir_exec_step_state_def,
                          bir_exec_step_def] >>
Cases_on `bir_state_is_terminated ms'` >- (
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_get_current_statement prog ms'.bst_pc` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [

  Cases_on `bir_exec_stmtB b ms'` >>
  IMP_RES_TAC bir_exec_stmtB_pc >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  Cases_on `bir_state_is_terminated r` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_pc_next_def]
  ),

  Cases_on `bir_exec_stmtE prog b ms'` >>
  Cases_on `bir_state_is_terminated (bir_state_t b' b0 b1)` >| [
    IMP_RES_TAC bir_exec_stmtE_terminated_pc_unchanged >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [],

    IMP_RES_TAC bir_exec_stmtE_terminated_pc_changed
  ]
]
);

(* TODO: Potentially useful lemma: if next state PC has non-zero
 * index, then statement-step execution did not change PC
 * label *)

val _ = export_theory();
