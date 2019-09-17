open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;

open bin_hoare_logicLib;

open bin_hoare_logicSimps;
open HolBACoreSimps;

val _ = new_theory "bin_hoare_logic_test";

(******************************************************************)
(*                         DEFINITIONS                            *)
(******************************************************************)

val bir_trs_def = Define `
  bir_trs (prog:'a bir_program_t) st =
  let
    (_, _, _, st') = bir_exec_block_n prog st 1
  in
   if ~(bir_state_is_terminated st')
   then SOME st'
   else NONE
`;

val bir_weak_trs_def = Define `
  bir_weak_trs ls prog st =
    case (bir_exec_to_labels ls prog st) of
      BER_Ended _ _ _ st' =>
        if ~(bir_state_is_terminated st')
        then SOME st'
        else NONE
    | BER_Looping _ => NONE
`;

(* 1. Instantiate a new weak model *)
val bir_etl_wm_def =
  Define `bir_etl_wm (prog :'a bir_program_t) = <|
    trs  := bir_trs prog;
    weak := (\st ls st'.
	       (bir_weak_trs ls prog st = SOME st')
	    );
    pc   := (\st. st.bst_pc.bpc_label)
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
  ``!prog st m m' l n c_l' st'.
      (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
      1 <= m ==>
      m' < m ==>
      ?l' n' c_l'' st''.
        bir_exec_block_n prog st m' = (l', n', c_l'', st'')``,

REPEAT STRIP_TAC >>
Cases_on `bir_state_is_terminated st` >- (
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
     (SOME (SUC m')) prog st` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss)
                [bir_exec_infinite_steps_COUNT_STEPS_EQ_NONE] >>
  QSPECL_X_ASSUM ``!(i:num). _`` [`n`] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                        bir_exec_steps_GEN_def, LET_DEF] >>
  Cases_on `bir_exec_infinite_steps_COUNT_STEPS
              (F,(\pc. pc.bpc_index = 0))
              (SOME m) prog st` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  Q.PAT_X_ASSUM `x = n` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
  FULL_SIMP_TAC std_ss
                [bir_exec_infinite_steps_COUNT_STEPS_EQ_SOME] >- (
    QSPECL_X_ASSUM
      ``!n. ~bir_state_is_terminated
            (bir_exec_infinite_steps_fun prog st n)`` [`n`] >>
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
      (bir_get_current_block prog pc = NONE)``,

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
  ``!prog st m l n c_l' st'.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (n = 0) ==>
    (st' = st)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM,
                      bir_exec_infinite_steps_fun_REWRS]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_block_nz_init_running =
  store_thm("bir_exec_block_n_block_nz_init_running",
  ``!prog st m l n c_l' st'.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (0 < m) ==>
    ~(bir_state_is_terminated st) ==>
    0 < n``,

REPEAT STRIP_TAC >>
Cases_on `n <> 0` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC arith_ss [] >>
IMP_RES_TAC bir_exec_block_n_0_steps >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
FULL_SIMP_TAC (arith_ss++holBACore_ss)
              [bir_exec_infinite_steps_fun_COUNT_PCs_END_DEF]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_block_nz_final_running =
  store_thm("bir_exec_block_n_block_nz_final_running",
  ``!prog st m l n c_l' st'.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (0 < m) ==>
    ~(bir_state_is_terminated st') ==>
    (st'.bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
subgoal `c_l' = m` >- (
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
	      [bir_state_is_terminated_def, bir_state_COUNT_PC_def]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_running =
  store_thm("bir_exec_block_n_running",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    ~(bir_state_is_terminated st') ==>
    ~(bir_state_is_terminated st)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
Cases_on `n = 0` >- (
  FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
subgoal `n > 0` >- (
  FULL_SIMP_TAC arith_ss []
) >>
QSPECL_X_ASSUM ``!n'. _`` [`0`] >>
REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def,
                            bir_exec_infinite_steps_fun_REWRS]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_ls =
  store_thm("bir_exec_block_n_step_ls",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (n' < n) ==>
    m' < m``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
QSPECL_X_ASSUM ``!n'.
                 n' < n ==>
                 ~bir_state_is_terminated
                   (bir_exec_infinite_steps_fun prog st n') /\
                 _`` [`n'`] >>
PAT_ASSUM ``(n':num) < n``
          (fn  thm => FULL_SIMP_TAC arith_ss [thm])
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_block_ls =
  store_thm("bir_exec_block_n_block_ls",
  ``!prog st l l' n n' c_l' c_l'' st' m m' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (m' < m) ==>
    ~(n < n')``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_ls >>
FULL_SIMP_TAC arith_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_ls_running =
  store_thm("bir_exec_block_n_step_ls_running",
  ``!prog st l l' n n' c_l' c_l'' st' m m' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (n' < n) ==>
    ~(bir_state_is_terminated st') ==>
    ~(bir_state_is_terminated st'')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
QSPECL_X_ASSUM ``!n'.
                 n' < n ==>
                 ~bir_state_is_terminated
                   (bir_exec_infinite_steps_fun prog st n') /\
                 _`` [`n'`] >>
REV_FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_eq =
  store_thm("bir_exec_block_n_step_eq",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (n' = n) ==>
    (st' = st'')``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_not_running_block_ge =
  store_thm("bir_exec_block_n_not_running_block_ge",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    bir_state_is_terminated st' ==>
    (m' >= m) ==>
    (st' = st'')``,

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
           (bir_exec_infinite_steps_fun prog st n)` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
) >>
subgoal `st' = bir_exec_infinite_steps_fun prog st n` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
) >>
QSPECL_X_ASSUM ``!n. _`` [`n`] >>
REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def] >>
FULL_SIMP_TAC std_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_eq_running =
  store_thm("bir_exec_block_n_step_eq_running",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (n' = n) ==>
    ~(bir_state_is_terminated st') ==>
    (m' = m)``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_eq >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
Cases_on `c_l' < m` >- (
  METIS_TAC [bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC arith_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_block_ls_running_running =
  store_thm("bir_exec_block_n_block_ls_running_running",
  ``!prog st l l' n n' c_l' c_l'' st' m m' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (m' < m) ==>
    ~(bir_state_is_terminated st') ==>
    ~(bir_state_is_terminated st'')``,

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
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (n' = n) ==>
    (m' < m) ==>
    bir_state_is_terminated st''``,

REPEAT STRIP_TAC >>
IMP_RES_TAC bir_exec_block_n_step_eq >>
Q.PAT_X_ASSUM `st' = st''` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
IMP_RES_TAC bir_exec_block_n_step_eq_running >>
Cases_on `bir_state_is_terminated st''` >> (
  FULL_SIMP_TAC arith_ss []
)
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_block_ls_running_step_ls =
  store_thm("bir_exec_block_n_block_ls_running_step_ls",
  ``!prog st m m' l n c_l' st' l' n' c_l'' st''.
    (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
    (m' < m) ==>
    ~(bir_state_is_terminated st'') ==>
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
  ``!prog st m (l':'a list) l''' n n'' c_l' c_l''' st' st''.
    (bir_exec_block_n prog st (SUC m) =
       (l''', n'', c_l''', st'')) ==>
    (bir_exec_block_n prog st 1 = (l',n,c_l',st')) ==>
    (m > 0) ==>
    ?l'' n'' c_l''.
    (bir_exec_block_n prog st' m = (l'',n'',c_l'',st''))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [arithmeticTheory.ADD1] >>
Q.PAT_X_ASSUM
  `bir_exec_block_n prog st (m + 1) = (l''',n'',c_l''',st'')`
  (fn thm =>
    (subgoal `bir_exec_block_n prog st (1 + m) =
                (l''',n'',c_l''',st'')`
             >- (FULL_SIMP_TAC arith_ss [thm])
    )
  ) >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add] >>
REV_FULL_SIMP_TAC std_ss [LET_DEF] >>
Cases_on `bir_exec_block_n prog st' m` >> Cases_on `r` >>
  Cases_on `r'` >>
FULL_SIMP_TAC std_ss []
);

(* TODO: Move to bir_program_multistep_propsTheory? *)
val bir_exec_block_n_step_eq_block_gt =
  store_thm("bir_exec_block_n_step_eq_block_gt",
  ``!prog st m m' l' n' c_l' st' l'' n'' c_l'' st'' l''' n'''
    c_l''' st'''.
    (bir_exec_block_n prog st (SUC m) = (l',n',c_l',st')) ==>
    (bir_exec_block_n prog st m' = (l'',n'',c_l'',st'')) ==>
    (bir_exec_block_n prog st m = (l''',n''',c_l''',st''')) ==>
    (bir_state_is_terminated st') ==>
    ~(bir_state_is_terminated st''') ==>
    (n'' = n') ==>
    (m' >= SUC m)``,

REPEAT STRIP_TAC >>
Cases_on `n'' = n'''` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_block_n_EQ_THM] >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `n'' < n'''` >- (
  subgoal `!n.
	   n < n''' ==>
	   ~bir_state_is_terminated
	     (bir_exec_infinite_steps_fun prog st n)` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!n. _`` [`n''`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_block_n_EQ_THM] >>
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
  IMP_RES_TAC bir_exec_block_n_EXISTS_prev >>
  FULL_SIMP_TAC arith_ss []
) >>
(* 2. Describe case #blocks=m *)
subgoal `?l' n' c_l'' st''.
           bir_exec_block_n prog st m = (l',n',c_l'',st'')` >- (
  IMP_RES_TAC bir_exec_block_n_EXISTS_prev >>
  FULL_SIMP_TAC arith_ss []
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

(* TODO: Should stay in this file. *)
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

(* TODO: Should stay in this file. *)
val FUNPOW_OPT_bir_trs_running =
  store_thm("FUNPOW_OPT_bir_trs_running",
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


(************************)
(* bir_exec_to_labels_n *)

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_n_ended_running =
  store_thm("bir_exec_to_labels_n_ended_running",
  ``!ls prog st l n c_l' st'.
    (bir_exec_to_labels_n ls prog st 1 = BER_Ended l n c_l' st') ==>
    ~(bir_state_is_terminated st') ==>
    ((st'.bst_pc.bpc_index = 0) /\ st'.bst_pc.bpc_label IN ls)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >> (
  subgoal `c_l' = 1` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `st'.bst_status = BST_Running` >- (
    FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_COUNT_PC_def]
)
);

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_block_n_block_n =
  store_thm ("bir_exec_block_n_block_n",
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
(* TODO: bir_exec_block_n_EXISTS_prev? *)
`?l1 c1 c_bl1 st1. bir_exec_block_n p st m = (l1, c1, c_bl1, st1)`
  by METIS_TAC [pairTheory.PAIR] >>
`?l2 c2 c_bl2 st2. bir_exec_block_n p st1 1 = (l2, c2, c_bl2, st2)`
  by METIS_TAC [pairTheory.PAIR] >>
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

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term =
  store_thm("bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term",
  ``!ls prog st l' n' n0 st' b.
    (bir_exec_to_labels ls prog st = BER_Ended l' n' n0 st') ==>
    ~(bir_state_is_terminated st) ==>
    (st'.bst_status = BST_JumpOutside b) ==>
    ((bir_block_pc b).bpc_index = 0) ==>
    ?m.
    (bir_exec_block_n prog st (SUC m) = (l',n',SUC m,st'))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
Cases_on `n'` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_step_n_REWR_0]
) >>
rename1 `bir_exec_step_n prog st (SUC n') = (l',SUC n',st')` >>
IMP_RES_TAC bir_exec_step_n_status_jumped >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
(* Translate both to bir_exec_steps_GEN? *)
FULL_SIMP_TAC std_ss [bir_exec_block_n_TO_steps_GEN,
                      bir_exec_step_n_TO_steps_GEN] >>
FULL_SIMP_TAC std_ss [bir_exec_steps_GEN_SOME_EQ_Ended] >>
subgoal `bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
     (bir_exec_infinite_steps_fun prog st (SUC n'))` >- (
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
     (F,(\pc. pc.bpc_index = 0)) prog st n'' <=
     bir_exec_infinite_steps_fun_COUNT_PCs
       (F,(\pc. pc.bpc_index = 0)) prog st n'` >- (
  IMP_RES_TAC bir_exec_infinite_steps_fun_COUNT_PCs_MONO >>
    FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC arith_ss [LET_DEF]
);

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_TO_bir_exec_block_n_SUC_term =
  store_thm("bir_exec_to_labels_TO_bir_exec_block_n_SUC_term",
  ``!ls prog st l' n' n0 st'.
    (bir_exec_to_labels ls prog st = BER_Ended l' n' n0 st') ==>
    bir_state_is_terminated st' ==>
    ?m.
    (bir_exec_block_n prog st (SUC m) = (l',n',m,st'))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
FULL_SIMP_TAC arith_ss [] >>
FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
REPEAT STRIP_TAC >>
subgoal
  `bir_exec_infinite_steps_fun_COUNT_PCs
     (F,(\pc. pc.bpc_index = 0)) prog st n'' <=
     bir_exec_infinite_steps_fun_COUNT_PCs
       (F,(\pc. pc.bpc_index = 0)) prog st n'` >- (
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
  ``!ls prog st l' n' c_l' st'.
    (bir_exec_to_labels ls prog st =
       BER_Ended l' n' c_l' st') ==>
    ~(bir_state_is_terminated st) ==>
    bir_state_is_terminated st' ==>
    ?m m'.
    ?l''' n'''  st'''.
    (bir_exec_block_n prog st (SUC m) = (l', n', m', st')) /\
    (bir_exec_block_n prog st m = (l''', n''', m, st''')) /\
    ~(bir_state_is_terminated st''')``,

REPEAT STRIP_TAC >>
Cases_on `!b. st'.bst_status <> BST_JumpOutside b` >- (
  IMP_RES_TAC bir_exec_to_labels_TO_bir_exec_block_n_SUC_term >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `m` >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bir_exec_block_n_block_n >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog st m = (l,n,c_l,st'')` >>
  Q.EXISTS_TAC `st''` >>
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
    (* This gives that st' = st''. But from the m block-step
     * execution we have that bir_state_COUNT_PC is fulfilled in
     * st''. This gives contradiction among assumptions in all
     * cases but JumpedOutside. *)
    subgoal `st' = st''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `st' = st''`
      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    subgoal `0 < m ==>
	     bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
	       (bir_exec_infinite_steps_fun prog st n)` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0]
    ) >>
    FULL_SIMP_TAC arith_ss [bir_state_COUNT_PC_def] >>
    subgoal `bir_exec_infinite_steps_fun prog st n = st''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    Cases_on `st''.bst_status` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    )
  ) >>
  subgoal `n < n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `c_l = m` >- (
    subgoal `~bir_state_is_terminated st''` >- (
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
              (bir_exec_infinite_steps_fun prog st n))` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!(n:num). n < n' ==> _`` [`n`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
) >>
(* Case JumpOutside: *)
FULL_SIMP_TAC std_ss [] >>
Cases_on `(bir_block_pc b).bpc_index = 0` >| [
  (* Block outside program fulfils PC count *)
  IMP_RES_TAC
    bir_exec_to_labels_TO_bir_exec_block_n_SUC_both_term >>
  IMP_RES_TAC bir_exec_block_n_block_n >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `SUC m` >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog st m = (l,n,c_l,st'')` >>
  Q.EXISTS_TAC `st''` >>
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
    subgoal `~bir_state_is_terminated st''` >- (
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
		 (bir_exec_infinite_steps_fun prog st n))` >- (
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
  IMP_RES_TAC bir_exec_block_n_block_n >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `m` >>
  Q.EXISTS_TAC `l` >>
  Q.EXISTS_TAC `n` >>
  rename1
    `bir_exec_block_n prog st m = (l,n,c_l,st'')` >>
  Q.EXISTS_TAC `st''` >>
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
    (* This gives that st' = st''. But from the m block-step
     * execution
     * we have that bir_state_COUNT_PC is fulfilled in st''. This
     * gives contradiction among assumptions in all cases but
     * JumpedOutside. *)
    subgoal `st' = st''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Q.PAT_X_ASSUM `st' = st''`
      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
    subgoal `0 < m ==>
	     bir_state_COUNT_PC (F,(\pc. pc.bpc_index = 0))
	       (bir_exec_infinite_steps_fun prog st n)` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    Cases_on `m` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0]
    ) >>
    FULL_SIMP_TAC arith_ss [bir_state_COUNT_PC_def] >>
    subgoal `bir_exec_infinite_steps_fun prog st n = st''` >- (
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  subgoal `n < n'` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  subgoal `c_l = m` >- (
    subgoal `~bir_state_is_terminated st''` >- (
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
		 (bir_exec_infinite_steps_fun prog st n))` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  QSPECL_X_ASSUM ``!(n:num). n < n' ==> _`` [`n`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
]
);

(* TODO: Move to bir_program_multistep_propsTheory *)
val bir_exec_to_labels_n_block_n_notin_ls =
  store_thm("bir_exec_to_labels_n_block_n_notin_ls",
  ``!ls prog st l l' n n' n0 c_l' c_l'' m m' st' st''.
  (bir_exec_to_labels_n ls prog st 1 = BER_Ended l n n0 st') ==>
  (bir_exec_block_n prog st m' = (l',n',c_l'',st'')) ==>
  (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
  (m' < m) ==>
  (0 < m') ==>
  ~(bir_state_is_terminated st'') ==>
  st''.bst_pc.bpc_label NOTIN ls``,

REPEAT STRIP_TAC >>
subgoal `n' < n` >- (
  METIS_TAC [bir_exec_block_n_block_ls_running_step_ls]
) >>
subgoal `~(bir_state_is_terminated st)` >- (
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
       prog st n' < 1` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended]
) >>
QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
REV_FULL_SIMP_TAC std_ss [NUM_LSONE_EQZ] >>
FULL_SIMP_TAC std_ss
  [bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
QSPECL_X_ASSUM ``!(j:num). _`` [`PRE n'`] >>
REV_FULL_SIMP_TAC arith_ss [arithmeticTheory.SUC_PRE,
			    bir_state_COUNT_PC_def] >>
subgoal `bir_exec_infinite_steps_fun prog st n' = st''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
  [bir_state_is_terminated_def] >>
METIS_TAC [arithmeticTheory.SUC_PRE,
           bir_exec_block_n_block_nz_final_running,
           bir_state_is_terminated_def]
);

val bir_trs_term =
  store_thm("bir_trs_term",
  ``!prog n st.
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

val bir_trs_FUNPOW_running =
  store_thm("bir_trs_FUNPOW_running",
  ``!prog n st st'.
    (FUNPOW_OPT (bir_trs prog) n st = SOME st') ==>
    n > 0 ==>
    ~(bir_state_is_terminated st')``,

REPEAT STRIP_TAC >>
Cases_on `st.bst_status = BST_Running` >- (
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
      (* Case 1AI *)
      REPEAT DISCH_TAC >>
      (* subsume b... *)
      rename1 `bir_exec_block_n prog st m = (l,n,c_l',b)` >>
      rename1 `bir_exec_block_n prog st m = (l,n,c_l',st'')` >>
      rename1 `st'' = st'` >>
      Q.PAT_X_ASSUM `st'' = st'`
                    (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      EXISTS_TAC ``m:num`` >>
      FULL_SIMP_TAC arith_ss [] >>
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      REPEAT STRIP_TAC >>
      rename1 `m' < m` >>
      IMP_RES_TAC (Q.SPECL [`prog`, `st`, `m`, `m'`]
                           bir_exec_block_n_EXISTS_prev) >>
      Q.EXISTS_TAC `st''` >>
      subgoal `~bir_state_is_terminated st''` >- (
	IMP_RES_TAC bir_exec_block_n_block_ls_running_running
      ) >>
      FULL_SIMP_TAC std_ss
        [bir_exec_block_n_to_FUNPOW_OPT_bir_trs] >>
      (* Use bir_exec_to_labels_n_block_n_notin_ls *)
      IMP_RES_TAC bir_exec_to_labels_n_block_n_notin_ls >>
      FULL_SIMP_TAC arith_ss [],

      (* Case 1AII: Assuming bir_trs plays nice, show that
       * b = st' (translate from bir_trs to block_n) *)
      REPEAT STRIP_TAC >>
      IMP_RES_TAC FUNPOW_OPT_bir_trs_to_bir_exec_block_n >>
      rename1 `bir_exec_block_n prog st n' = (l',n'',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog st m' = (l',n'',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',ms')` >>
      rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',st')` >>
      (* Here, n < n' as well as n' < n leads to contradiction, so
       * only remaining posssibility is n = n', which proves the
       * goal. *)
      Cases_on `n' < n` >- (
        (* This would mean that st' does not have PC with label in
         * ls and pointing to instruction 0, which is a
         * contradiction. *)
        (* Step 1: Prove m' < m *)
	subgoal `m' < m` >- (
	  METIS_TAC [bir_exec_block_n_step_ls]
	) >>
        (* Step 2: Prove st'.bst_status = BST_Running *)
        subgoal `~bir_state_is_terminated st'` >- (
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
        QSPECL_X_ASSUM
          ``!n'.
             n' < m' /\ n' > 0 ==>
             ?ms''.
                 (FUNPOW_OPT (bir_trs prog) n' st = SOME ms'') /\
                 ms''.bst_pc.bpc_label NOTIN ls`` [`m`] >>
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
        subgoal `~bir_state_is_terminated st'` >- (
	  IMP_RES_TAC bir_exec_block_n_step_eq >>
	  REV_FULL_SIMP_TAC arith_ss []
        ) >>
        IMP_RES_TAC bir_exec_block_n_step_eq_running
      ) >>
      FULL_SIMP_TAC arith_ss []
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
    Cases_on `m' < (SUC m)` >| [
      (* If m' is less than SUC m, then st'' is the result of less
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
      (* If n'' < n', then we have that either PC index of st'' is
       * non-zero or PC label is not in ls (by bir_exec_to_labels
       * definition and bir_exec_steps_GEN_1_EQ_Ended). Since we
       * also know that status is Running for all block-steps less
       * than SUC m, the result of m' block-steps will always
       * have index zero (contradiction in assumptions), and so
       * PC label must not be in ls, which was the goal. *)
      Cases_on `n'' < n'` >- (
	subgoal `~bir_state_is_terminated st''` >- (
	  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def,
                                bir_exec_to_labels_n_def,
				bir_exec_steps_GEN_1_EQ_Ended] >>
          QSPECL_X_ASSUM ``!(n:num). n < n' ==> _``
                         [`n''`] >>
          REV_FULL_SIMP_TAC arith_ss [] >>
	  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
	) >>
        subgoal `st''.bst_pc.bpc_label NOTIN ls \/
                 st''.bst_pc.bpc_index <> 0` >- (
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
            [bir_state_COUNT_PC_def, bir_state_is_terminated_def] >>
	  FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
          REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >> (
            FULL_SIMP_TAC std_ss []
          )
        ) >>
        Cases_on
          `bir_exec_infinite_steps_fun_COUNT_PCs
             (F,(\pc. pc.bpc_index = 0)) prog st n'' < m'` >- (
          FULL_SIMP_TAC arith_ss [bir_exec_block_n_EQ_THM,
                                  bir_state_is_terminated_def] >>
          REV_FULL_SIMP_TAC arith_ss []
        ) >>
        subgoal
          `bir_exec_infinite_steps_fun_COUNT_PCs
             (F,(\pc. pc.bpc_index = 0)) prog st n'' = m'` >- (
          FULL_SIMP_TAC arith_ss [bir_exec_block_n_EQ_THM]
        ) >>
        subgoal `st''.bst_pc.bpc_index = 0` >- (
          FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
          subgoal
            `bir_exec_infinite_steps_fun prog st n'' = st''` >- (
            FULL_SIMP_TAC (std_ss++holBACore_ss)
              [bir_exec_block_n_EQ_THM]
          ) >>
          FULL_SIMP_TAC (arith_ss++holBACore_ss)
            [bir_exec_block_n_EQ_THM, bir_state_COUNT_PC_def,
             bir_state_is_terminated_def]
        )
      ) >>
      subgoal `n'' > n'` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      (* If n'' > n', then we can obtain that st' is Running,
       * which means a contradiction among assumptions. *)
      FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM] >>
      QSPECL_X_ASSUM ``!n'.
                       n' < n'' ==>
                       ~bir_state_is_terminated
                         (bir_exec_infinite_steps_fun prog st n') /\
                       _``
		     [`n'`] >>
      REV_FULL_SIMP_TAC arith_ss [],

      (* If m' is equal to or greater than SUC m, then the status
       * of st'' must be terminated. But this means that the return
       * value of FUNPOW_OPT (bir_trs prog) m' st must be NONE,
       * which is a contradiction among assumptions. *)
      subgoal `m' >= SUC m` >- (
        FULL_SIMP_TAC arith_ss []
      ) >>
      IMP_RES_TAC bir_trs_FUNPOW_running >>
      IMP_RES_TAC bir_exec_block_n_not_running_block_ge >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
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
  rename1 `bir_exec_block_n prog st m = (l',n,c_l',ms')` >>
  rename1 `bir_exec_block_n prog st m = (l',n,c_l',st')` >>
  QSPECL_X_ASSUM ``!(n:num). (0 < n) ==> _`` [`n`] >>
  (* Since m is larger than zero, n has to be as well...
   * if st is Running *)
  subgoal `~bir_state_is_terminated st` >- (
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
  subgoal `bir_exec_infinite_steps_fun prog st n = st'` >- (
    FULL_SIMP_TAC std_ss [bir_exec_block_n_EQ_THM]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
		[bir_state_is_terminated_def] >| [
    IMP_RES_TAC bir_exec_block_n_block_nz_final_running >>
    REV_FULL_SIMP_TAC arith_ss [bir_state_is_terminated_def],

    IMP_RES_TAC bir_exec_block_n_to_FUNPOW_OPT_bir_trs >>
    FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
  ]
]
);

(****************************************************)
(* OLD BUT POTENTIALLY USEFUL STUFF: MOVE ELSEWHERE *)
(* TODO: Use bir_exec_block_n_EQ_THM where appropriate *)


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
    FULL_SIMP_TAC std_ss [bir_exec_stmt_assign_def, LET_DEF] >>
    Cases_on
      `bir_eval_exp b0''
         (bir_state_t (bir_programcounter_t l1 i1)
                      b0 b1
         ).bst_environ` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_typeerror_def, bir_state_t_fn_updates]
    ) >>
    Cases_on
      `bir_env_write b x b0` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_t_fn_updates]
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_assert_def, LET_DEF] >>
    Cases_on
      `bir_eval_exp b
         (bir_state_t (bir_programcounter_t l1 i1)
                      b0 b1
         ).bst_environ` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_typeerror_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `bir_dest_bool_val x` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
	  [bir_state_t_fn_updates]
      ) >>
      Cases_on `x'` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_t_fn_updates]
      )
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_assume_def, LET_DEF] >>
    Cases_on
      `bir_eval_exp b
         (bir_state_t (bir_programcounter_t l1 i1)
                      b0 b1
         ).bst_environ` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	 [bir_state_set_typeerror_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `bir_dest_bool_val x` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
	  [bir_state_t_fn_updates]
      ) >>
      Cases_on `x'` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_t_fn_updates]
      )
    ),

    FULL_SIMP_TAC std_ss [bir_exec_stmt_observe_def, LET_DEF] >>
    Cases_on
      `bir_eval_exp b
         (bir_state_t (bir_programcounter_t l1 i1)
                      b0 b1
         ).bst_environ` >> (
       FULL_SIMP_TAC (std_ss++holBACore_ss)
	 [bir_state_set_typeerror_def, bir_state_t_fn_updates]
    ) >> (
      Cases_on `bir_dest_bool_val x` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
	  [bir_state_t_fn_updates]
      ) >>
      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
          [bir_state_t_fn_updates]
      ) >>
      Cases_on `EXISTS IS_NONE (MAP (\e. bir_eval_exp e b0) l)` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss)
          [bir_state_t_fn_updates]
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
      [bir_state_set_typeerror_def, bir_state_t_fn_updates],

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
  Cases_on `bir_eval_exp b b0` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_typeerror_def, bir_state_t_fn_updates, LET_DEF]
  ) >>
  Cases_on `bir_dest_bool_val x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def]
  ) >>
  Cases_on `x'` >> (
    FULL_SIMP_TAC std_ss [] >>
    rename1 `bir_eval_label_exp b0'' b0` >>
    Cases_on `bir_eval_label_exp b0'' b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_typeerror_def, bir_state_t_fn_updates],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_exec_stmt_jmp_to_label_def] >>
      Cases_on `MEM x' (bir_labels_of_program prog)` >> (
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_t_fn_updates,
		     bir_state_is_terminated_def]
      )
    ]
  ),

  (* Halt *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_halt_def] >>
  Cases_on `bir_eval_exp b b0` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_typeerror_def, bir_state_t_fn_updates]
  )
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
      [bir_state_set_typeerror_def, bir_state_t_fn_updates,
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
  Cases_on `bir_eval_exp b b0` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_typeerror_def, bir_state_t_fn_updates,
       bir_state_is_terminated_def,
       optionTheory.option_case_compute, LET_DEF]
  ) >>
  Cases_on `bir_dest_bool_val x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_jmp_def] >>
    rename1 `bir_eval_label_exp b0'' b0` >>
    Cases_on `bir_eval_label_exp b0'' b0` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
	[bir_state_set_typeerror_def, bir_state_t_fn_updates,
         bir_state_is_terminated_def],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_exec_stmt_jmp_to_label_def] >>
      Cases_on `MEM x' (bir_labels_of_program prog)` >> (
	FULL_SIMP_TAC (std_ss++holBACore_ss)
		    [bir_state_t_fn_updates, bir_block_pc_def,
		     bir_state_is_terminated_def] >>
	RW_TAC std_ss []
      )
    ]
  ),

  (* Halt *)
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_halt_def] >>
  Cases_on `bir_eval_exp b b0` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_set_typeerror_def, bir_state_t_fn_updates,
       bir_state_is_terminated_def]
  )
]
);

val test_lemma = store_thm("test_lemma",
  ``!prog st n ls.
    (~bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog st n)) ==>
    ((bir_exec_infinite_steps_fun prog st n).bst_pc.bpc_label
       NOTIN ls) ==>
    (bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog st (SUC n))) ==>
    ((bir_exec_infinite_steps_fun prog st (SUC n)).bst_pc.bpc_label
       NOTIN ls)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_SUC,
                      bir_exec_step_state_def, bir_exec_step_def] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_get_current_statement prog
            (FUNPOW (bir_exec_step_state prog) n st).bst_pc` >- (
  Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_set_failed_def, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [
  (* BStmt *)
  FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >>
  Cases_on
    `bir_exec_stmtB b (FUNPOW (bir_exec_step_state prog) n st)` >>
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
       (FUNPOW (bir_exec_step_state prog) n st)` >>
  IMP_RES_TAC bir_exec_stmtE_terminated_pc_unchanged >>
    FULL_SIMP_TAC std_ss []
]
);

val test_lemma4 = store_thm("test_lemma4",
  ``!prog st n.
    (~bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog st n)) ==>
    ((bir_exec_infinite_steps_fun prog st n).bst_pc.bpc_index
       <> 0) ==>
    (bir_state_is_terminated
       (bir_exec_infinite_steps_fun prog st (SUC n))) ==>
    ((bir_exec_infinite_steps_fun prog st (SUC n)).bst_pc.bpc_index
       <> 0)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_def] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.FUNPOW_SUC,
                      bir_exec_step_state_def, bir_exec_step_def] >>
REV_FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_get_current_statement prog
            (FUNPOW (bir_exec_step_state prog) n st).bst_pc` >- (
  Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_state_set_failed_def, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [
  (* BStmt *)
  (* TODO: Make lemma *)
  (* Contradiction: Can't execute from a BStmt at index nonzero
   * and reach index zero. *)
  Q.ABBREV_TAC `st' = FUNPOW (bir_exec_step_state prog) n st` >>
  Cases_on `bir_exec_stmtB b st'` >>
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
  Q.ABBREV_TAC `st' = FUNPOW (bir_exec_step_state prog) n st` >>
  Cases_on `bir_exec_stmtE prog b st'` >>
  IMP_RES_TAC bir_exec_stmtE_terminated_pc_unchanged >>
  FULL_SIMP_TAC std_ss []
]
);

val test_lemma3 =
  store_thm("test_lemma3",
  ``!prog st n ls.
    ((bir_exec_infinite_steps_fun prog st n).bst_pc.bpc_index <> 0) ==>
    ((bir_exec_infinite_steps_fun prog st n).bst_pc.bpc_label NOTIN ls) ==>
    ((bir_exec_infinite_steps_fun prog st (SUC n)).bst_pc.bpc_label IN ls) ==>
    ((bir_exec_infinite_steps_fun prog st (SUC n)).bst_pc.bpc_index = 0)``,

REPEAT STRIP_TAC >>
Q.ABBREV_TAC `st' = bir_exec_infinite_steps_fun prog st n` >>
    FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS2,
                          bir_exec_step_state_def,
                          bir_exec_step_def] >>
Cases_on `bir_state_is_terminated st'` >- (
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `bir_get_current_statement prog st'.bst_pc` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Cases_on `x` >> FULL_SIMP_TAC std_ss [bir_exec_stmt_def] >| [

  Cases_on `bir_exec_stmtB b st'` >>
  IMP_RES_TAC bir_exec_stmtB_pc >>
  FULL_SIMP_TAC std_ss [LET_DEF] >>
  Cases_on `bir_state_is_terminated r` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [LET_DEF, bir_pc_next_def]
  ),

  Cases_on `bir_exec_stmtE prog b st'` >>
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
