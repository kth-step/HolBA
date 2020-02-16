open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_auxiliaryTheory;
open bin_hoare_logicTheory;
open bir_program_multistep_propsTheory;
open bir_program_terminationTheory;
open bir_program_blocksTheory;

open bir_wm_instTheory;

open bir_auxiliaryLib;

open HolBACoreSimps;
open bin_hoare_logicSimps;

val _ = new_theory "bir_av_wm_inst";

(******************************************************************)
(*                         DEFINITIONS                            *)
(******************************************************************)

val _ = Datatype `bir_weak_state_t =
    BWS_Regular bir_label_t
  | BWS_Top
  | BWS_Bottom
`;


val bir_get_weak_state_def = Define `
  bir_get_weak_state st =
    if ~(bir_state_is_terminated st)
    then BWS_Regular (st.bst_pc.bpc_label)
    else if st.bst_status = BST_AssumptionViolated
    then BWS_Top
    else BWS_Bottom
`;


val bir_get_label_from_weak_state_def = Define `
  bir_get_label_from_weak_state ws =
    case ws of
      BWS_Regular l => SOME l
    | BWS_Top => NONE
    | BWS_Bottom => NONE
`;

val bir_get_label_set_from_weak_label_set_def = Define `
  bir_get_label_set_from_weak_label_set wss =
    (IMAGE THE
      ((IMAGE bir_get_label_from_weak_state wss) DELETE NONE)
    )
`;


(* The transition of the BIR WM *)
val bir_trs_av_def = Define `
  bir_trs_av (prog:'a bir_program_t) st =
  let
    (_, _, _, st') = bir_exec_block_n prog st 1;
    ws = bir_get_weak_state st'
  in
   if ws <> BWS_Bottom
   then SOME st'
   else NONE
`;


val bir_weak_trs_av_def = Define `
  bir_weak_trs_av wls prog st =
    let
      ls = bir_get_label_set_from_weak_label_set wls
    in
      case (bir_exec_to_labels ls prog st) of
	BER_Ended _ _ _ st' =>
	  if ((bir_get_weak_state st') IN (BWS_Top INSERT wls))
	  then SOME st'
	  else NONE
      | BER_Looping _ => NONE
`;


(* The BIR WM which is later proven to obey the property
 * "weak_model". *)
val bir_etl_wm_av_def =
  Define `bir_etl_wm_av (prog :'a bir_program_t) = <|
    trs  := bir_trs_av prog;
    weak := (\st ls st'.
	       (bir_weak_trs_av ls prog st = SOME st')
	    );
    pc   := (\st. bir_get_weak_state st)
  |>`;


(* TODO: Move this... *)
val ws_type = mk_thy_type {Tyop="bir_weak_state_t",
                           Thy="bir_av_wm_inst",
                           Args=[]
                          };

val bir_ws_SS = rewrites (flatten (map type_rws [ws_type]));


(******************************************************************)
(*                            LEMMATA                             *)
(******************************************************************)

val bir_wls_filter_keeps_regular =
  store_thm("bir_wls_filter_keeps_regular",
  ``!st wls.
    st.bst_pc.bpc_label NOTIN
      bir_get_label_set_from_weak_label_set wls <=>
    BWS_Regular st.bst_pc.bpc_label NOTIN wls``,

REPEAT STRIP_TAC >>
EQ_TAC >| [
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss
    [bir_get_label_set_from_weak_label_set_def,
     pred_setTheory.IMAGE_IN, pred_setTheory.IMAGE_DEF] >>
  REV_FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  QSPECL_X_ASSUM ``!x. _`` [`SOME st.bst_pc.bpc_label`] >>
  FULL_SIMP_TAC std_ss [] >>
  QSPECL_X_ASSUM ``!x'. _`` [`BWS_Regular st.bst_pc.bpc_label`] >>
  FULL_SIMP_TAC (std_ss++bir_ws_SS)
    [bir_get_label_from_weak_state_def],

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss
    [bir_get_label_set_from_weak_label_set_def,
     pred_setTheory.IMAGE_IN, pred_setTheory.IMAGE_DEF] >>
  REV_FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
  FULL_SIMP_TAC (std_ss++bir_ws_SS)
    [bir_get_label_from_weak_state_def] >>
  Cases_on `x'` >>
  FULL_SIMP_TAC (std_ss++bir_ws_SS) []
]
);


val bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av =
  store_thm("bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av",
  ``!st' prog st m l n c_l'.
      (bir_exec_block_n prog st m = (l,n,c_l',st')) ==>
      ((st'.bst_status = BST_Running) \/
       (st'.bst_status = BST_AssumptionViolated)) ==>
      (FUNPOW_OPT (bir_trs_av prog) m st = SOME st')``,

Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >> (
  QSPECL_X_ASSUM ``!st'. _`` [`st'`] >>
  REV_FULL_SIMP_TAC std_ss []
) >> (
(*
(* 1. Deal with case m = 0. *)
Cases_on `m = 0` >- (
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
  Cases_on `bir_trs_av prog st` >- (
    FULL_SIMP_TAC std_ss [bir_trs_av_def] >>
    REV_FULL_SIMP_TAC (std_ss++bir_ws_SS)
      [LET_DEF, bir_get_weak_state_def, bir_state_is_terminated_def]
  ) >>
  REV_FULL_SIMP_TAC std_ss [bir_trs_av_def, LET_DEF]
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
  ``!prog. _`` [`prog`, `st''`, `l'''`, `n'''`, `c_l''''`] >>
REV_FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
subgoal `bir_trs_av prog st = SOME st''` >- (
  FULL_SIMP_TAC std_ss [bir_trs_av_def, LET_DEF] >>
  cheat >>
  (* TODO *)
  IMP_RES_TAC bir_exec_block_n_block_ls_running_running >>
  FULL_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC std_ss []
*)
  cheat
)
);


val FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n =
  store_thm("FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n",
  ``!prog st m st'.
      (FUNPOW_OPT (bir_trs_av prog) m st = SOME st') ==>
      ?l n c_l'.
      (bir_exec_block_n prog st m = (l,n,c_l',st'))``,

(*
Induct_on `m` >- (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_n_REWR_0, FUNPOW_OPT_REWRS]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
Cases_on `bir_trs_av prog st` >- (
  FULL_SIMP_TAC std_ss []
) >>
QSPECL_X_ASSUM
  ``!prog. _`` [`prog`, `x`, `st'`] >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [arithmeticTheory.ADD1] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC std_ss [bir_exec_block_n_add, bir_trs_av_def, LET_DEF] >>
Cases_on `x.bst_status = BST_Running` >> (
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `bir_exec_block_n prog st 1` >> Cases_on `r` >>
  Cases_on `r'` >>
  FULL_SIMP_TAC std_ss [LET_DEF]
)
*)
cheat
);


(******************************************************************)
(*                         MAIN PROOF                             *)
(******************************************************************)

(* 2. Prove that weak_model bir_etl_wm *)
val bir_model_av_is_weak = store_thm("bir_model_av_is_weak",
  ``!(prog: 'a bir_program_t).
      weak_model (bir_etl_wm_av prog)``,

cheat
(*
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
              [weak_model_def, bir_etl_wm_av_def] >>
FULL_SIMP_TAC std_ss [bir_weak_trs_av_def, bir_get_weak_state_def,
                      LET_DEF] >>
REPEAT STRIP_TAC >>
CASE_TAC >| [
  (* Case 1: Result of bir_exec_to_labels is Ended *)
  Cases_on `~bir_state_is_terminated b` >- (
    FULL_SIMP_TAC (std_ss++bir_ws_SS++pred_setLib.PRED_SET_ss) [] >>
    Cases_on `BWS_Regular b.bst_pc.bpc_label IN ls` >| [
      subgoal `?m c_l'. (m > 0) /\ (bir_exec_block_n prog ms m = (l,n,c_l',b))` >- (
	FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
	IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
	Q.EXISTS_TAC `m` >>
	Q.EXISTS_TAC `c_l'` >>
	FULL_SIMP_TAC arith_ss []
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC bir_exec_to_labels_ended_running >>
      EQ_TAC >| [
(* TODO:
   New version of bir_exec_block_n_to_FUNPOW_OPT_bir_trs
*)
        cheat
(*
        (* Case 1AI: b=ms' as assumption *)
	DISCH_TAC >>
	(* Rename states and clean up *)
	rename1 `bir_exec_block_n prog st m = (l,n,c_l',b)` >>
	rename1 `bir_exec_block_n prog st m = (l,n,c_l',st'')` >>
	rename1 `st'' = st'` >>
        FULL_SIMP_TAC std_ss [] >>
	Q.PAT_X_ASSUM `st'' = st'`
		      (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
	(* We now have the initial state st and the final state
         * st' *)
	EXISTS_TAC ``m:num`` >>
	FULL_SIMP_TAC arith_ss [] >>
        FULL_SIMP_TAC std_ss
          [bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av] >>
	REPEAT STRIP_TAC >>
	rename1 `m' < m` >>
	ASSUME_TAC (Q.SPECL [`prog`, `st`, `m'`]
			    bir_exec_block_n_EXISTS) >>
	FULL_SIMP_TAC std_ss [] >>
	Q.EXISTS_TAC `st''` >>
	subgoal `~bir_state_is_terminated st''` >- (
	  IMP_RES_TAC bir_exec_block_n_block_ls_running_running
	) >>
	FULL_SIMP_TAC std_ss
	  [bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av] >>
	(* Use bir_exec_to_labels_n_block_n_notin_ls *)
	IMP_RES_TAC bir_exec_to_labels_block_n_notin_ls >>
	REV_FULL_SIMP_TAC arith_ss [] >>
	(* Here comes additional part for AV definitions... *)
        FULL_SIMP_TAC std_ss [bir_wls_filter_keeps_regular]
*),

	(* Case 1AII: Assuming bir_trs_av plays nice, show that
	 * b = st' (translate from bir_trs_av to block_n) *)
(* TODO: New version of FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n,
         bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av
*)
        cheat
(*
	REPEAT STRIP_TAC >>
	IMP_RES_TAC FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n >>
	rename1 `bir_exec_block_n prog st n' =
                   (l',n'',c_l'',ms')` >>
	rename1 `bir_exec_block_n prog st m' =
                   (l',n'',c_l'',ms')` >>
	rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',ms')` >>
	rename1 `bir_exec_block_n prog st m' = (l',n',c_l'',st')` >>
	(* Here, n < n' as well as n' < n leads to contradiction, so
	 * only remaining posssibility is n = n', which proves the
	 * goal. *)
	Cases_on `n' < n` >- (
	  (* This would mean that st' does not have PC with label in
	   * wls and pointing to instruction 0, which is a
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
	  IMP_RES_TAC bir_exec_to_labels_block_n_notin_ls >>
	  REV_FULL_SIMP_TAC arith_ss [] >>
          FULL_SIMP_TAC std_ss [bir_wls_filter_keeps_regular]
	) >>
	Cases_on `n < n'` >- (
	  (* Slightly more complex case: This would mean that
           * state b
	   * has crossed less than m' blocks. This would mean,
	   * together with init assumption, that PC label of b is
           * not in wls
           * (with bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av) *)
	  subgoal `m < m'` >- (
	    IMP_RES_TAC bir_exec_block_n_step_ls
	  ) >>
	  (* Use initial assumption *)
	  QSPECL_X_ASSUM
	    ``!n'.
             n' < m' /\ n' > 0 ==>
             ?ms''.
                 (FUNPOW_OPT (bir_trs_av prog) n' st = SOME ms'') /\
                 (if ~bir_state_is_terminated ms'' then
                    BWS_Regular ms''.bst_pc.bpc_label
                  else if ms''.bst_status = BST_AssumptionViolated then
                    BWS_Top
                  else BWS_Bottom) NOTIN wls`` [`m`] >>
	  REV_FULL_SIMP_TAC arith_ss [] >>
	  IMP_RES_TAC bir_exec_to_labels_ended_running >>
	  IMP_RES_TAC bir_exec_block_n_to_FUNPOW_OPT_bir_trs_av >>
	  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
	  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
          REV_FULL_SIMP_TAC std_ss []
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
 *)
      ],

      IMP_RES_TAC bir_exec_to_labels_ended_running >>
      IMP_RES_TAC bir_wls_filter_keeps_regular
    ]
  ) >>

  (* Case 1B *)
  (* This means that Ended must have been reached by termination
   * somewhere. *)
  FULL_SIMP_TAC std_ss [GSYM boolTheory.IMP_DISJ_THM] >>
  (* TODO: What now here? *)
  Cases_on `b.bst_status = BST_AssumptionViolated` >| [
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
    EQ_TAC >> (REPEAT STRIP_TAC) >| [
      subgoal `?m c_l'. (m > 0) /\
                        (bir_exec_block_n prog ms m =
                           (l,n,c_l',b))` >- (
	FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
	IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
	Q.EXISTS_TAC `m` >>
	Q.EXISTS_TAC `c_l'` >>
	FULL_SIMP_TAC arith_ss []
      ) >>
      EXISTS_TAC ``m:num`` >>
      FULL_SIMP_TAC arith_ss [] >>
      (* TODO: New stuff here *)
      cheat,

      (* TODO: New stuff here... *)
      cheat,

      (* ??? *)
      cheat
    ],

    cheat
  ],

  (* Case 2: Result of bir_exec_to_labels is Looping *)
(* TODO: New version of FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n
*)
  cheat
(*
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
  IMP_RES_TAC FUNPOW_OPT_bir_trs_av_to_bir_exec_block_n >>
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

    (* TODO: Only difference from non-AV is this case *)
    IMP_RES_TAC bir_wls_filter_keeps_regular
  ]
*)
]
*)
);


val _ = export_theory();
