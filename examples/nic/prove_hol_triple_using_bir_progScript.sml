(* In this script, we are trying to prove a theorem on a HOL4 state about a
 * BIR program.
 *
 * The program does the following:
 *
 *   nic.x := nic.x + 1
 *   if nic.x > 10:
 *     nic.dead := true
 *
 * We want to prove this property:
 *
 *   !nic nic'.
 *     (  (~nic.dead /\ nic.x = 0) .... {P(nic)}
 *     /\ (nic' = holprog nic)) ....... prog
 *     ==> (~nic'.dead /\ nic'.x = nic.x + 1) .. {Q(nic,nic')} .............. (1)
 *
 * However, the program is a BIR program working with a BIR state, so we
 * have to perform some plumbing:
 *
 *    {P}     HOL4 definition (a)     {Q}
 *    NIC --------------------------> NIC'
 *     |                               ^
 * (b) |                           (d) |
 *     v  {P'}    BIR program (c)      |  {Q'}
 *    BIR_STATE --------------------> BIR_STATE'
 *
 * When proving theorem 1, all we should have to know is the NIC state
 * definition and some equivalence theorem saying that ``NIC' = prog NIC``
 * (a) is equivalent to executing the BIR program from a state BIR_STATE to
 * a state BIR_STATE' (c), where NIC is somehow equivalent to BIR_STATE (b)
 * and NIC' somehow equivalent to BIR_STATE' (d).
 *
 * To express the equivalence between HOL4 states ("NIC") and BIR states,
 * we introduce a relation R (2). For the needs of our proof, we need the
 * following property:
 *
 *   !nic. ?bir_state. R nic bir_state ............................. (3)
 *
 * Finally, we also need an equivalence theorem between the HOL4 definition
 * (a) and the BIR program (c). This can be produced by a lifter.
 *
 *   !nic nic'. (nic' = prog nic)   ...................... (a)
 *     <=> !bir_state bir_state'.
 *           (  R nic bir_state     ...................... (b)
 *           /\ bir_state' = BIR_exec prog bir_state)   .. (c)
 *           ==> R nic' bir_state' ....................... (d) ..... (4)
 *
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory optionTheory;
open wordsLib;
open HolSmtLib;
open bir_envTheory bir_programTheory;
open bir_expTheory bir_bool_expTheory bir_valuesTheory;
open bir_exp_equivTheory bir_typing_progTheory
open bir_exp_immTheory;
open HolBASimps;
open bir_wpTheory;
open bslSyntax;
open pretty_exnLib;

if (!Globals.interactive) then let
  val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
  val _ = Globals.linewidth := 100;
  val _ = bir_ppLib.install_bir_pretty_printers ();
  (*
  val _ = bir_ppLib.remove_bir_pretty_printers ();
  *)
in () end else ();
val _ = Globals.show_tags := true;

val _ = new_theory "prove_hol_triple_using_bir_prog";

(* NIC state *)
val _ = Datatype `nic_state = <|
  dead : bool;
  x : word32
|>`;

(* This is the equivalent BIR program *)
val obs_ty = alpha
val bir_prog_def = bdefprog_list obs_ty "bir_prog" [
  (blabel_str "entry", [], (bjmp o belabel_str) "inc_x"),

  (blabel_str "inc_x", [
    bassign (bvarimm32 "nic_x",
             bplus ((bden o bvarimm32) "nic_x", bconst32 1))
  ], (bjmp o belabel_str) "cjmp"),

  (blabel_str "cjmp", [],
    bcjmp (blt (bconst32 10, (bden o bvarimm32) "nic_x"),
           belabel_str "nic_x_gt_10",
           belabel_str "epilogue")),

  (blabel_str "nic_x_gt_10", [
    bassign (bvarimm1 "nic_dead", btrue)
  ], (bjmp o belabel_str) "epilogue"),

  (blabel_str "epilogue", [], (bjmp o belabel_str) "end"),
  (blabel_str "end", [], bhalt (bconst32 0))
];
val entry_label_def = Define `entry_label = BL_Label "entry"`
val end_labels_def = Define `end_labels = (\label. label = (BL_Label "end"))`

(* Definition of the relation R (2) *)
val bool2imm1_def = Define `(bool2imm1 T = Imm1 1w) /\ (bool2imm1 F = Imm1 0w)`
val bool2imm1_REWR = store_thm ( "bool2imm1_REWR",
  ``!b. bool2imm1 b = Imm1 (if b then 1w else 0w)``,
  Cases >> FULL_SIMP_TAC std_ss [bool2imm1_def])
val bool2bexp_def = Define `(bool2bexp b = BExp_Const (bool2imm1 b))`
val bool2bval_def = Define `(bool2bval b = BVal_Imm (bool2imm1 b))`
val w2bval32_def = Define `(w2bval32 n = BVal_Imm (Imm32 n))`
val R_def = Define `
  R (nic: nic_state) (bir_state: bir_state_t) <=>
    (  (bir_state.bst_pc.bpc_index = 0)
    /\ (bir_state.bst_pc.bpc_label = entry_label)
    /\ (bir_state.bst_status = BST_Running)
    /\ (bir_env_lookup "nic_dead" bir_state.bst_environ
          = SOME (BType_Bool, SOME (bool2bval nic.dead)))
    /\ (bir_env_lookup "nic_x" bir_state.bst_environ
          = SOME (BType_Imm Bit32, SOME (w2bval32 nic.x))))`

(* Lemma (3) *)
val R_inj_thm = store_thm ( "R_inj_thm",
  ``!nic. ?bir_state. R nic bir_state``,
  STRIP_TAC >>
  REWRITE_TAC [R_def] >>
  EXISTS_TAC ``
    <|bst_pc := <|bpc_label := entry_label; bpc_index := 0|>;
      bst_status := BST_Running;
      bst_environ := BEnv (FEMPTY
        |+ ("nic_dead", (BType_Imm Bit1, SOME (bool2bval nic.dead)))
        |+ ("nic_x", (BType_Imm Bit32, SOME (w2bval32 nic.x)))
    )|>`` >>
  EVAL_TAC
)

(* Equivalence theorem (4) *)
val eq_thm = Define `
  (exec_prog nic bir_prog nic')
    = (!(bir_state:bir_state_t) (bir_state':bir_state_t).
         R nic bir_state
      /\ (?obs step_count pc_count.
            (bir_exec_to_labels end_labels bir_prog bir_state
                = BER_Ended obs step_count pc_count bir_state'))
      ==> R nic' bir_state')`

(* This is the theorem we want to prove *)
val NIC_P_def = Define `NIC_P nic = (nic.dead = F) /\ (nic.x = 0w)`
val NIC_Q_def = Define `NIC_Q nic nic' = (nic'.dead = F) /\ (nic'.x = 1w)`
val goal_tm = ``!nic nic'. (NIC_P nic /\ exec_prog nic bir_prog nic') ==> NIC_Q nic nic'``;

(* Equivalent preconditions on BIR variables *)
(* Should be possible to autogenerate *)
val BIR_P_exp_def = Define `BIR_P_exp = ^(bandl [
  beq ((bden o bvarimm1) "nic_dead", bfalse),
  beq ((bden o bvarimm32) "nic_x", bconst32 0)
])`
val BIR_Q_exp_def = Define `BIR_Q_exp = ^(bandl [
  beq ((bden o bvarimm1) "nic_dead", bfalse),
  beq ((bden o bvarimm32) "nic_x", bconst32 1)
])`
val BIR_P_def = Define `BIR_P bstate = bir_eval_bool_exp BIR_P_exp bstate.bst_environ`
val BIR_Q_def = Define `BIR_Q bstate = bir_eval_bool_exp BIR_Q_exp bstate.bst_environ`

(* (b): NIC --> BIR_state *)
val b_thm = store_thm ( "b_thm",
  ``!bir_state. (?nic. R nic bir_state /\ NIC_P nic) ==> BIR_P bir_state``,
  REWRITE_TAC [BIR_P_def, NIC_P_def, R_def, bool2bval_def, w2bval32_def, bool2imm1_def] >>
  SIMP_TAC std_ss [bir_eval_bool_exp_def, bir_eval_exp_def] >>
  REPEAT STRIP_TAC >>
  REPEAT (FULL_SIMP_TAC std_ss [] >> EVAL_TAC)
)

(* (d): BIR_state' --> NIC' *)
val holba_ss = arith_ss
  ++ wordsLib.WORD_ss
  ++ wordsLib.SIZES_ss
  ++ pred_setSimps.PRED_SET_ss
  ++ HolBACoreSimps.holBACore_ss
val EVAL_SIMP_TAC = (ASSUM_LIST
  (fn thms => SIMP_TAC holba_ss (List.map (EVAL o concl) thms)))
val FULL_EVAL_SIMP_TAC = (ASSUM_LIST
  (fn thms => FULL_SIMP_TAC holba_ss (List.map (EVAL o concl) thms)))
fun PAT_X_TAC pat = Q.PAT_X_ASSUM pat (fn thm => ALL_TAC)
val d_thm = store_thm ( "d_thm",
  ``!bir_state'. BIR_Q bir_state'
      ==> (!nic nic' bir_state. (BIR_P bir_state /\ R nic bir_state /\ R nic' bir_state')
            ==> (NIC_Q nic nic'))``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [NIC_Q_def] >>
  FULL_SIMP_TAC holba_ss [BIR_Q_def, BIR_Q_exp_def, R_def] >>
  FULL_SIMP_TAC holba_ss [bool2bval_def, w2bval32_def, bool2imm1_REWR] >>
  CCONTR_TAC >>
  REPEAT FULL_EVAL_SIMP_TAC
)

(* Useful lemmas *)
val BIR_P_is_bool_exp_thm = store_thm ( "BIR_P_is_bool_exp_thm",
  ``!nic bir_state.
      (R nic bir_state /\ BIR_P bir_state)
      ==> bir_is_bool_exp_env bir_state.bst_environ BIR_P_exp``,
  PURE_REWRITE_TAC [R_def, BIR_P_def, bir_is_bool_exp_env_def] >>
  REPEAT STRIP_TAC >| [
    PURE_REWRITE_TAC [bir_is_bool_exp_def, BIR_P_exp_def, type_of_bir_exp_def] >>
    PURE_REWRITE_TAC [bir_var_type_def, bir_type_is_Imm_def, type_of_bir_imm_def, BType_Bool_def] >>
    RW_TAC holba_ss []
    ,
    PURE_REWRITE_TAC [BIR_P_exp_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_def] >>
    RW_TAC holba_ss [] >>
    PURE_REWRITE_TAC [bir_env_var_is_initialised_def, BType_Bool_def] >>
    RW_TAC holba_ss [] >>
    REWRITE_TAC [BType_Bool_def] >>
    REWRITE_TAC [type_of_bir_val_def, bool2bval_def, bool2imm1_REWR, w2bval32_def] >>
    REWRITE_TAC [type_of_bir_imm_def]
  ])
val bir_eval_bool_exp_LEMMA = store_thm ( "bir_eval_bool_exp_LEMMA",
  ``!exp env.
      (  (bir_is_bool_exp_env env exp)
      /\ (bir_eval_exp exp env = bir_val_true))
      ==> (bir_eval_bool_exp exp env)``,
  METIS_TAC [bir_eval_bool_exp_EQ]
)
val eval_BIR_P_is_true_thm = store_thm ( "eval_BIR_P_is_true_thm",
  ``!nic bir_state.
      (R nic bir_state /\ BIR_P bir_state)
      ==> (bir_eval_exp BIR_P_exp bir_state.bst_environ = bir_val_true)``,
  METIS_TAC [BIR_P_is_bool_exp_thm, R_def, BIR_P_def, bir_eval_bool_exp_EQ]
)

(* TODO: Move to theory/bir[-support] *)
val bir_type_of_val_is_imm_then_exists_imm = prove (
  ``!imm_ty v. (type_of_bir_val v = SOME (BType_Imm imm_ty))
        ==> (?imm. v = (BVal_Imm imm))``,
  Cases_on `v` >>
  SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
)

(* {P} bir_prog {Q} *)
val (wp_thm, triple_thm) =
  let
    open bir_wpLib
    open boolTheory pred_setTheory
    (**)
    val post_def = BIR_Q_exp_def
    val wps_def = Define `wps = (FEMPTY |+ (BL_Label "end", BIR_Q_exp))`
    (**)
    val program = ``bir_prog``
    val post = ``BIR_Q_exp``
    val ls = ``end_labels``
    val wps = ``wps``
    val defs = [bir_prog_def, post_def, end_labels_def, wps_def]
    (**)
    val prog_tm = (snd o dest_comb o concl) bir_prog_def
    val wps_tm = (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps
    val wps_bool_sound_thm = bir_wp_init_wps_bool_sound_thm (program, post, ls) wps defs
    val (wpsdom, blstodo) = bir_wp_init_rec_proc_jobs prog_tm wps_tm
    (**)
    val reusable_thm = (INST_TYPE [alpha |-> obs_ty]) bir_wp_exec_of_block_reusable_thm
    val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls) defs
    (**)
    val (wpsrec, wpsrec_bool_sound_thm) = bir_wp_comp_wps prog_thm
      ((wps, wps_bool_sound_thm), (wpsdom, blstodo)) (program, post, ls) defs
    (**)
    val wpsrec_def = Define `wpsrec = ^wpsrec`
    val wpsrec_bool_sound_thm_readable = REWRITE_RULE [GSYM wpsrec_def] wpsrec_bool_sound_thm
    (**)
    val Abbrev_def = markerTheory.Abbrev_def
    val INITIALIZED_TAC = FULL_SIMP_TAC holba_ss [
      bir_is_bool_exp_env_def, BIR_P_exp_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_def,
      BIR_P_exp_def, EVAL ``bir_wp_comp_wps_iter_step2_wp_entry``, Abbrev_def]
    val IS_IMM_EXP_TAC = FULL_SIMP_TAC holba_ss [bir_is_imm_exp_def, Abbrev_def]
    val UNABBREV_EVAL_TAC = unabbrev_all_tac >> EVAL_TAC
    (**)
    val bexp_not_bool2b = prove (
      ``!b. (bir_unary_exp BIExp_Not (bool2b b)) = (bool2b ~b)``,
      Cases >> EVAL_TAC)
    val bexp_and_bool2b = prove (
      ``!a b. (bir_bin_exp BIExp_And (bool2b a) (bool2b b)) = (bool2b (a /\ b))``,
      REPEAT Cases >> EVAL_TAC)
    val bexp_or_bool2b = prove (
      ``!a b. (bir_bin_exp BIExp_Or (bool2b a) (bool2b b)) = (bool2b (a \/ b))``,
      REPEAT Cases >> EVAL_TAC)
    (**)
    fun REPEAT_N 1 tac = tac | REPEAT_N n tac = tac >> REPEAT_N (n-1) tac
    (**)
    val bir_exp_equiv_thms = [
      bir_equal_equiv,
      GSYM bir_and_equiv,
      GSYM bir_not_equiv,
      GSYM bir_or_impl
    ]
    val bir_eval_defs = [
      bir_eval_exp_def,
      bir_eval_bin_pred_def,
      bir_eval_bin_exp_def,
      bir_eval_unary_exp_def
    ]
    val bir_to_OPER_equiv_thms = [
      bir_unary_exp_def,
      bir_bin_exp_def,
      bir_bin_pred_def
    ]
    val OPER_thms = [bir_bin_exp_GET_OPER_def, bir_bin_pred_GET_OPER_def, bir_unary_exp_GET_OPER_def]
    val bool2b_REWRS = [
      bool2b_11, bool2b_inv,
      bool2b_ELIMS, bool2b_EQ_IMM1_ELIMS, bool2b_NEQ_IMM_ELIMS,
      bir_eval_bool_exp_BExp_Const_bool2b, BVal_Imm_bool2b_EQ_TF_REWRS,
      bexp_not_bool2b, bexp_and_bool2b, bexp_or_bool2b
    ]
    val BIR_TO_WORDS_ss = rewrites (
       bir_exp_equiv_thms
      @bir_eval_defs
      @bir_to_OPER_equiv_thms
      @OPER_thms
      @bool2b_REWRS
      @[type_of_bir_imm_def]
      @[EVAL ``~T``, COND_CLAUSES]
    )
    val bir_to_words_ss = pure_ss++HolBACoreSimps.holBACore_ss++BIR_TO_WORDS_ss

(*PURE_REWRITE_TAC [((UNDISCH o UNDISCH) (Q.SPECL [`env`, `BIR_P_exp`, `bir_wp_comp_wps_iter_step2_wp_entry`] bir_impl_equiv))]*)

    (**)
    val triple_thm = store_thm ( "triple_thm",
      ``bir_exec_to_labels_triple bir_prog entry_label end_labels BIR_P_exp BIR_Q_exp``,
      (* WP --> Q *)
      ASSUME_TAC wpsrec_bool_sound_thm >>
      RW_TAC std_ss [bir_sound_wps_map_def] >>
      ASSUME_TAC (SIMP_CONV (bool_ss++SET_SPEC_ss) [end_labels_def,
                                                    IN_DEF,
                                                    EVAL ``BL_Label "entry" = BL_Label "end"``]
                    ``(BL_Label "entry") IN end_labels``) >>
      FULL_SIMP_TAC std_ss [FEVERY_FUPDATE, entry_label_def] >>
      PAT_X_TAC `FEVERY _ _` >>
      PAT_X_TAC `_ NOTIN _` >>

      (* is_bool_exp WP *)
      FULL_SIMP_TAC std_ss [bir_bool_wps_map_def] >>
      FULL_SIMP_TAC std_ss [FEVERY_FUPDATE, entry_label_def] >>
      PAT_X_TAC `FEVERY _ _` >>

      (* some renaming *)
      Q.ABBREV_TAC `wp = bir_wp_comp_wps_iter_step2_wp_entry` >>
      Q.ABBREV_TAC `p = BIR_P_exp` >>
      Q.ABBREV_TAC `q = BIR_Q_exp` >>

      (* expand bir_exec_to_labels_triple *)
      SIMP_TAC holba_ss [bir_exec_to_labels_triple_def] >>
      RW_TAC holba_ss [] >>
      rename1 `bir_state.bst_status = _` >>

      (* bir_is_bool_exp_env WP *)
      subgoal `bir_is_bool_exp_env bir_state.bst_environ wp` >- (
        FULL_SIMP_TAC holba_ss [
          bir_is_bool_exp_env_def, bir_is_bool_exp_def, bir_env_vars_are_initialised_def] >>
        Q.UNABBREV_TAC `wp` >>
        Q.UNABBREV_TAC `p` >>
        FULL_SIMP_TAC holba_ss [EVAL ``bir_wp_comp_wps_iter_step2_wp_entry``] >>
        FULL_SIMP_TAC holba_ss [BIR_P_exp_def] >>
        METIS_TAC []
      ) >>
      (* P => WP *)
      subgoal `bir_eval_exp wp bir_state.bst_environ = bir_val_true` >- (
        (* Not needed, but improves readibility *)
        PAT_X_TAC `bir_state.bst_pc.bpc_index = 0` >>
        PAT_X_TAC `bir_state.bst_pc.bpc_label = BL_Label "entry"` >>
        PAT_X_TAC `bir_state.bst_status = BST_Running` >>
        PAT_X_TAC `Abbrev (q = _ )` >>

        Q.ABBREV_TAC `env = bir_state.bst_environ` >>

        (* P ==> WP *)
        Q.UNDISCH_TAC `bir_eval_exp p env = bir_val_true` >>
        Q.UNABBREV_TAC `wp` >>
        Q.UNABBREV_TAC `p` >>
        PURE_REWRITE_TAC [BIR_P_exp_def, EVAL ``bir_wp_comp_wps_iter_step2_wp_entry``] >>

        Q.ABBREV_TAC `nic_x: bir_var_t = BVar "nic_x" (BType_Imm Bit32)` >>
        Q.ABBREV_TAC `nic_dead: bir_var_t = BVar "nic_dead" (BType_Imm Bit1)` >>
        Q.ABBREV_TAC `x_exp = (BExp_Den nic_x)` >>
        Q.ABBREV_TAC `dead_exp = (BExp_Den nic_dead)` >>

        (*** now we want to translate into a words expression ***)

        (** bir_equal_equiv requires some lemmas **)
        `bir_env_var_is_initialised env nic_x` by INITIALIZED_TAC >>
        `bir_env_var_is_initialised env nic_dead` by INITIALIZED_TAC >>
        `bir_env_vars_are_initialised env (bir_vars_of_exp x_exp)` by INITIALIZED_TAC >>
        `bir_env_vars_are_initialised env (bir_vars_of_exp dead_exp)` by INITIALIZED_TAC >>
        `bir_is_imm_exp x_exp` by IS_IMM_EXP_TAC >>
        `bir_is_imm_exp dead_exp` by IS_IMM_EXP_TAC >>

        Q.ABBREV_TAC `exp_0w1 = (BExp_Const (Imm1 0w))` >>
        Q.ABBREV_TAC `exp_0w32 = (BExp_Const (Imm32 0w))` >>
        `bir_env_vars_are_initialised env (bir_vars_of_exp exp_0w1)` by INITIALIZED_TAC >>
        `bir_env_vars_are_initialised env (bir_vars_of_exp exp_0w32)` by INITIALIZED_TAC >>
        `bir_is_imm_exp exp_0w1` by IS_IMM_EXP_TAC >>
        `bir_is_imm_exp exp_0w32` by IS_IMM_EXP_TAC >>

        `type_of_bir_exp dead_exp = type_of_bir_exp exp_0w1` by UNABBREV_EVAL_TAC >>
        `type_of_bir_exp    x_exp = type_of_bir_exp exp_0w32` by UNABBREV_EVAL_TAC >>

        `(  (bir_eval_exp (BExp_BinPred BIExp_Equal dead_exp exp_0w1) env = bir_val_true)
          = (bir_eval_exp dead_exp env = bir_eval_exp exp_0w1 env)
        ) /\ (
            (bir_eval_exp (BExp_BinPred BIExp_Equal x_exp exp_0w32) env = bir_val_true)
          = (bir_eval_exp x_exp env = bir_eval_exp exp_0w32 env)
        )` by METIS_TAC [bir_equal_equiv] >>

        Q.ABBREV_TAC `x_val = (bir_env_read nic_x env)` >>
        Q.ABBREV_TAC `dead_val = (bir_env_read nic_dead env)` >>
        subgoal `type_of_bir_val x_val = SOME (BType_Imm Bit32)` >- (
          unabbrev_all_tac >>
          FULL_SIMP_TAC pure_ss [type_of_bir_val_def, bir_env_read_def, bir_env_var_is_initialised_def] >>
          ASM_SIMP_TAC (srw_ss()) [] >>
          REWRITE_TAC [bir_var_type_def]
        ) >>
        subgoal `type_of_bir_val dead_val = SOME (BType_Imm Bit1)` >- (
          unabbrev_all_tac >>
          FULL_SIMP_TAC pure_ss [type_of_bir_val_def, bir_env_read_def, bir_env_var_is_initialised_def] >>
          ASM_SIMP_TAC (srw_ss()) [] >>
          REWRITE_TAC [bir_var_type_def]
        ) >>
        subgoal `?x_imm. x_val = BVal_Imm x_imm` >- (
          subgoal `type_of_bir_val x_val = SOME (BType_Imm Bit32)` >- (
            unabbrev_all_tac >>
            FULL_SIMP_TAC pure_ss [bir_env_read_def, bir_env_var_is_initialised_def] >>
            ASM_SIMP_TAC (srw_ss()) [] >>
            REWRITE_TAC [bir_var_type_def]
          ) >>
          ASM_SIMP_TAC holba_ss [bir_type_of_val_is_imm_then_exists_imm]
        ) >>
        subgoal `?dead_imm. dead_val = BVal_Imm dead_imm` >- (
          subgoal `type_of_bir_val dead_val = SOME (BType_Imm Bit1)` >- (
            unabbrev_all_tac >>
            FULL_SIMP_TAC pure_ss [bir_env_read_def, bir_env_var_is_initialised_def] >>
            ASM_SIMP_TAC (srw_ss()) [] >>
            REWRITE_TAC [bir_var_type_def]
          ) >>
          ASM_SIMP_TAC holba_ss [bir_type_of_val_is_imm_then_exists_imm]
        ) >>
        subgoal `type_of_bir_imm x_imm = Bit32` >- (
          FULL_SIMP_TAC pure_ss [type_of_bir_val_def] >>
          FULL_SIMP_TAC (srw_ss()) []
        ) >>
        subgoal `type_of_bir_imm dead_imm = Bit1` >- (
          FULL_SIMP_TAC pure_ss [type_of_bir_val_def] >>
          FULL_SIMP_TAC (srw_ss()) []
        ) >>
        Q.UNABBREV_TAC `x_val` >>
        Q.UNABBREV_TAC `dead_val` >>

        subgoal `?x_w. x_imm = Imm32 x_w` >- (
          (* TODO: That's UGLY *)
          ASSUME_TAC (SPEC ``x_imm: bir_imm_t`` bir_imm_t_nchotomy) >>
          RW_TAC holba_ss [] >>
          FULL_SIMP_TAC holba_ss [type_of_bir_imm_def]
        ) >>
        subgoal `?dead_w. dead_imm = Imm1 dead_w` >- (
          (* TODO: That's UGLY *)
          ASSUME_TAC (SPEC ``dead_imm: bir_imm_t`` bir_imm_t_nchotomy) >>
          RW_TAC holba_ss [] >>
          FULL_SIMP_TAC holba_ss [type_of_bir_imm_def]
        ) >>

        Q.UNABBREV_TAC `x_exp` >>
        Q.UNABBREV_TAC `dead_exp` >>
        Q.UNABBREV_TAC `exp_0w1` >>
        Q.UNABBREV_TAC `exp_0w32` >>
        FULL_SIMP_TAC bir_to_words_ss [] >>

        (REPEAT o PAT_X_TAC) `_` >>
        Z3_ORACLE_TAC
      ) >>
      METIS_TAC [bir_exec_to_labels_triple_def]
    )
  in
    (EVAL ``bir_wp_comp_wps_iter_step2_wp_entry``, triple_thm)
  end
    handle e => raise pp_exn_s "Failed during WP part" e

(*val goal_tm = ``!nic nic'. (NIC_P nic /\ exec_prog nic bir_prog nic') ==> NIC_Q nic nic'``;*)
val goal_thm = store_thm ( "goal_thm",
  goal_tm,
  (* 1 *)
  REPEAT STRIP_TAC >>
  `?bir_state. R nic bir_state` by METIS_TAC[R_inj_thm] >>
  `BIR_P bir_state` by METIS_TAC[b_thm] >>

  (* 2 *)
  `bir_is_bool_exp_env bir_state.bst_environ BIR_P_exp` by METIS_TAC [BIR_P_is_bool_exp_thm] >>
  `bir_eval_exp BIR_P_exp bir_state.bst_environ = bir_val_true` by METIS_TAC [eval_BIR_P_is_true_thm] >>

  Q.UNDISCH_TAC `R nic bir_state` >>
  SIMP_TAC pure_ss [R_def] >>
  REPEAT STRIP_TAC >>

  subgoal `bir_env_vars_are_initialised bir_state.bst_environ (bir_vars_of_program bir_prog)` >- (
    (* TODO: Remove pred_setSimps.PRED_SET_ss if it gets added to VARS_OF_PROG_ss *)
    SIMP_TAC (pure_ss++VARS_OF_PROG_ss++pred_setSimps.PRED_SET_ss) [bir_prog_def] >>
    RW_TAC holba_ss [bir_env_vars_are_initialised_def] >> (
      FULL_SIMP_TAC holba_ss [
        bir_env_var_is_initialised_def, bir_env_lookup_def,
        w2bval32_def, bool2bval_def, bool2imm1_REWR, BType_Bool_def]
    )
  ) >>

  (drule o SIMP_RULE holba_ss [bir_exec_to_labels_triple_def]) triple_thm >>
  ASM_SIMP_TAC holba_ss [] >>
  RW_TAC holba_ss [] >| [
    rename1 `bir_is_bool_exp_env bir_state'.bst_environ BIR_Q_exp`
    ,
    rename1 `bir_state'.bst_status = BST_AssumptionViolated` >>
    (* FIXME: Remove the cheat related to BST_AssumptionViolated *)
    (* we just need to use: !stmt. stmt <> assume ==> BST_AssumptionViolated impossible *)
    (* this should be easy, but I need the thm from HolBA *)
    cheat
  ] >>

  (* 3 *)
  `BIR_Q bir_state'` by METIS_TAC [BIR_Q_def, bir_eval_bool_exp_LEMMA] >>

  (* 4 *)
  `R nic bir_state` by FULL_SIMP_TAC holba_ss [R_def] >>
  `R nic' bir_state'` by METIS_TAC [eq_thm] >>

  (* 5 *)
  METIS_TAC [d_thm]
);

(* Print interesting theorems *)
if (!Globals.interactive) then let
  fun thm_to_ppstring thm = (ppstring pp_thm) thm
  fun pprint_thm thm = ((print o thm_to_ppstring) thm; print "\n")
  fun pprint_named_thm name thm = (print (name ^ ":\n"); pprint_thm thm)
  fun pprint_def name = pprint_named_thm name (DB.fetch "-" name)

  val _ = pprint_named_thm "bir_prog_def" bir_prog_def
  val _ = pprint_named_thm "R_def" R_def
  val _ = pprint_named_thm "R_inj_thm" R_inj_thm
  val _ = pprint_named_thm "eq_thm" eq_thm
  val _ = pprint_named_thm "NIC_P_def" NIC_P_def
  val _ = pprint_named_thm "NIC_Q_def" NIC_Q_def
  val _ = pprint_named_thm "BIR_P_def" BIR_P_def
  val _ = pprint_named_thm "BIR_Q_def" BIR_Q_def
  val _ = pprint_named_thm "BIR_P_exp_def" BIR_P_exp_def
  val _ = pprint_named_thm "BIR_Q_exp_def" BIR_Q_exp_def
  val _ = pprint_named_thm "b_thm" b_thm
  val _ = pprint_named_thm "d_thm" d_thm
  val _ = pprint_named_thm "wp_thm" wp_thm
  val _ = pprint_named_thm "triple_thm" triple_thm
  val _ = pprint_named_thm "goal_thm" goal_thm
in () end else ();

val _ = export_theory ();

