open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_imm_expTheory
open bir_immSyntax bir_programTheory wordsTheory
open bir_auxiliaryTheory
open bir_mem_expTheory bir_bool_expTheory
open bir_program_env_orderTheory
open bir_program_blocksTheory
open bir_temp_varsTheory
open bir_exp_liftingTheory
open bir_lifting_machinesTheory
open bir_interval_expTheory
open bir_update_blockTheory
open bir_lifting_machinesLib
open pred_setTheory

(* This theory defines what it means for a block and a whole program
   to be corresponding to a machine instruction *)

val _ = new_theory "bir_inst_lifting";


(*****************************)
(* Unchanged memory interval *)
(*****************************)

val bmr_ms_mem_unchanged_def = Define `bmr_ms_mem_unchanged r ms ms' i <=>
  (!a. WI_MEM a i ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a))`;


val bmr_ms_mem_contains_UNCHANGED = store_thm ("bmr_ms_mem_contains_UNCHANGED",
``!r ms ms' i ba vs.
  WF_bmr_ms_mem_contains (ba, vs) ==>
  bmr_ms_mem_unchanged r ms ms' i ==>
  WI_is_sub (bmr_ms_mem_contains_interval (ba, vs)) i ==>

  (bmr_ms_mem_contains r ms (ba, vs) <=>
   bmr_ms_mem_contains r ms' (ba, vs))``,

SIMP_TAC std_ss [bmr_ms_mem_contains_def, WI_is_sub_def,
  bmr_ms_mem_contains_interval_def,
  WI_MEM_WI_size, WF_bmr_ms_mem_contains_def,
  bmr_ms_mem_unchanged_def, w2n_n2w] >>
REPEAT STRIP_TAC >>
`!a. MEM a (WI_ELEM_LIST ba (LENGTH vs)) ==>
     (bmr_mem_lf r ms' a = bmr_mem_lf r ms a)` by METIS_TAC[] >>
POP_ASSUM MP_TAC >>
REPEAT (POP_ASSUM (K ALL_TAC)) >>
Q.ID_SPEC_TAC `ba` >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bmr_ms_mem_contains_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [bmr_ms_mem_contains_def,
  WI_ELEM_LIST_def, DISJ_IMP_THM, FORALL_AND_THM]);



(***************************************************)
(* Lifting a machine instruction to a single block *)
(***************************************************)

val bir_is_lifted_inst_block_def = Define `
  bir_is_lifted_inst_block
    (* machine description *)
    (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t)


    (* A condition allowing is to get extra information into our reasoning. It can
       say for example which of the theorems of produced by the step theorem we are
       dealing with and just assume at the meta level some of it's preconditions
       instead of asserting them in BIR. This allows to discard them later by looking
       at the control flow of a larger bir program containing the block. *)
    (ms_case_cond : 'ms -> bool)

    (* The label to start executing. This may not always be the label of the block,
       but it corresponds to the PC of the machine state. A machine step might be translated
       to multiple bir blocks. Only the entry block has a label corresponding to the
       machine PC. Other blocks are selected by this entry as appropriate. *)
    l

    (* A region of memory not touched by the execution. Usually this is the part where
       the program code is stored. *)
    mu

    (* The code for the machine instruction stored somewhere (usually at the PC) stored
       in mem *)
    mm

    (* BIR Block *)
    (bl :'o bir_block_t)

    <=>

  (* Parameters are sensible *)
  (WI_wfe mu /\ WF_bmr_ms_mem_contains mm /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu) /\

  (!ms bs (p : 'o bir_program_t) c lo bs'.

    (* The extra condition holds *)
    ms_case_cond ms ==>

    (* The machine state and the bir state are related *)
    (bmr_rel r bs ms) ==>

    (* The PC points to where we expect *)
    (bs.bst_pc = bir_block_pc l) ==>

    (* At this location in memory the expected instruction code is found *)
    bmr_ms_mem_contains r ms mm ==>

    (* The bir state is not terminated yet *)
    ~(bir_state_is_terminated bs) ==>

    (* We execute in BIR and reach a new bir-state bs' *)
    (bir_exec_block p bl bs = (lo, c, bs')) ==>

    (* We did not violate any assertions during the execution in BIR *)
    ~(bs'.bst_status = BST_AssertionViolated) ==>


    (* Then a related step is taking by the machine, i.e.
       a next state of the machine exists that is related to our
       new bir state and the protected region of memory has really not been touched. *)
    (?ms'. (r.bmr_step_fun ms = SOME ms') /\
           (bmr_ms_mem_unchanged r ms ms' mu) /\
           (bmr_rel r bs' ms')))`;




(**********************************************)
(* Deriving bir_is_lifted_inst_block theorems *)
(**********************************************)

(* The main functionality of the instruction lifter to lift single machine instructions
   and as justification provide bir_is_lifted_inst_block theorems. These are
   later combined to have a connection for whole programs instead of single blocks,
   but this is comparably simple and non-machine dependent.

   So, given some step-theorem describing the behaviour of our machine, that
   describes the behaviour of one step of a machine usually using the assumptions that

   - some instr is stored at the PC pointer in memory
   - PC has a certain value
   - some extra conditions hold

   and further given

   - a machine description "r"
   - a condition "ms_case_cond" we may assume from the calling context
   - a region of memory we should not touch "mu"

   we want to derive

   - a memory mapping "mm" that describes the instruction stored in mem
   - a label "l" corresponding to the PC
   - and most importantly a bir-block "bl" such that

   bir_is_lifted_inst_block r ms_case_cond l mu mm bl

   holds.

   To do this, we want to do as little real work as possible at runtime.
   So preproved theorems about assert-update-blocks and the record r are
   used. The theorem "bir_is_lifted_inst_block_COMPUTE" captures at a high
   level of abstraction how to do such a computation.

   However, "bir_is_lifted_inst_block_COMPUTE" is not how one would really
   like to reason automatically. It is at a high, intuitive level of abstraction.
   Many properties esp. things like

   - variable names being well-formed
   - var names being distinct
   - vars are declared properly
   ...

   are demanded by the preconditions of "bir_is_lifted_inst_block_COMPUTE"
   explicitly, while they could be derived by e.g. well-formedness properties
   of the machine lifting record "r". So, there is an
   optimised version "bir_is_lifted_inst_block_COMPUTE_OPTIMISED".
   The idea is the same as for ""bir_is_lifted_inst_block_COMPUTE". However,
   not the preconditions are streamlined for efficient instantiation in the
   automation provided by bir_inst_liftingLib.

   Both for "bir_is_lifted_inst_block_COMPUTE" and
   "bir_is_lifted_inst_block_COMPUTE_OPTIMISED" many auxiliary definitions are
   introduced.
*)


(*-----------------------*)
(* Auxiliary definitions *)
(*-----------------------*)

val bir_is_lifted_inst_block_COMPUTE_ms'_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_ms'_COND r ms al_step ms' <=>
     (* We can compute the next machine state using extra assumptions in al_step *)
     ((EVERY (\a. bir_assert_desc_value a) al_step) ==>
      (r.bmr_step_fun ms = SOME ms')) /\

     (* This machine step satisfies the machine state invariants *)
     ((EVERY (\a. bir_assert_desc_value a) al_step) ==>
      r.bmr_extra ms')`


val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_imm_ups_COND r ms ms' imm_ups updates <=>

     (* For every immediate value mapped, we checked, whether it is changed or not *)
     (MAP FST imm_ups = r.bmr_imms) /\
     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
             (lf ms' = lf ms) /\ (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)) /\
             (bir_var_name v <> bir_var_name (bir_updateB_desc_temp_var up)))) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (lf ms' = res) /\ (?up. MEM up updates /\ (bir_updateB_desc_var up = v) /\
                                   (bir_updateB_desc_value up = BVal_Imm res)))`



val bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_al_mem_COND r mu ms ms' al_mem <=>

     (* Only explicitly listed memory locations are updated and these are
        outside the unchanged region *)
     ?mem_chs.
     (!a. ~(MEM a mem_chs) ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a)) /\
     (EVERY (\a. bir_assert_desc_value a) al_mem ==>
      (!a. (MEM a mem_chs) ==> ~(WI_MEM a mu)))`;


val bir_is_lifted_inst_block_COMPUTE_mem_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_mem_COND r bs ms ms' mem_up updates <=>
     (* Memory update sensible *)
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) => (
             (lf ms' = lf ms) /\ (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)) /\
             (bir_var_name v <> bir_var_name (bir_updateB_desc_temp_var up))))
       | (SOME res, BMLM v lf) =>
              (lf ms' = res) /\ (?up.

              MEM up updates /\ (bir_updateB_desc_var up = v) /\
              (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp up) (BLV_Mem res))))`


val bir_is_lifted_inst_block_COMPUTE_eup_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_eup_COND r eup ms'  <=>
     (* EUP sensible *)
     (!var. (bir_updateE_desc_var eup = SOME var) ==>
            ((!v lf. (MEM (BMLI v lf) r.bmr_imms ==>
                    (bir_var_name var) <> (bir_var_name v))) /\
            (case r.bmr_mem of
               | (BMLM v lf) => (bir_var_name var) <> (bir_var_name v)))) /\
     (bir_updateE_SEM eup = BUpdateValE_Jmp (BL_Address (bmr_pc_lf r ms')))`;



(*-------------*)
(* The theorem *)
(*-------------*)

val bir_is_lifted_inst_block_COMPUTE = store_thm ("bir_is_lifted_inst_block_COMPUTE",
``!r bl ms_case_cond l mm mu l'.

  (WI_wfe mu /\ WF_bmr_ms_mem_contains mm /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu) ==>
  (!ms bs. ?ms' al_mem al_step imm_ups mem_up eup updates.

     bmr_rel r bs ms ==>  ms_case_cond ms ==> bmr_ms_mem_contains r ms mm ==> (BL_Address (bmr_pc_lf r ms) = l) ==> (

     (* ms' is reached and we need only extra assertions al_step to
        discard preconds of the step theorem. To instantiate this,
        the automation needs to come up with ms' and al_step *)
     bir_is_lifted_inst_block_COMPUTE_ms'_COND r ms al_step ms' /\

     (* All relevant immediate fields are either unchanged or taken care of
        by updates. Unchanged ones are not modified. To do this, the SML code should
        generate imm_ups and later with other information use it to generate updates. *)
     bir_is_lifted_inst_block_COMPUTE_imm_ups_COND r ms ms' imm_ups updates /\

     (* The memory is only changed in a finite number of locations. These are outside region
        mu and the extra assertions al_mem are all we need to show this. The SML
        code should generate al_mem. *)
     bir_is_lifted_inst_block_COMPUTE_al_mem_COND r mu ms ms' al_mem /\

     (* We take care of potential memory changes via an update. The ML code
        should use it to generate mem_up. *)
     bir_is_lifted_inst_block_COMPUTE_mem_COND r bs ms ms' mem_up updates /\

     (* The update of the PC is sensible. This should generate EUP except the
        flag whether a temp var is needed. *)
     bir_is_lifted_inst_block_COMPUTE_eup_COND r eup ms' /\

     (* Everything fits with respect to temps etc. *)
     EVERY (bir_assert_desc_OK bs.bst_environ) (al_mem++al_step) /\
     bir_update_block_desc_OK bs.bst_environ eup updates /\

     (* The block does not depend on the actual values for the state, but just
        the expressions. So, bl should be independent of the actual state. *)
     (bl = (bir_update_assert_block l' (al_mem++al_step) eup updates)))) ==>
  bir_is_lifted_inst_block (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) ms_case_cond l mu mm (bl :'o bir_block_t)
``,

SIMP_TAC std_ss [bir_is_lifted_inst_block_def] >>
REPEAT STRIP_TAC >>
`l = BL_Address (bmr_pc_lf r ms)` by (
  Cases_on `r.bmr_pc` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_rel_def, bir_machine_lifted_pc_def,
    bir_block_pc_def, bmr_pc_lf_def, bir_state_is_terminated_def]
) >>
Q.PAT_X_ASSUM `!ms bs. _` (MP_TAC o Q.SPECL [`ms`, `bs`]) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>
`bir_env_order bs.bst_environ bs'.bst_environ` by
   METIS_TAC[pairTheory.SND, bir_exec_block_ENV_ORDER] >>

MP_TAC (Q.SPECL [`bs`, `l'`, `eup`, `p`, `updates`, `bl`, `al_mem++al_step`]
   (INST_TYPE [``:'a`` |-> ``:'o``] bir_update_assert_block_SEM)) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >>
`(r.bmr_step_fun ms = SOME ms') /\ (r.bmr_extra ms')` by (
   FULL_SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_ms'_COND_def]
) >>
FULL_SIMP_TAC list_ss [bmr_rel_def] >>

`EVERY (\i. bir_machine_lifted_imm i bs' ms') r.bmr_imms` by (
   FULL_SIMP_TAC std_ss [EVERY_MEM, bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_def] >>
   REPEAT STRIP_TAC >>
   `bir_machine_lifted_imm i bs ms` by METIS_TAC[] >>
   `?vo. MEM (i, vo) imm_ups` by (
      Q.PAT_X_ASSUM `_ = r.bmr_imms` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [MEM_MAP] >>
      METIS_TAC[pairTheory.PAIR]
   ) >>
   Cases_on `i` >> rename1 `BMLI v lf` >>
   Cases_on `vo` >- (
      `(lf ms' = lf ms)` by METIS_TAC[] >>
      FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_def, AND_IMP_INTRO] >>
      `bir_env_read v bs'.bst_environ = bir_env_read v bs.bst_environ`
         suffices_by METIS_TAC [bir_env_var_is_declared_ORDER] >>
      MATCH_MP_TAC bir_env_read_EQ_lookup_IMPL >>
      Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
      METIS_TAC[bir_is_lifted_inst_block_COMPUTE_eup_COND_def]
   ) >>

   rename1 `MEM (_, SOME res) imm_ups` >>
   `(lf ms' = res) /\
    (?up.
       MEM up updates /\ (bir_updateB_desc_var up = v) /\
       (bir_updateB_desc_value up = BVal_Imm res))` by METIS_TAC[] >>

   FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_def, AND_IMP_INTRO] >>
   Tactical.REVERSE CONJ_TAC >- METIS_TAC[bir_env_var_is_declared_ORDER] >>

   Q.PAT_X_ASSUM `!up. MEM up updates ==> _` (MP_TAC o Q.SPEC `up`) >>
   ASM_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm]
) >>

`bmr_ms_mem_unchanged r ms ms' mu` by (
  FULL_SIMP_TAC std_ss [bmr_ms_mem_unchanged_def,
     bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def] >>
  METIS_TAC[]
) >>

`bir_machine_lifted_mem r.bmr_mem bs' ms'` by (
  Cases_on `r.bmr_mem`  >> rename1 `BMLM mv mlf` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bir_machine_lifted_mem_def,
    pairTheory.pair_case_thm, AND_IMP_INTRO,
    bir_is_lifted_inst_block_COMPUTE_mem_COND_def] >>
  Cases_on `mem_up` >- (
    FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
    `bir_env_read mv bs'.bst_environ = bir_env_read mv bs.bst_environ`
       suffices_by METIS_TAC [bir_env_var_is_declared_ORDER] >>
    MATCH_MP_TAC bir_env_read_EQ_lookup_IMPL >>
    Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
    FULL_SIMP_TAC (std_ss++bmr_ss) [EVERY_MEM, bir_is_lifted_inst_block_COMPUTE_eup_COND_def] >>
    METIS_TAC[]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  rename1 `mlf ms' = mem_fun'` >>
  `bir_updateB_desc_OK bs.bst_environ up` by (
     FULL_SIMP_TAC std_ss [bir_update_block_desc_OK_def,
       bir_update_blockB_desc_OK_def, EVERY_MEM]
  ) >>
  `(bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) bs'.bst_environ =
    SOME (bir_var_type (bir_updateB_desc_var up),
          SOME (bir_updateB_desc_value up)))` by (
     FULL_SIMP_TAC std_ss [EVERY_MEM]
  ) >>
  Cases_on `up` >>
  rename1 `BUpdateDescB up_v up_e up_res up_temp` >>
  FULL_SIMP_TAC std_ss [bir_is_lifted_exp_def,
    bir_is_lifted_mem_exp_def, bir_updateB_desc_OK_def,
    bir_updateB_desc_exp_def, bir_updateB_desc_var_def] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  Q.EXISTS_TAC `mem_n'` >> ASM_REWRITE_TAC[] >>
  Tactical.REVERSE CONJ_TAC >- METIS_TAC[bir_env_var_is_declared_ORDER] >>

  ASM_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm,
    bir_updateB_desc_value_def]
) >>

`bir_machine_lifted_pc r.bmr_pc bs' ms'` by (
  Cases_on `r.bmr_pc` >> rename1 `BMLPC v_pc v_pc_cons pc_lf` >>
  FULL_SIMP_TAC std_ss [bir_machine_lifted_pc_def,
     bir_is_lifted_inst_block_COMPUTE_eup_COND_def] >>
  `bir_env_var_is_declared bs'.bst_environ v_pc /\
   bir_env_var_is_declared bs'.bst_environ v_pc_cons` by
      METIS_TAC[bir_env_var_is_declared_ORDER] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++bmr_ss) [BUpdateValE_SEM_def,
    bir_state_pc_is_at_label_def, bmr_pc_lf_def] >>
  METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss []);



(**********************************************************)
(* Efficiently deriving bir_is_lifted_inst_block theorems *)
(**********************************************************)

(* The lemma bir_is_lifted_inst_block_COMPUTE is worded in such a way that
   it is comparably easy to understand for humans. The actual SML code does not need to
   (and should) not follow it literally though.

   Please see above for details. *)


(*-----------------------*)
(* Auxiliary definitions *)
(*-----------------------*)

val bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_def = Define
  `bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK r bs ms al_step ms' <=>
   (bir_is_lifted_inst_block_COMPUTE_ms'_COND r ms al_step ms' /\
    EVERY (bir_assert_desc_OK bs.bst_environ) al_step)`;

val bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def = Define
  `bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK r mu bs ms ms' al_mem <=>
   (bir_is_lifted_inst_block_COMPUTE_al_mem_COND r mu ms ms' al_mem /\
    EVERY (bir_assert_desc_OK bs.bst_environ) al_mem)`;


val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def = Define
  `bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups <=>

     (MAP FST imm_ups = r.bmr_imms) /\
     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
                     (lf ms' = lf ms)) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (lf ms' = res))`;

val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES_def = Define
  `bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES r ms ms' imm_ups updates <=>

     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
             (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)))) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (?up. MEM up updates /\ (bir_updateB_desc_var up = v) /\
                 (bir_updateB_desc_value up = BVal_Imm res)))`


val bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES_def = Define
  `bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES r bs ms ms' mem_up updates <=>
     (* Memory update sensible *)
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) =>
             (!up. MEM up updates ==>
                   (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)))
       | (SOME res, BMLM v lf) =>
              (?up.
              MEM up updates /\ (bir_updateB_desc_var up = v) /\
              (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp up) (BLV_Mem res))))`;

val bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def = Define
  `bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' mem_up <=>
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) => (
             (lf ms' = lf ms))
       | (SOME res, BMLM v lf) =>
              (lf ms' = res))`;


val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def = Define
  `bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms'  <=>
     bir_updateE_desc_OK bs.bst_environ eup /\

     (case (bir_updateE_desc_var eup) of NONE => T
       | SOME var => case r.bmr_pc of BMLPC v_pc v_pc_cond _ =>
         ((var = v_pc) \/ (var = v_pc_cond))) /\

     (bir_updateE_SEM eup = BUpdateValE_Jmp (BL_Address (bmr_pc_lf r ms')))`;


val bir_is_lifted_inst_block_COMPUTE_updates_FULL_def = Define
  `bir_is_lifted_inst_block_COMPUTE_updates_FULL
      (r: ('a, 'b, 'c) bir_lifting_machine_rec_t) bs
      (mem_up : ('a word -> 'b word) option)
      (imm_ups :('c bir_machine_lifted_imm_t # bir_imm_t option) list)
      (eup :bir_updateE_desc_t) (eup_temp :bool) updates =

     ?updates_imm updates_mem.

     (* imm_ups covered *)
     ((MAP (\up. (bir_updateB_desc_var up, bir_updateB_desc_value up)) updates_imm) =
      (MAP (\x. (case x of | (BMLI v _, SOME r) => (v, BVal_Imm r)))
        (FILTER (\x. IS_SOME (SND x)) imm_ups))) /\

     (* mem_up covered *)
     (case mem_up of NONE => (updates_mem = []) | SOME res =>
       (?upd_mem. (updates_mem = [upd_mem]) /\
           (bir_updateB_desc_var upd_mem = bmr_mem_var r) /\
           (bir_updateB_desc_value upd_mem =
             (bir_eval_exp (bir_updateB_desc_exp upd_mem) bs.bst_environ)) /\
           (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp upd_mem)
             (BLV_Mem res)))) /\

     (* Nothing else updated *)
     (PERM updates (updates_imm ++ updates_mem)) /\

     (* imm_ups are lifted properly *)
     (!var e v use_temp.
            MEM (BUpdateDescB var e (BVal_Imm v) use_temp) updates_imm ==>
            bir_is_lifted_imm_exp bs.bst_environ e v) /\

     (* Vars fit *)
     (!i j var.
        i < LENGTH updates /\ j < i /\
        var IN bir_vars_of_exp (bir_updateB_desc_exp (EL i updates)) ==>
        bir_var_name var <>
        bir_var_name (bir_updateB_desc_temp_var (EL j updates))) /\

     (!v up v'.
        eup_temp ==>
        (bir_updateE_desc_var eup = SOME v) ==>
        MEM up (updates_imm ++ updates_mem) ==>
        v' IN  bir_vars_of_exp (bir_updateB_desc_exp up) ==>
        bir_var_name v <> bir_var_name v') /\

     (!v e up v'.
        (~eup_temp \/ (bir_updateE_desc_var eup = NONE)) ==>
        (bir_updateE_desc_exp eup = SOME e) ==>
        v IN bir_vars_of_exp e ==>
        MEM up (updates_imm ++ updates_mem) ==>
        v' IN {bir_updateB_desc_temp_var up; bir_updateB_desc_var up} ==>
        bir_var_name v <> bir_var_name v')`;


val bir_is_lifted_inst_block_COMPUTE_block_def = Define `
  bir_is_lifted_inst_block_COMPUTE_block l' al_mem al_step eup_temp eup updates =
  bir_update_assert_block l' (al_mem ++ al_step)
                 (if eup_temp then eup
                  else bir_updateE_desc_remove_var eup) updates`;

val bir_is_lifted_inst_block_COMPUTE_precond_def = Define
  `bir_is_lifted_inst_block_COMPUTE_precond r bs ms l mu mm bl l' ms_case_cond ms'
     al_step imm_ups mem_up al_mem eup eup_temp updates <=> (

     bmr_rel r bs ms ==>
     ms_case_cond ms ==>
     bmr_ms_mem_contains r ms mm ==>
     (BL_Address (bmr_pc_lf r ms) = l) ==> (
     bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK r bs ms al_step ms' /\
     bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups /\
     bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' mem_up /\
     bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK r mu bs ms ms' al_mem /\
     bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms' /\
     bir_is_lifted_inst_block_COMPUTE_updates_FULL r bs mem_up imm_ups eup eup_temp updates /\
     (bl = bir_is_lifted_inst_block_COMPUTE_block l' al_mem al_step eup_temp eup updates)))`;

val bir_is_lifted_inst_block_COMPUTE_mm_WF_def = Define
  `bir_is_lifted_inst_block_COMPUTE_mm_WF mu mm <=>
    ((WF_bmr_ms_mem_contains mm) /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu)`;



(*-----------------------*)
(* Proving optimised thm *)
(*-----------------------*)

val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_THM = prove (
``!r ms ms' imm_ups updates. bmr_ok r ==>
   (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND r ms ms' imm_ups updates <=>
    (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups /\
     bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES r ms ms' imm_ups updates))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES_def,
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def,
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_def,
  IMP_CONJ_THM, FORALL_AND_THM] >>
REPEAT STRIP_TAC >>
`bir_var_name v <> bir_var_name (bir_updateB_desc_var up)` by METIS_TAC[] >>
Cases_on `up` >> rename1 `BUpdateDescB v' e res use_temp` >>
Cases_on `use_temp` >> (
  FULL_SIMP_TAC std_ss [bir_updateB_desc_var_def, bir_updateB_desc_temp_var_def,
    bir_temp_var_REWRS]
) >>
`bir_machine_lifted_imm_OK (BMLI v lf)` by (
  Q.PAT_X_ASSUM `_ = r.bmr_imms` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC std_ss [bmr_ok_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  METIS_TAC[pairTheory.FST]
) >>
FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def] >>
METIS_TAC[bir_is_temp_var_name_REWR]);



val bir_is_lifted_inst_block_COMPUTE_mem_COND_THM = prove (
``!r bs ms ms' mem_up updates. bmr_ok r ==>
   (bir_is_lifted_inst_block_COMPUTE_mem_COND r bs ms ms' mem_up updates <=>
    (bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' mem_up /\
     bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES r bs ms ms' mem_up updates))``,

GEN_TAC >>
Cases_on `r.bmr_mem` >> rename1 `BMLM mv lf` >>
ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``: 'a option``]) [
  bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES_def,
  bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def,
  bir_is_lifted_inst_block_COMPUTE_mem_COND_def,
  IMP_CONJ_THM, FORALL_AND_THM, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >>
`bir_var_name mv <> bir_var_name (bir_updateB_desc_var up)` by METIS_TAC[] >>
Cases_on `up` >> rename1 `BUpdateDescB v' e res use_temp` >>
Cases_on `use_temp` >> (
  FULL_SIMP_TAC std_ss [bir_updateB_desc_var_def, bir_updateB_desc_temp_var_def,
    bir_temp_var_REWRS]
) >>
REV_FULL_SIMP_TAC std_ss [bmr_ok_def, bir_machine_lifted_mem_OK_def] >>
METIS_TAC[bir_is_temp_var_name_REWR]);


val bir_is_lifted_inst_block_COMPUTE_eup_COND_remove_var = prove (
``!r eup eup_temp ms'.
bir_is_lifted_inst_block_COMPUTE_eup_COND r eup ms' ==>
bir_is_lifted_inst_block_COMPUTE_eup_COND r
  (if eup_temp then eup else bir_updateE_desc_remove_var eup) ms'``,

Cases_on `eup_temp` >> SIMP_TAC std_ss [] >>
SIMP_TAC (std_ss) [bir_is_lifted_inst_block_COMPUTE_eup_COND_def,
   bir_updateE_desc_remove_var_REWRS]);


val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_THM = prove (
``!r bs eup ms'.
    bmr_ok r ==>
    bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms' ==>
    bir_is_lifted_inst_block_COMPUTE_eup_COND r eup ms'``,

REPEAT GEN_TAC >>
FULL_SIMP_TAC list_ss [bmr_ok_def, bmr_varnames_distinct_def,
  bir_is_lifted_inst_block_COMPUTE_eup_COND_def, ALL_DISTINCT_APPEND,
  bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bmr_temp_vars_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
NTAC 4 STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `pc_vars = (case r.bmr_pc of BMLPC v1 v2 v4 => [v1; v2])` >>
`MEM var pc_vars` by (
  Q.UNABBREV_TAC `pc_vars` >>
  Cases_on `r.bmr_pc` >>
  FULL_SIMP_TAC (list_ss++bmr_ss) []
) >>
REPEAT STRIP_TAC >- (
  `MEM v (bmr_vars r)` suffices_by METIS_TAC[] >>
  ASM_SIMP_TAC (list_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [
     bmr_vars_def, MEM_MAP] >>
  METIS_TAC[]
) >>
Cases_on `r.bmr_mem` >> rename1 `BMLM mv lf_mem` >>
FULL_SIMP_TAC (std_ss++bmr_ss) [] >>
`MEM mv (bmr_vars r)` suffices_by METIS_TAC[] >>
FULL_SIMP_TAC (list_ss++bmr_ss) [bmr_vars_def]);



val bir_is_lifted_inst_block_COMPUTE_updates_FULL_THM = prove (
``!r bs ms ms' mem_up imm_ups eup eup_temp updates.
     bmr_ok r ==>
     bmr_rel r bs ms ==>
     bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups ==>
     bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms' ==>

     bir_is_lifted_inst_block_COMPUTE_updates_FULL r bs mem_up imm_ups eup eup_temp updates ==>

     (bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES r bs ms ms' mem_up updates /\
      bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES r ms ms' imm_ups updates /\
      bir_update_block_desc_OK bs.bst_environ (if eup_temp then eup else bir_updateE_desc_remove_var eup) updates)``,

REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_def] >>
`!upd. MEM upd updates_imm ==>
       (?lf i. (bir_updateB_desc_value upd = BVal_Imm i) /\
               MEM (BMLI (bir_updateB_desc_var upd) lf, SOME i) imm_ups)` by (
  REPEAT STRIP_TAC >>
  `MEM (bir_updateB_desc_var upd, bir_updateB_desc_value upd)
      (MAP (\up.(bir_updateB_desc_var up,bir_updateB_desc_value up))
      updates_imm)` by (
    FULL_SIMP_TAC std_ss [MEM_MAP] >> METIS_TAC[]
  ) >>
  POP_ASSUM MP_TAC >>
  ASM_REWRITE_TAC[] >>
  SIMP_TAC (list_ss++QI_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``])
    [MEM_MAP, MEM_FILTER, pairTheory.pair_case_thm]
) >>
`!upd. MEM upd updates_imm ==>
       (?lf. MEM (BMLI (bir_updateB_desc_var upd) lf) r.bmr_imms)` by (
   REPEAT STRIP_TAC >>
   FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def] >>
   METIS_TAC[MEM_MAP, pairTheory.FST]
) >>
`!up. MEM up updates <=> MEM up (updates_imm ++ updates_mem)` by
   METIS_TAC[sortingTheory.MEM_PERM] >>
Cases_on `r.bmr_mem` >> rename1 `BMLM mem_v mem_lf` >>

`MEM mem_v (bmr_vars r)` by (
  FULL_SIMP_TAC (list_ss++bmr_ss) [bmr_vars_def]
) >>

`!up.
  MEM up updates_imm ==>
  (MEM (bir_updateB_desc_var up) (bmr_vars r) /\
  (bir_var_name mem_v <> bir_var_name (bir_updateB_desc_var up)))` by (

  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `bmr_ok r` MP_TAC >>
  ASM_SIMP_TAC (list_ss++bmr_ss) [bmr_ok_def, bmr_varnames_distinct_def, ALL_DISTINCT_APPEND, bmr_vars_def, MAP_MAP_o, combinTheory.o_DEF] >>
  REPEAT STRIP_TAC >>
  `?lf. MEM (BMLI (bir_updateB_desc_var up) lf) r.bmr_imms` by METIS_TAC[] >>
  SIMP_TAC (std_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [
    MEM_MAP] >>
  METIS_TAC[]
) >>

REPEAT STRIP_TAC >- (
  ASM_SIMP_TAC (std_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES_def,
    pairTheory.pair_case_thm] >>
  Tactical.REVERSE (Cases_on `mem_up`) >> (
    FULL_SIMP_TAC (list_ss++bmr_ss) [bmr_mem_var_def]
  ) >>
  METIS_TAC[]
) >- (
  ASM_SIMP_TAC (std_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES_def,
    pairTheory.pair_case_thm] >>

  Q.PAT_X_ASSUM `bmr_ok r` MP_TAC >>
  ASM_SIMP_TAC (list_ss++bmr_ss) [bmr_ok_def, bmr_varnames_distinct_def, ALL_DISTINCT_APPEND, bmr_vars_def, MAP_MAP_o, combinTheory.o_DEF] >>
  `r.bmr_imms = MAP FST imm_ups` by
    FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def] >>
  REPEAT STRIP_TAC >- (
    `?n1. n1 < LENGTH imm_ups /\ (EL n1 imm_ups = (BMLI v lf,NONE))` by METIS_TAC[MEM_EL] >>
    `?n2 lf' i. n2 < LENGTH imm_ups /\
                (EL n2 imm_ups = (BMLI (bir_updateB_desc_var up) lf', SOME i))` by
       METIS_TAC[MEM_EL] >>
    `n1 <> n2` by (
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss []
    ) >>
    Q.ABBREV_TAC `vs_imms = (MAP (\i. bir_var_name (case i of BMLI v v2 => v)) r.bmr_imms)` >>
    `LENGTH vs_imms = LENGTH imm_ups` by (
       Q.UNABBREV_TAC `vs_imms` >> FULL_SIMP_TAC list_ss []) >>
    `(EL n1 vs_imms = bir_var_name v) /\
     (EL n2 vs_imms = bir_var_name v)` by (
       Q.UNABBREV_TAC `vs_imms` >>
       FULL_SIMP_TAC (list_ss++bmr_ss) [EL_MAP]
    ) >>
    METIS_TAC[EL_ALL_DISTINCT_EL_EQ]
  ) >- (
    Cases_on `mem_up` >> REV_FULL_SIMP_TAC list_ss[] >>
    REV_FULL_SIMP_TAC (list_ss++bmr_ss) [bmr_mem_var_def] >>
    REPEAT (BasicProvers.VAR_EQ_TAC) >>
    FULL_SIMP_TAC (list_ss++bmr_ss++QI_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [MEM_MAP] >>
    METIS_TAC[]
  ) >- (
    `MEM (v, BVal_Imm res) (MAP (\up. (bir_updateB_desc_var up,bir_updateB_desc_value up))
         updates_imm)` by (
      ASM_REWRITE_TAC[] >>
      ASM_SIMP_TAC (list_ss++QI_ss++bir_TYPES_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [MEM_MAP, MEM_FILTER, pairTheory.pair_case_thm]
    ) >>
    POP_ASSUM MP_TAC >>
    SIMP_TAC std_ss [MEM_MAP] >>
    METIS_TAC[]
  )
) >>

SIMP_TAC std_ss [bir_update_block_desc_OK_def, bir_update_blockB_desc_OK_def] >>

`bir_updateE_desc_OK bs.bst_environ
  (if eup_temp then eup else bir_updateE_desc_remove_var eup)` by (
  FULL_SIMP_TAC (std_ss) [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def] >>
  Cases_on `eup_temp` >> (
    ASM_SIMP_TAC std_ss [bir_updateE_desc_OK_remove_var]
  )
) >>

`EVERY (bir_updateB_desc_OK bs.bst_environ) updates` by (
  ASM_SIMP_TAC list_ss [EVERY_MEM] >>
  Cases >> rename1 `BUpdateDescB v e res use_temp` >>
  STRIP_TAC >- (
    `?i. res = BVal_Imm i` by METIS_TAC[bir_updateB_desc_value_def] >>
    `bir_is_lifted_imm_exp bs.bst_environ e i` by METIS_TAC[] >>

    FULL_SIMP_TAC std_ss [bir_updateB_desc_OK_def, bir_is_lifted_imm_exp_def] >>
    `?lf. MEM (BMLI v lf, SOME i) imm_ups` by METIS_TAC[bir_updateB_desc_value_def,
       bir_updateB_desc_var_def, bir_val_t_11] >>

    FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def] >>
    `lf ms' = i` by METIS_TAC[] >>
    `MEM (BMLI v lf) r.bmr_imms` by  (
       Q.PAT_X_ASSUM `_ = r.bmr_imms` (ASSUME_TAC o GSYM) >>
       ASM_SIMP_TAC (std_ss++QI_ss) [MEM_MAP]
    ) >>
    `bir_machine_lifted_imm_OK (BMLI v lf)` by METIS_TAC[bmr_ok_def, EVERY_MEM] >>
    FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def] >>
    Q.PAT_X_ASSUM `!ms. _ = bir_var_type _` (MP_TAC o GSYM o Q.SPEC `ms'`) >>
    ASM_SIMP_TAC std_ss [type_of_bir_val_def] >>
    `MEM v (bmr_vars r)` by (
       ASM_SIMP_TAC (list_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [bmr_vars_def, MEM_MAP] >>
       METIS_TAC[]
    ) >>
    Cases_on `use_temp` >> (
      METIS_TAC[EVERY_MEM, bmr_vars_DECLARED, bmr_temp_vars_DECLARED,
        bmr_vars_IN_TEMP, bir_temp_var_REWRS]
    )
  ) >- (
    Cases_on `mem_up` >> REV_FULL_SIMP_TAC list_ss [] >>
    REV_FULL_SIMP_TAC list_ss [] >>
    REPEAT (BasicProvers.VAR_EQ_TAC) >>
    FULL_SIMP_TAC (std_ss++bmr_ss) [bir_updateB_desc_var_def,
      bir_updateB_desc_OK_def, bir_updateB_desc_value_def,
      bir_updateB_desc_exp_def, bmr_ok_def, type_of_bir_val_def,
      bir_machine_lifted_mem_OK_def, bmr_mem_var_def,
      bir_is_lifted_exp_def, bir_is_lifted_mem_exp_def] >>
    CONJ_TAC >- METIS_TAC[size_of_bir_immtype_INJ] >>
    Cases_on `use_temp` >> (
      METIS_TAC[EVERY_MEM, bmr_vars_DECLARED, bmr_temp_vars_DECLARED,
        bmr_vars_IN_TEMP, bir_temp_var_REWRS]
    )
  )
) >>
`ALL_DISTINCT (MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates)` by (
  `ALL_DISTINCT (MAP (\up. bir_var_name (bir_updateB_desc_var up)) (updates_imm ++ updates_mem))`
     suffices_by (METIS_TAC[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP]) >>

  SIMP_TAC list_ss [ALL_DISTINCT_APPEND] >>
  Tactical.REVERSE CONJ_TAC >- (
    Cases_on `mem_up` >> REV_FULL_SIMP_TAC list_ss [] >>
    FULL_SIMP_TAC (list_ss++bmr_ss) [MEM_MAP, bmr_mem_var_def] >>
    METIS_TAC[]
  ) >>

  Q.ABBREV_TAC `imm_up_vars = (MAP (\x. ((case (FST x) of BMLI v v2 => v), SND x)) imm_ups)` >>

  `ALL_DISTINCT (MAP (bir_var_name o FST) imm_up_vars)` by (

    `ALL_DISTINCT (MAP bir_var_name (MAP (\i. case i of BMLI v v2 => v) r.bmr_imms))` by (
      Q.PAT_X_ASSUM `bmr_ok r` MP_TAC >>
      SIMP_TAC list_ss [bmr_ok_def,  bmr_varnames_distinct_def, MAP_APPEND,
        bmr_vars_def, ALL_DISTINCT_APPEND]
    ) >>

    `(MAP (\i. case i of BMLI v v2 => v) r.bmr_imms) = (MAP FST imm_up_vars)` by (
      Q.UNABBREV_TAC `imm_up_vars` >>
      `r.bmr_imms = MAP FST imm_ups` by
         FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def] >>
       ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF]
    ) >>
    FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [MAP_MAP_o]
  ) >>

  `(MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates_imm) =
   (MAP (bir_var_name o FST) (FILTER (IS_SOME o SND) imm_up_vars))` suffices_by
     METIS_TAC[ALL_DISTINCT_MAP_FILTER] >>


   `MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates_imm =
    MAP (bir_var_name o FST) (MAP (\up. (bir_updateB_desc_var up,bir_updateB_desc_value up))
        updates_imm)` by (
      SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF]
   ) >>
   ASM_REWRITE_TAC[] >>
   Q.UNABBREV_TAC `imm_up_vars` >>
   ASM_SIMP_TAC std_ss [FILTER_MAP, combinTheory.o_DEF, MAP_MAP_o, pairTheory.pair_CASE_def] >>
   SIMP_TAC (std_ss++QI_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss[``:'a bir_machine_lifted_imm_t``]) [listTheory.MAP_EQ_f, MEM_FILTER]
) >>

ASM_SIMP_TAC std_ss [] >>

Cases_on `r.bmr_pc` >> rename1 `BMLPC v_pc v_pc_cond lf_pc` >>
REPEAT CONJ_TAC >- (
  METIS_TAC[]
) >- (
  Cases_on `eup_temp` >> SIMP_TAC std_ss [bir_updateE_desc_remove_var_REWRS] >>
  FULL_SIMP_TAC std_ss [] >>
  REPEAT STRIP_TAC >>
  `(v' <> mem_v) /\ (!b. v' <> bir_temp_var b mem_v) /\
   ~(MEM v' (MAP (\i. case i of BMLI v v2 => v) r.bmr_imms)) /\
   (!b. ~(MEM v' (MAP (\i. case i of BMLI v v2 => bir_temp_var b v) r.bmr_imms)))` by (
    `v IN {v_pc; v_pc_cond}` by (
     FULL_SIMP_TAC (std_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
       IN_INSERT]
    ) >>
    Q.PAT_X_ASSUM `brm_ok r` MP_TAC >>
    ASM_SIMP_TAC (list_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss [``:'a bir_machine_lifted_imm_t``]) [
      bmr_ok_def, bmr_varnames_distinct_def,
      bmr_vars_def, bmr_temp_vars_def, bir_temp_var_REWRS, MAP_MAP_o,
      ALL_DISTINCT_APPEND, MEM_MAP, combinTheory.o_DEF, PULL_EXISTS,
      FORALL_BOOL] >>
    FULL_SIMP_TAC std_ss [IN_INSERT, NOT_IN_EMPTY] >>
       METIS_TAC [bir_temp_var_REWRS]
  ) >>

  Cases_on `v' IN bir_vars_of_exp (bir_updateB_desc_exp up)` >- METIS_TAC[] >>
  Cases_on `up` >> rename1 `BUpdateDescB v_up e_up val_up tmp_up` >>
  FULL_SIMP_TAC (list_ss++bmr_ss++DatatypeSimps.expand_type_quants_ss [``:'a bir_machine_lifted_imm_t``]) [MEM_MAP, bir_updateB_desc_exp_def] >- (
     `?lf. MEM (BMLI v_up lf) r.bmr_imms` by METIS_TAC[bir_updateB_desc_var_def] >>
     FULL_SIMP_TAC std_ss [bir_vars_of_updateB_desc_def, IN_INSERT,
       bir_updateB_desc_temp_var_def] >> (
       METIS_TAC[]
     )
  ) >>
  Cases_on `mem_up` >> REV_FULL_SIMP_TAC list_ss [] >>
  REV_FULL_SIMP_TAC list_ss [] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC (std_ss++bmr_ss) [bir_updateB_desc_var_def, bmr_mem_var_def] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC std_ss [bir_vars_of_updateB_desc_def, IN_INSERT,
       bir_updateB_desc_temp_var_def, bir_updateB_desc_var_def] >> (
       METIS_TAC[]
  )
) >- (
  Cases_on `eup_temp` >> SIMP_TAC std_ss [bir_updateE_desc_remove_var_REWRS] >>
  METIS_TAC[]
));



val bir_is_lifted_inst_block_COMPUTE_OPTIMISED = store_thm (
"bir_is_lifted_inst_block_COMPUTE_OPTIMISED",
``!r. bmr_ok r ==> !mu. WI_wfe mu ==> !mm l.
  (bir_is_lifted_inst_block_COMPUTE_mm_WF mu mm) ==>
  !ms_case_cond bl l'.
  (!ms bs.
     ?ms' al_step imm_ups mem_up al_mem eup eup_temp updates. (
       bir_is_lifted_inst_block_COMPUTE_precond r bs ms l mu mm bl l' ms_case_cond ms'
         al_step imm_ups mem_up al_mem eup eup_temp updates
     )) ==>
  bir_is_lifted_inst_block (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) ms_case_cond l mu mm (bl :'o bir_block_t)
``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] bir_is_lifted_inst_block_COMPUTE) >>
Q.EXISTS_TAC `l'` >> ASM_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_THM,
  bir_is_lifted_inst_block_COMPUTE_mem_COND_THM, EVERY_APPEND,
  bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_def,
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def,
  bir_is_lifted_inst_block_COMPUTE_precond_def,
  bir_is_lifted_inst_block_COMPUTE_block_def,
  bir_is_lifted_inst_block_COMPUTE_mm_WF_def] >>
METIS_TAC [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_THM,
          bir_is_lifted_inst_block_COMPUTE_updates_FULL_THM,
          bir_is_lifted_inst_block_COMPUTE_eup_COND_remove_var]);




(*------------------------------------------------------------------*)
(* Lemmata to help using bir_is_lifted_inst_block_COMPUTE_OPTIMISED *)
(*------------------------------------------------------------------*)

(* To instantiate bir_is_lifted_inst_block_COMPUTE_OPTIMISED various
   lemmata and even more auxiliary definitions are handy. These are developed below. *)

(* .....................*)
(* Deriving assert_desc *)
(* .....................*)

val bir_assert_desc_OK_via_lifting = store_thm ("bir_assert_desc_OK_via_lifting",
``!env e b.
  bir_is_lifted_exp env e (BLV_Imm (bool2b b)) ==>
  bir_assert_desc_OK env (BAssertDesc e b)``,

SIMP_TAC std_ss [bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def,
  bir_assert_desc_OK_def]);


(* .................................. *)
(* efficient checking of imm_ups_COND *)
(* .................................. *)

val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def = Define `
  (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms' [] [] <=> T) /\
  (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms'
     ((BMLI v lf, NONE)::imm_ups) ((BMLI v' lf')::imms) <=>
       (v' = v) /\ (lf' = lf) /\
       (lf ms' = lf ms) /\
       bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms' imm_ups imms
     ) /\
  (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms'
     ((BMLI v lf, SOME res)::imm_ups) ((BMLI v' lf')::imms) <=>
       (v' = v) /\ (lf' = lf) /\
       (lf ms' = res) /\
       bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms' imm_ups imms
     ) /\
  (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms'
     _ _ <=> F)`


val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_EVAL = store_thm (
  "bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_EVAL",
``!r ms ms' imm_ups.
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups <=>
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms' imm_ups r.bmr_imms``,

SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def,
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def] >>
REPEAT STRIP_TAC >>
CONV_TAC SYM_CONV >>
Q.ABBREV_TAC `bmr_imms = r.bmr_imms` >>
Q.ID_SPEC_TAC `bmr_imms` >> UNABBREV_ALL_TAC >>

Induct_on `imm_ups` >- (
  Cases_on `bmr_imms` >> SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def]
) >>
Cases >> rename1 `(qq, res_opt)` >>
Cases_on `qq` >> rename1 `BMLI v lf` >>

Cases >- SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def] >>
rename1 `_ _ (XX::bmr_imms')` >>
Cases_on `XX` >>
SIMP_TAC (list_ss++bmr_ss) [DISJ_IMP_THM, FORALL_AND_THM] >>
Cases_on `res_opt` >> (
  ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def]
));



(* .............................. *)
(* efficient checking of mem_COND *)
(* .............................. *)

val bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_EVAL = store_thm (
  "bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_EVAL",

``(!r ms ms'. bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' NONE <=>
     (bmr_mem_lf r ms' = bmr_mem_lf r ms)) /\

  (!r ms ms' res. bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' (SOME res) <=>
     (bmr_mem_lf r ms' = res))``,

SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def,
  pairTheory.pair_case_thm, bmr_mem_lf_def] >>
REPEAT STRIP_TAC >> (
  Cases_on ` r.bmr_mem` >>
  SIMP_TAC (std_ss++bmr_ss) []
));

val bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE = store_thm (
  "bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE",
``!r mu bs ms ms'.
   bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' NONE ==>
   bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK
            r mu bs ms ms' []``,

SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def,
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def,
  bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def,
  pairTheory.pair_case_thm, bmr_mem_lf_def] >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `[]` >>
Cases_on `r.bmr_mem` >>
FULL_SIMP_TAC (list_ss++bmr_ss) []);


(* ......................... *)
(* efficient checking of eup *)
(* ......................... *)

val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_REMOVE_VAR = store_thm (
 "bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_REMOVE_VAR",

``!r bs eup ms'. bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms' ==>
bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs (bir_updateE_desc_remove_var eup) ms'``,

SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_remove_var_REWRS, bir_updateE_desc_OK_remove_var]);



val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___JMP =
store_thm ("bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___JMP",
``!r bs ms'. bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs (BUpdateDescE_Jmp (BL_Address (bmr_pc_lf r ms'))) ms'``,

SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_var_def, bir_updateE_SEM_def,
  bir_updateE_desc_OK_def, bir_updateE_desc_exp_def]);


val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___CJMP =
store_thm ("bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___CJMP",
``!r bs ms.
   bmr_ok r ==>
   bmr_rel r bs ms ==>
   !ms' c l_t l_f.
   (bmr_pc_lf r ms' = (if c then l_t else l_f)) ==>
   !e_c.
   (bir_is_lifted_exp bs.bst_environ e_c (BLV_Imm (bool2b c))) ==>

   bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs
     (BUpdateDescE_CJmp
        (SOME (bmr_pc_var_cond r))
        e_c c (BL_Address l_t) (BL_Address l_f)) ms'``,

REPEAT GEN_TAC >>
Cases_on `r.bmr_pc` >> rename1 `BMLPC pc_v pc_cond_v lf` >>
ASM_SIMP_TAC (std_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_var_def, bir_updateE_SEM_def,
  bir_updateE_desc_OK_def, bir_updateE_desc_exp_def,
  bir_updateE_desc_value_def, bmr_ok_def, bmr_pc_lf_def,
  bir_machine_lifted_pc_OK_def, type_of_bool2b,
  BType_Bool_def, bmr_pc_var_cond_def,
  bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def
] >>
REPEAT STRIP_TAC >- (
  `EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_temp_vars r)` by
     METIS_TAC[bmr_temp_vars_DECLARED] >>
  `MEM pc_cond_v (bmr_temp_vars r)` by (
     ASM_SIMP_TAC (list_ss++bmr_ss) [bmr_temp_vars_def]
  ) >>
  METIS_TAC[EVERY_MEM]
) >>
METIS_TAC[]);


val bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___XJMP =
store_thm ("bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___XJMP",
``!r bs ms.
   bmr_ok r ==>
   bmr_rel r bs ms ==>
   !ms' e.
   (bir_is_lifted_exp bs.bst_environ e (BLV_Imm (bmr_pc_lf r ms'))) ==>

   bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs
     (BUpdateDescE_XJmp
        (SOME (bmr_pc_var r))
        e (bmr_pc_lf r ms')) ms'``,

REPEAT GEN_TAC >>
Cases_on `r.bmr_pc` >> rename1 `BMLPC pc_v pc_cond_v lf` >>
ASM_SIMP_TAC (std_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_var_def, bir_updateE_SEM_def,
  bir_updateE_desc_OK_def, bir_updateE_desc_exp_def,
  bir_updateE_desc_value_def, bmr_ok_def, bmr_pc_lf_def,
  bir_machine_lifted_pc_OK_def, type_of_bool2b,
  BType_Bool_def, bmr_pc_var_def,
  bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def
] >>
REPEAT STRIP_TAC >>
`EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_temp_vars r)` by
   METIS_TAC[bmr_temp_vars_DECLARED] >>
`MEM pc_v (bmr_temp_vars r)` by (
   ASM_SIMP_TAC (list_ss++bmr_ss) [bmr_temp_vars_def]
) >>
METIS_TAC[EVERY_MEM]);



(* ..................................................................... *)
(* efficiently checking of bir_is_lifted_inst_block_COMPUTE_updates_FULL *)
(* ..................................................................... *)



val bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def = Define
  `bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL
      (r: ('a, 'b, 'c) bir_lifting_machine_rec_t) bs
      (mem_up : ('a word -> 'b word) option)
      (imm_ups :('c bir_machine_lifted_imm_t # bir_imm_t option) list)
      all_var_names updates_imm update_mem_opt <=>

     (* imm_ups covered *)
     ((MAP (\up. (bir_updateB_desc_var up, bir_updateB_desc_value up)) updates_imm) =
      (MAP (\x. (case x of | (BMLI v _, SOME r) => (v, BVal_Imm r)))
        (FILTER (\x. IS_SOME (SND x)) imm_ups))) /\

     (* mem_up covered *)
     (case mem_up of NONE => (update_mem_opt = NONE) | SOME res =>
       (?upd_mem. (update_mem_opt = SOME upd_mem) /\
           (bir_updateB_desc_var upd_mem = bmr_mem_var r) /\
           (bir_updateB_desc_value upd_mem =
             (bir_eval_exp (bir_updateB_desc_exp upd_mem) bs.bst_environ)) /\
           (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp upd_mem)
             (BLV_Mem res)))) /\

     (* imm_ups are lifted properly *)
     (!var e v use_temp.
            MEM (BUpdateDescB var e (BVal_Imm v) use_temp) updates_imm ==>
            bir_is_lifted_imm_exp bs.bst_environ e v) /\

     (* Vars fit *)
     let updates = updates_imm ++ (option_CASE update_mem_opt [] (\x. [x])) in (

     (!i j var.
        i < LENGTH updates /\ j < i /\
        var IN bir_vars_of_exp (bir_updateB_desc_exp (EL i updates)) ==>
        bir_var_name var <>
        bir_var_name (bir_updateB_desc_temp_var (EL j updates)))) /\

     (!up var. MEM up updates ==>
               var IN bir_vars_of_exp (bir_updateB_desc_exp up) ==>
               (bir_var_name var IN all_var_names))
`;


val bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO_raw = prove (
``!r bs mem_up imm_ups all_var_names updates_imm update_mem_opt eup eup_temp.

      (bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt /\

      (!v up v'.
        eup_temp ==>
        (bir_updateE_desc_var eup = SOME v) ==>
        ~(bir_var_name v IN all_var_names)) /\
     (!v e up v'.
        (~eup_temp \/ (bir_updateE_desc_var eup = NONE)) ==>
        (bir_updateE_desc_exp eup = SOME e) ==>
        v IN bir_vars_of_exp e ==>
        MEM up (updates_imm ++ (option_CASE update_mem_opt [] (\x. [x]))) ==>
        v' IN {bir_updateB_desc_temp_var up; bir_updateB_desc_var up} ==>
        bir_var_name v <> bir_var_name v')) ==>

bir_is_lifted_inst_block_COMPUTE_updates_FULL
  r bs mem_up imm_ups eup eup_temp (updates_imm ++ (option_CASE update_mem_opt [] (\x. [x])))``,


SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_def,
  bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def, LET_THM] >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `updates_imm` >>
Q.EXISTS_TAC `case update_mem_opt of NONE => [] | SOME x => [x]` >>
Q.ABBREV_TAC `updates = (updates_imm ++ case update_mem_opt of NONE => [] | SOME x => [x])` >>
ASM_SIMP_TAC std_ss [sortingTheory.PERM_REFL] >>
REPEAT STRIP_TAC >- (
  Cases_on `mem_up` >> FULL_SIMP_TAC list_ss []
) >> (
  METIS_TAC[]
));


val bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def =
  Define `bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS updates =
    BIGUNION (IMAGE (\up. {bir_var_name (bir_updateB_desc_temp_var up); bir_var_name (bir_updateB_desc_var up)}) (set updates))`;



val bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO = store_thm (
"bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO",
``!r bs mem_up imm_ups all_var_names updates_imm update_mem_opt eup eup_temp.

bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==>

     ((!v up v'.
        eup_temp ==>
        (bir_updateE_desc_var eup = SOME v) ==>
        ~(bir_var_name v IN all_var_names)) /\
     (!vn e up v'.
        (~eup_temp \/ (bir_updateE_desc_var eup = NONE)) ==>
        (bir_updateE_desc_exp eup = SOME e) ==>
        DISJOINT (IMAGE bir_var_name (bir_vars_of_exp e))
           (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS
             (updates_imm ++ (option_CASE update_mem_opt [] (\x. [x])))))) ==>

bir_is_lifted_inst_block_COMPUTE_updates_FULL
  r bs mem_up imm_ups eup eup_temp (updates_imm ++ (option_CASE update_mem_opt [] (\x. [x])))``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO_raw >>
Q.EXISTS_TAC `all_var_names` >>
FULL_SIMP_TAC std_ss [
  bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def,
  IN_BIGUNION, IN_IMAGE,
  GSYM RIGHT_FORALL_OR_THM, IN_INSERT,
  NOT_IN_EMPTY, pred_setTheory.DISJOINT_ALT] >>
METIS_TAC[]);


val bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS =
store_thm ("bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS",
 ``(bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS [] = {}) /\
   (!e v vn ty ups. (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS
      ((BUpdateDescB (BVar vn ty) e v T)::ups) =
      ((bir_temp_var_name vn) INSERT vn INSERT
      (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS ups)))) /\

   (!e v vn ty ups. (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS
      ((BUpdateDescB (BVar vn ty) e v F)::ups) =
      (vn INSERT
       (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS ups))))``,

SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def,
  IMAGE_EMPTY, BIGUNION_EMPTY, IMAGE_INSERT,
  bir_updateB_desc_temp_var_def, bir_temp_var_REWRS,
  bir_updateB_desc_var_def, INSERT_INSERT, BIGUNION_INSERT,
  INSERT_UNION_EQ, UNION_EMPTY, bir_var_name_def]);


val bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_NO_MEM =
store_thm ("bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_NO_MEM",
``!r bs. bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs NONE [] {} [] NONE``,
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  LET_THM]);


val bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_MEM =
store_thm ("bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_MEM",
``!r bs e mres.
   bir_is_lifted_exp bs.bst_environ e (BLV_Mem mres) ==>
   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs (SOME mres) [] (IMAGE bir_var_name (bir_vars_of_exp e)) []
       (SOME (BUpdateDescB (bmr_mem_var r) e (bir_eval_exp e bs.bst_environ) F))``,

SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  LET_THM, bir_updateB_desc_exp_def, bir_updateB_desc_value_def,
  bir_updateB_desc_var_def, IN_IMAGE] >>
REPEAT STRIP_TAC >- (
  `i = 0` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss []
) >- (
  METIS_TAC[]
));


val bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP_NONE =
store_thm ("bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP_NONE",
``!r bs mem_up imm_ups all_var_names updates_imm update_mem_opt var lf.

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==>

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up
       ((BMLI var lf, NONE)::imm_ups) all_var_names updates_imm update_mem_opt``,

SIMP_TAC (list_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  bir_updateB_desc_var_def, bir_updateB_desc_value_def, pairTheory.pair_case_thm, LET_THM] >>
METIS_TAC[]);




val bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP =
store_thm ("bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP",
``!r bs mem_up imm_ups all_var_names updates_imm update_mem_opt.

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==>

   !var lf v e temp.
   bir_is_lifted_imm_exp bs.bst_environ e v ==>
   ~(bir_var_name (bir_temp_var temp var) IN all_var_names) ==>
   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up
       ((BMLI var lf, SOME v)::imm_ups) (IMAGE bir_var_name (bir_vars_of_exp e) UNION all_var_names) ((BUpdateDescB var e (BVal_Imm v) temp)::updates_imm) update_mem_opt``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def, LET_THM, APPEND,
  LENGTH] >>
Q.ABBREV_TAC `updates =  (updates_imm ++
            case update_mem_opt of NONE => [] | SOME x => [x])` >>

SIMP_TAC (list_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  bir_updateB_desc_var_def, bir_updateB_desc_value_def, pairTheory.pair_case_thm, LET_THM,
  bir_updateB_desc_t_11, bir_val_t_11, bir_updateB_desc_exp_def, bir_updateB_desc_value_def] >>
REPEAT STRIP_TAC >> REPEAT (BasicProvers.VAR_EQ_TAC) >| [
  METIS_TAC[],
  METIS_TAC[],

  Cases_on `i` >- (
    FULL_SIMP_TAC std_ss []
  ) >>
  rename1 `j < SUC i'` >>
  FULL_SIMP_TAC list_ss [arithmeticTheory.ADD_CLAUSES] >>
  Q.ABBREV_TAC `up = (EL i' updates)` >>
  `MEM up updates` by METIS_TAC[MEM_EL] >>
  Cases_on `j` >- (
    FULL_SIMP_TAC list_ss [bir_updateB_desc_temp_var_def] >>
    METIS_TAC[]
  ) >>
  FULL_SIMP_TAC list_ss [] >>
  METIS_TAC[],

  FULL_SIMP_TAC std_ss [bir_updateB_desc_exp_def, IN_IMAGE] >>
  METIS_TAC[],

  METIS_TAC[]
]);


val bir_is_lifted_inst_block_COMPUTE_mm_WF_REWR = store_thm ("bir_is_lifted_inst_block_COMPUTE_mm_WF_REWR",
``!mu_b mu_e.
  WI_wfe (WI_end ((n2w mu_b):'a word) (n2w mu_e)) ==>
  (mu_e < dimword (:'a)) ==>
  !mm_b ml.
  ((mm_b + LENGTH (ml:'b word list) <= mu_e) /\ (mu_b <= mm_b)) ==>

   (bir_is_lifted_inst_block_COMPUTE_mm_WF (WI_end ((n2w mu_b):'a word) (n2w mu_e)) (n2w mm_b, ml))``,

SIMP_TAC arith_ss [bir_is_lifted_inst_block_COMPUTE_mm_WF_def,
  WF_bmr_ms_mem_contains_def, bmr_ms_mem_contains_interval_def,
  WI_wf_size_compute, wordsTheory.word_ls_n2w, word_1comp_n2w] >>
REPEAT STRIP_TAC >>
`WI_wf (WI_end ((n2w mu_b):'a word) (n2w mu_e))` by FULL_SIMP_TAC std_ss [WI_wfe_def] >>
`WI_wf (WI_size ((n2w mm_b):'a word) (n2w (LENGTH ml)))` by (
  ASM_SIMP_TAC arith_ss [bir_interval_expTheory.WI_wf_size_compute, word_1comp_n2w,
    wordsTheory.word_ls_n2w]
) >>
FULL_SIMP_TAC arith_ss [WI_size_def, WI_is_sub_compute,
  wordsTheory.word_ls_n2w, word_add_n2w]);


val _ = export_theory();
