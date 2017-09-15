open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_imm_expTheory
open bir_immSyntax bir_programTheory wordsTheory
open bir_mem_expTheory bir_bool_expTheory
open bir_program_env_orderTheory
open bir_program_blocksTheory

open bir_exp_liftingTheory
open bir_lifting_machinesTheory
open bir_interval_expTheory
open bir_update_blockTheory
open bir_lifting_machinesLib

(* This theory defines what it means for a block and a whole program
   to be corresponding to a machine instruction *)

val _ = new_theory "bir_inst_lifting";


val bmr_ms_mem_unchanged_def = Define `bmr_ms_mem_unchanged r ms ms' i <=>
  (!a. WI_MEM a i ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a))`;

val bmr_ms_mem_contains_def = Define `
  (bmr_ms_mem_contains (r : ('a, 'b, 'ms) bir_lifting_machine_rec_t)  (ms : 'ms) (ba, []) = T) /\
  (bmr_ms_mem_contains r ms (ba, v::vs) =
     (bmr_mem_lf r ms ba = (v:'b word)) /\
     (bmr_ms_mem_contains r ms (ba+1w, vs)))`;

val bmr_ms_mem_contains_interval_def = Define `
  bmr_ms_mem_contains_interval (ba: 'a word, wl:'b word list) <=>
  (WI_size ba (n2w (LENGTH wl)))`;

val WF_bmr_ms_mem_contains_def = Define `WF_bmr_ms_mem_contains (ba: 'a word, wl:'b word list) <=>
  (LENGTH wl < dimword (:'a)) /\
  (WI_wf (bmr_ms_mem_contains_interval (ba, wl)))`



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


val bir_is_lifted_inst_block_def = Define `
  bir_is_lifted_inst_block
    (* machine description *)
    (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t)

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
  (WI_wf mu /\ WF_bmr_ms_mem_contains mm) /\

  (!ms bs (p : 'o bir_program_t) c lo bs'.

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



val bir_is_lifted_inst_block_COMPUTE_ms'_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_ms'_COND r ms al_step ms' <=>

     (* We can compute the next machine state using extra assumptions in al_step *)
     ((EVERY (\a. bir_assert_desc_value a) al_step) ==>
      (r.bmr_step_fun ms = SOME ms')) /\

     (* This machine step statisfies the machine state invariants *)
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


val bir_is_lifted_inst_block_COMPUTE_mem_chs_COND_def = Define
  `bir_is_lifted_inst_block_COMPUTE_mem_chs_COND r mu ms ms' al_mem mem_chs <=>

     (* Only explicitly listed memory locations are updated and these are
        outside the unchanged region *)
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
     (bir_updateE_SEM eup = BUpdateValE_Jmp (BL_Address (bmr_pc_lf r ms')))`


val bir_is_lifted_inst_block_COMPUTE = store_thm ("bir_is_lifted_inst_block_COMPUTE",
``!r bl l mm mu l'.

  (WI_wf mu /\ WF_bmr_ms_mem_contains mm) ==>
  (!ms bs. ?ms' al_mem al_step imm_ups mem_chs mem_up eup updates.

     bmr_rel r bs ms ==>  bmr_ms_mem_contains r ms mm ==> (BL_Address (bmr_pc_lf r ms) = l) ==> (

     (* ms' is reached and we need only extra assertions al_step to
        discard preconds of the step theorem. To instantiate this,
        the automation needs to come up with ms' and al_step *)
     bir_is_lifted_inst_block_COMPUTE_ms'_COND r ms al_step ms' /\

     (* All relevant immediate fields are either unchanged or taken care of
        by updates. Unchanged ones are not modified. To do this, the SML code should
        generate imm_ups and later with other information use it to generate updates. *)
     bir_is_lifted_inst_block_COMPUTE_imm_ups_COND r ms ms' imm_ups updates /\

     (* The memory is only changed in locations mem_chs. These are outside region
        mu and the extra assertions al_mem are all we need to show this. The SML
        code should generate mem_chs and al_mem. *)
     bir_is_lifted_inst_block_COMPUTE_mem_chs_COND r mu ms ms' al_mem mem_chs /\

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
  bir_is_lifted_inst_block (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) l mu mm (bl :'o bir_block_t)
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
     bir_is_lifted_inst_block_COMPUTE_mem_chs_COND_def] >>
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



val _ = export_theory();
