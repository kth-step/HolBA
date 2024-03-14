open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_exp_immTheory
open bir_immSyntax bir_programTheory wordsTheory
open bir_auxiliaryTheory
open bir_exp_memTheory bir_bool_expTheory
open bir_program_env_orderTheory
open bir_program_blocksTheory
open bir_temp_varsTheory
open bir_exp_liftingTheory
open bir_lifting_machinesTheory
open bir_interval_expTheory
open bir_update_blockTheory
open bir_program_multistep_propsTheory

open bir_subprogramTheory
open bir_program_valid_stateTheory
open bir_program_labelsTheory
open quantHeuristicsLib
open pred_setTheory
open optionTheory;

(* This theory defines what it means for a block and a whole program
   to be corresponding to a machine instruction *)

val _ = new_theory "bir_inst_lifting";



(* TODO: find a better place for this. bmr_ss is now created in 3
   places and there are probably more like this in the lifter *)
val bmr_REWRS = (
   (type_rws ``:('a, 'b, 'c) bir_lifting_machine_rec_t``) @
   (type_rws ``:'a bir_machine_lifted_pc_t``) @
   (type_rws ``:'a bir_machine_lifted_imm_t``) @
   (type_rws ``:('a, 'b, 'c) bir_machine_lifted_mem_t``)
)
;

val bmr_ss = rewrites bmr_REWRS
(* TODO: end of TODO todo above*)


(*****************************)
(* Unchanged memory interval *)
(*****************************)

Definition bmr_ms_mem_unchanged_def:
  bmr_ms_mem_unchanged r ms ms' i <=>
  (!a. WI_MEM a i ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a))
End


Theorem bmr_ms_mem_contains_UNCHANGED:
  !r ms ms' i mm.
  WF_bmr_ms_mem_contains mm ==>
  bmr_ms_mem_unchanged r ms ms' i ==>
  WI_is_sub (bmr_ms_mem_contains_interval mm) i ==>

  (bmr_ms_mem_contains r ms mm <=>
   bmr_ms_mem_contains r ms' mm)
Proof
Cases_on `mm` >>
rename1 `(ba, vs)` >>
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
  WI_ELEM_LIST_def, DISJ_IMP_THM, FORALL_AND_THM]
QED



(****************************)
(* Execute to address label *)
(****************************)

(* Each machine instruction is translated to a bir program consisting of a
   - block whose label is an address corresponding to the memory address of the instruction
   - potentially some auxiliary blocks whose labels are strings

   Executing a machine instruction corresponds in the BIR program therefore to
   running till one reaches the next address label. For this some auxiliary
   definitions are useful. *)

Definition bir_exec_to_addr_label_n_def:
  bir_exec_to_addr_label_n =
  bir_exec_to_labels_n {l | IS_BL_Address l}
End

Definition bir_exec_to_addr_label_def:
  bir_exec_to_addr_label =
  bir_exec_to_labels {l | (IS_BL_Address l)}
End

Theorem bir_exec_to_addr_label_n_REWR_0:
  bir_exec_to_addr_label_n p bs 0 = BER_Ended [] 0 0 bs
Proof
SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_REWR_0]
QED

Theorem bir_exec_to_addr_label_n_REWR_TERMINATED:
  bir_state_is_terminated bs ==> (bir_exec_to_addr_label_n p bs n = BER_Ended [] 0 0 bs)
Proof
SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_REWR_TERMINATED]
QED


Theorem bir_exec_to_addr_label_n_REWR_SUC:
  (bir_exec_to_addr_label_n p st (SUC n) =
      case bir_exec_to_addr_label p st of
        BER_Ended l1 c1 c1' st1 =>
          (case bir_exec_to_addr_label_n p st1 n of
             BER_Ended l2 c2 c2' st2 =>
               BER_Ended (l1 ++ l2) (c1 + c2) (c1' + c2') st2
           | BER_Looping ll2 => BER_Looping (LAPPEND (fromList l1) ll2))
      | BER_Looping ll1 => BER_Looping ll1)
Proof
SIMP_TAC std_ss [bir_exec_to_addr_label_def, bir_exec_to_addr_label_n_def,
  bir_exec_to_labels_n_REWR_SUC]
QED


Theorem bir_exec_to_addr_label_n_ended_running:
  !prog st l n m c_l' st'.
    (n > 0) ==>
    (bir_exec_to_addr_label_n prog st n = BER_Ended l m c_l' st') ==>
    ~(bir_state_is_terminated st') ==>
    (st'.bst_pc.bpc_index = 0)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def] >> (
  subgoal `(1:num) > 0` >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  IMP_RES_TAC bir_exec_to_labels_n_ended_running
)
QED


(***************************************************)
(* Lifting a machine instruction to a single block *)
(***************************************************)

Definition bir_is_lifted_inst_block_def:
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
           (bmr_rel r bs' ms')))
End




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


Definition bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_def:
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND r ms ms' imm_ups updates <=>

     (* For every immediate value mapped, we checked, whether it is changed or not *)
     (MAP FST imm_ups = r.bmr_imms) /\
     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
             (lf ms' = lf ms) /\ (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)) /\
             (bir_var_name v <> bir_var_name (bir_updateB_desc_temp_var up)))) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (lf ms' = res) /\ (?up. MEM up updates /\ (bir_updateB_desc_var up = v) /\
                                   (bir_updateB_desc_value up = SOME (BVal_Imm res))))
End



Definition bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def:
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND r mu ms ms' al_mem <=>

     (* Only explicitly listed memory locations are updated and these are
        outside the unchanged region *)
     (EVERY (\a. bir_assert_desc_value a) al_mem ==>
     ?mem_chs.
     (!a. ~(MEM a mem_chs) ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a)) /\
     (!a. (MEM a mem_chs) ==> ~(WI_MEM a mu)))
End


Definition bir_is_lifted_inst_block_COMPUTE_mem_COND_def:
  bir_is_lifted_inst_block_COMPUTE_mem_COND r bs ms ms' mem_up updates <=>
     (* Memory update sensible *)
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) => (
             (lf ms' = lf ms) /\ (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)) /\
             (bir_var_name v <> bir_var_name (bir_updateB_desc_temp_var up))))
       | (SOME res, BMLM v lf) =>
              (lf ms' = res) /\ (?up.

              MEM up updates /\ (bir_updateB_desc_var up = v) /\
              (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp up) (BLV_Mem res))))
End


Definition bir_is_lifted_inst_block_COMPUTE_eup_COND_def:
  bir_is_lifted_inst_block_COMPUTE_eup_COND r eup ms'  <=>
     (* EUP sensible *)
     (!var. (bir_updateE_desc_var eup = SOME var) ==>
            ((!v lf. (MEM (BMLI v lf) r.bmr_imms ==>
                    (bir_var_name var) <> (bir_var_name v))) /\
            (case r.bmr_mem of
               | (BMLM v lf) => (bir_var_name var) <> (bir_var_name v)))) /\
     (bir_updateE_SEM eup = BUpdateValE_Jmp (BL_Address (bmr_pc_lf r ms')))
End



(*-------------*)
(* The theorem *)
(*-------------*)

Theorem bir_is_lifted_inst_block_COMPUTE:
  !r bl ms_case_cond l mm mu l'.

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
     EVERY (bir_assert_desc_OK bs.bst_environ) (al_step++al_mem) /\
     bir_update_block_desc_OK bs.bst_environ eup updates /\

     (* The block does not depend on the actual values for the state, but just
        the expressions. So, bl should be independent of the actual state. *)
     (bl = (bir_update_assert_block l' (al_step++al_mem) eup updates)))) ==>
  bir_is_lifted_inst_block (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) ms_case_cond l mu mm (bl :'o bir_block_t)
Proof
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

MP_TAC (Q.SPECL [`bs`, `l'`, `eup`, `p`, `updates`, `bl`, `al_step++al_mem`]
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
         suffices_by METIS_TAC [bir_env_oldTheory.bir_env_var_is_declared_ORDER] >>
      MATCH_MP_TAC bir_env_read_EQ_lookup_IMPL >>
      Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
      METIS_TAC[bir_is_lifted_inst_block_COMPUTE_eup_COND_def]
   ) >>

   rename1 `MEM (_, SOME res) imm_ups` >>
   `(lf ms' = res) /\
    (?up.
       MEM up updates /\ (bir_updateB_desc_var up = v) /\
       (bir_updateB_desc_value up = SOME (BVal_Imm res)))` by METIS_TAC[] >>

   FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_def, AND_IMP_INTRO] >>
   Tactical.REVERSE CONJ_TAC >- METIS_TAC[bir_env_oldTheory.bir_env_var_is_declared_ORDER] >>

   Q.PAT_X_ASSUM `!up. MEM up updates ==> _` (MP_TAC o Q.SPEC `up`) >>
   ASM_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm, bir_env_check_type_def, bir_env_lookup_type_def]
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
       suffices_by METIS_TAC [bir_env_oldTheory.bir_env_var_is_declared_ORDER] >>
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
          (bir_updateB_desc_value up)) /\
   (OPTION_MAP type_of_bir_val (bir_updateB_desc_value up) = SOME (bir_var_type (bir_updateB_desc_var up)))` by (
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
  Tactical.REVERSE CONJ_TAC >- (
    METIS_TAC[n2w_bir_load_mmap_w2n_thm,
              bir_env_oldTheory.bir_env_var_is_declared_ORDER]
  ) >>

  ASM_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm,
    bir_updateB_desc_value_def, bir_env_check_type_def, bir_env_lookup_type_def] >>

  FULL_SIMP_TAC std_ss [bir_env_read_def, pairTheory.pair_case_thm,
    bir_updateB_desc_value_def, bir_env_check_type_def, bir_env_lookup_type_def] >>
  Cases_on `z` >> FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
) >>

`bir_machine_lifted_pc r.bmr_pc bs' ms'` by (
  Cases_on `r.bmr_pc` >> rename1 `BMLPC v_pc v_pc_cons pc_lf` >>
  FULL_SIMP_TAC std_ss [bir_machine_lifted_pc_def,
     bir_is_lifted_inst_block_COMPUTE_eup_COND_def] >>
  `bir_env_var_is_declared bs'.bst_environ v_pc /\
   bir_env_var_is_declared bs'.bst_environ v_pc_cons` by
      METIS_TAC[bir_env_oldTheory.bir_env_var_is_declared_ORDER] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC (std_ss++bmr_ss) [BUpdateValE_SEM_def,
    bir_state_pc_is_at_label_def, bmr_pc_lf_def] >>
  METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss []
QED



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

Definition bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def:
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK r mu bs ms ms' al_mem <=>
   (bir_is_lifted_inst_block_COMPUTE_al_mem_COND r mu ms ms' al_mem /\
    EVERY (bir_assert_desc_OK bs.bst_environ) al_mem)
End


Definition bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_def:
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups <=>

     (MAP FST imm_ups = r.bmr_imms) /\
     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
                     (lf ms' = lf ms)) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (lf ms' = res))
End

Definition bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES_def:
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_UPDATES r ms ms' imm_ups updates <=>

     (!v lf. (MEM (BMLI v lf, NONE) imm_ups) ==>
             (!up. MEM up updates ==>
             (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)))) /\

     (!v lf res. (MEM (BMLI v lf, SOME res) imm_ups) ==>
                 (?up. MEM up updates /\ (bir_updateB_desc_var up = v) /\
                 (bir_updateB_desc_value up = SOME (BVal_Imm res))))
End


Definition bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES_def:
  bir_is_lifted_inst_block_COMPUTE_mem_COND_UPDATES r bs ms ms' mem_up updates <=>
     (* Memory update sensible *)
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) =>
             (!up. MEM up updates ==>
                   (bir_var_name v <> bir_var_name (bir_updateB_desc_var up)))
       | (SOME res, BMLM v lf) =>
              (?up.
              MEM up updates /\ (bir_updateB_desc_var up = v) /\
              (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp up) (BLV_Mem res))))
End

Definition bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def:
  bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' mem_up <=>
     (case (mem_up, r.bmr_mem) of
       | (NONE, BMLM v lf) => (
             (lf ms' = lf ms))
       | (SOME res, BMLM v lf) =>
              (lf ms' = res))
End


Definition bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def:
  bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms'  <=>
     bir_updateE_desc_OK bs.bst_environ eup /\

     (case (bir_updateE_desc_var eup) of NONE => T
       | SOME var => case r.bmr_pc of BMLPC v_pc v_pc_cond _ =>
         ((var = v_pc) \/ (var = v_pc_cond))) /\

     (bir_updateE_SEM eup = BUpdateValE_Jmp (BL_Address (bmr_pc_lf r ms')))
End


Definition bir_is_lifted_inst_block_COMPUTE_updates_FULL_def:
  bir_is_lifted_inst_block_COMPUTE_updates_FULL
      (r: ('a, 'b, 'c) bir_lifting_machine_rec_t) bs
      (mem_up : ('a word -> 'b word) option)
      (imm_ups :('c bir_machine_lifted_imm_t # bir_imm_t option) list)
      (eup :bir_updateE_desc_t) (eup_temp :bool) updates =

     ?updates_imm updates_mem.

     (* imm_ups covered *)
     ((MAP (\up. (bir_updateB_desc_var up, bir_updateB_desc_value up)) updates_imm) =
      (MAP (\x. (case x of | (BMLI v _, SOME r) => (v, SOME (BVal_Imm r))))
        (FILTER (\x. IS_SOME (SND x)) imm_ups))) /\

     (* mem_up covered *)
     (case mem_up of NONE => (updates_mem = []) | SOME res =>
       (?upd_mem. (updates_mem = [upd_mem]) /\
           (bir_updateB_desc_var upd_mem = bmr_mem_var r) /\
           ((bir_updateB_desc_value upd_mem) =
             (bir_eval_exp (bir_updateB_desc_exp upd_mem) bs.bst_environ)) /\
           (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp upd_mem)
             (BLV_Mem res)))) /\

     (* Nothing else updated *)
     (PERM updates (updates_imm ++ updates_mem)) /\

     (* imm_ups are lifted properly *)
     (!var e v use_temp.
            MEM (BUpdateDescB var e (SOME (BVal_Imm v)) use_temp) updates_imm ==>
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
        bir_var_name v <> bir_var_name v')
End


Definition bir_is_lifted_inst_block_COMPUTE_block_def:
  bir_is_lifted_inst_block_COMPUTE_block l' al_mem al_step eup_temp eup updates =
  bir_update_assert_block l' (al_step ++ al_mem)
                 (if eup_temp then eup
                  else bir_updateE_desc_remove_var eup) updates
End

Definition bir_is_lifted_inst_block_COMPUTE_precond_def:
  bir_is_lifted_inst_block_COMPUTE_precond r bs ms l mu mm bl l' ms_case_cond ms'
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
     (bl = bir_is_lifted_inst_block_COMPUTE_block l' al_mem al_step eup_temp eup updates)))
End

Definition bir_is_lifted_inst_block_COMPUTE_mm_WF_def:
  bir_is_lifted_inst_block_COMPUTE_mm_WF mu mm <=>
    ((WF_bmr_ms_mem_contains mm) /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu)
End



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
       (?lf i. (bir_updateB_desc_value upd = SOME (BVal_Imm i)) /\
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
    `MEM (v, SOME (BVal_Imm res)) (MAP (\up. (bir_updateB_desc_var up,bir_updateB_desc_value up))
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
    `?i. res = SOME (BVal_Imm i)` by METIS_TAC[bir_updateB_desc_value_def] >>
    `bir_is_lifted_imm_exp bs.bst_environ e i` by METIS_TAC[] >>

    FULL_SIMP_TAC std_ss [bir_updateB_desc_OK_def, bir_is_lifted_imm_exp_def] >>

    `?lf. MEM (BMLI v lf, SOME i) imm_ups` by (
      METIS_TAC [bir_updateB_desc_value_def,
        bir_updateB_desc_var_def, bir_val_t_11, SOME_11]
    ) >>

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



Theorem bir_is_lifted_inst_block_COMPUTE_OPTIMISED:
  !r. bmr_ok r ==> !mu. WI_wfe mu ==> !mm l.
  (bir_is_lifted_inst_block_COMPUTE_mm_WF mu mm) ==>
  !ms_case_cond bl l'.
  (!ms bs.
     ?ms' al_step imm_ups mem_up al_mem eup eup_temp updates. (
       bir_is_lifted_inst_block_COMPUTE_precond r bs ms l mu mm bl l' ms_case_cond ms'
         al_step imm_ups mem_up al_mem eup eup_temp updates
     )) ==>
  bir_is_lifted_inst_block (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) ms_case_cond l mu mm (bl :'o bir_block_t)
Proof
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
          bir_is_lifted_inst_block_COMPUTE_eup_COND_remove_var]
QED




(*------------------------------------------------------------------*)
(* Lemmata to help using bir_is_lifted_inst_block_COMPUTE_OPTIMISED *)
(*------------------------------------------------------------------*)

(* To instantiate bir_is_lifted_inst_block_COMPUTE_OPTIMISED various
   lemmata and even more auxiliary definitions are handy. These are developed below. *)

(* .....................*)
(* Deriving assert_desc *)
(* .....................*)

Theorem bir_assert_desc_OK_via_lifting:
  !env e b.
  bir_is_lifted_exp env e (BLV_Imm (bool2b b)) ==>
  bir_assert_desc_OK env (BAssertDesc e b)
Proof
SIMP_TAC std_ss [bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def,
  bir_assert_desc_OK_def]
QED


(* .................................. *)
(* efficient checking of imm_ups_COND *)
(* .................................. *)

Definition bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def:
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
     _ _ <=> F)
End


Theorem bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_EVAL:
  !r ms ms' imm_ups.
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES r ms ms' imm_ups <=>
  bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK ms ms' imm_ups r.bmr_imms
Proof
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
)
QED



(* .............................. *)
(* efficient checking of mem_COND *)
(* .............................. *)

Theorem bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_EVAL:
  (!r ms ms'. bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' NONE <=>
     (bmr_mem_lf r ms' = bmr_mem_lf r ms)) /\

  (!r ms ms' res. bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' (SOME res) <=>
     (bmr_mem_lf r ms' = res))
Proof
SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def,
  pairTheory.pair_case_thm, bmr_mem_lf_def] >>
REPEAT STRIP_TAC >> (
  Cases_on ` r.bmr_mem` >>
  SIMP_TAC (std_ss++bmr_ss) []
)
QED

Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE:
  !r mu bs ms ms'.
   bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES r ms ms' NONE ==>
   bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK
            r mu bs ms ms' []
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def,
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def,
  bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_def,
  pairTheory.pair_case_thm, bmr_mem_lf_def] >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `[]` >>
Cases_on `r.bmr_mem` >>
FULL_SIMP_TAC (list_ss++bmr_ss) []
QED


(* ......................... *)
(* efficient checking of eup *)
(* ......................... *)

Theorem bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_REMOVE_VAR:
  !r bs eup ms'. bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs eup ms' ==>
bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs (bir_updateE_desc_remove_var eup) ms'
Proof
SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_remove_var_REWRS, bir_updateE_desc_OK_remove_var]
QED



Theorem bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___JMP:
  !r bs ms'. bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs (BUpdateDescE_Jmp (BL_Address (bmr_pc_lf r ms'))) ms'
Proof
SIMP_TAC std_ss [bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS_def,
  bir_updateE_desc_var_def, bir_updateE_SEM_def,
  bir_updateE_desc_OK_def, bir_updateE_desc_exp_def]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___CJMP:
  !r bs ms.
   bmr_ok r ==>
   bmr_rel r bs ms ==>
   !ms' c l_t l_f.
   (bmr_pc_lf r ms' = (if c then l_t else l_f)) ==>
   !e_c.
   (bir_is_lifted_exp bs.bst_environ e_c (BLV_Imm (bool2b c))) ==>

   bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs
     (BUpdateDescE_CJmp
        (SOME (bmr_pc_var_cond r))
        e_c c (BL_Address l_t) (BL_Address l_f)) ms'
Proof
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
METIS_TAC[]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___XJMP:
  !r bs ms.
   bmr_ok r ==>
   bmr_rel r bs ms ==>
   !ms' e.
   (bir_is_lifted_exp bs.bst_environ e (BLV_Imm (bmr_pc_lf r ms'))) ==>

   bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS r bs
     (BUpdateDescE_XJmp
        (SOME (bmr_pc_var r))
        e (bmr_pc_lf r ms')) ms'
Proof
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
METIS_TAC[EVERY_MEM]
QED



(* ..................................................................... *)
(* efficiently checking of bir_is_lifted_inst_block_COMPUTE_updates_FULL *)
(* ..................................................................... *)



Definition bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def:
  bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL
      (r: ('a, 'b, 'c) bir_lifting_machine_rec_t) bs
      (mem_up : ('a word -> 'b word) option)
      (imm_ups :('c bir_machine_lifted_imm_t # bir_imm_t option) list)
      all_var_names updates_imm update_mem_opt <=>

     (* imm_ups covered *)
     ((MAP (\up. (bir_updateB_desc_var up, bir_updateB_desc_value up)) updates_imm) =
      (MAP (\x. (case x of | (BMLI v _, SOME r) => (v, SOME (BVal_Imm r))))
        (FILTER (\x. IS_SOME (SND x)) imm_ups))) /\

     (* mem_up covered *)
     (case mem_up of NONE => (update_mem_opt = NONE) | SOME res =>
       (?upd_mem. (update_mem_opt = SOME upd_mem) /\
           (bir_updateB_desc_var upd_mem = bmr_mem_var r) /\
           ((bir_updateB_desc_value upd_mem) =
             (bir_eval_exp (bir_updateB_desc_exp upd_mem) bs.bst_environ)) /\
           (bir_is_lifted_exp bs.bst_environ (bir_updateB_desc_exp upd_mem)
             (BLV_Mem res)))) /\

     (* imm_ups are lifted properly *)
     (!var e v use_temp.
            MEM (BUpdateDescB var e (SOME (BVal_Imm v)) use_temp) updates_imm ==>
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
End


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


Definition bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def:
  bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS updates =
    BIGUNION (IMAGE (\up. {bir_var_name (bir_updateB_desc_temp_var up); bir_var_name (bir_updateB_desc_var up)}) (set updates))
End



Theorem bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO:
  !r bs mem_up imm_ups all_var_names updates_imm update_mem_opt.

bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==> !eup eup_temp.

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
  r bs mem_up imm_ups eup eup_temp (updates_imm ++ (option_CASE update_mem_opt [] (\x. [x])))
Proof
REPEAT STRIP_TAC >>
MATCH_MP_TAC bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO_raw >>
Q.EXISTS_TAC `all_var_names` >>
FULL_SIMP_TAC std_ss [
  bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def,
  IN_BIGUNION, IN_IMAGE,
  GSYM RIGHT_FORALL_OR_THM, IN_INSERT,
  NOT_IN_EMPTY, pred_setTheory.DISJOINT_ALT] >>
METIS_TAC[]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS:
  (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS [] = {}) /\
   (!e v vn ty ups. (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS
      ((BUpdateDescB (BVar vn ty) e v T)::ups) =
      ((bir_temp_var_name vn) INSERT vn INSERT
      (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS ups)))) /\

   (!e v vn ty ups. (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS
      ((BUpdateDescB (BVar vn ty) e v F)::ups) =
      (vn INSERT
       (bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS ups))))
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_def,
  IMAGE_EMPTY, BIGUNION_EMPTY, IMAGE_INSERT,
  bir_updateB_desc_temp_var_def, bir_temp_var_REWRS,
  bir_updateB_desc_var_def, INSERT_INSERT, BIGUNION_INSERT,
  INSERT_UNION_EQ, UNION_EMPTY, bir_var_name_def]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_NO_MEM:
  !r bs. bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs NONE [] {} [] NONE
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  LET_THM]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_MEM:
  !r bs e mres.
   bir_is_lifted_exp bs.bst_environ e (BLV_Mem mres) ==>
     (bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs (SOME mres) [] (IMAGE bir_var_name (bir_vars_of_exp e)) []
        (SOME (BUpdateDescB (bmr_mem_var r) e (bir_eval_exp e bs.bst_environ) F)))
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  LET_THM, bir_updateB_desc_exp_def, bir_updateB_desc_value_def,
  bir_updateB_desc_var_def, IN_IMAGE] >>
REPEAT STRIP_TAC >- (
  `i = 0` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss []
) >- (
  METIS_TAC[]
)
QED


Theorem bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP_NONE:
  !r bs mem_up imm_ups all_var_names updates_imm update_mem_opt var lf.

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==>

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up
       ((BMLI var lf, NONE)::imm_ups) all_var_names updates_imm update_mem_opt
Proof
SIMP_TAC (list_ss++bmr_ss) [bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL_def,
  bir_updateB_desc_var_def, bir_updateB_desc_value_def, pairTheory.pair_case_thm, LET_THM] >>
METIS_TAC[]
QED




Theorem bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP:
  !r bs mem_up imm_ups all_var_names updates_imm update_mem_opt.

   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up imm_ups all_var_names updates_imm update_mem_opt ==>

   !var lf v e temp.
   bir_is_lifted_imm_exp bs.bst_environ e v ==>
   ~(bir_var_name (bir_temp_var temp var) IN all_var_names) ==>
   bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL r bs mem_up
       ((BMLI var lf, SOME v)::imm_ups) (IMAGE bir_var_name (bir_vars_of_exp e) UNION all_var_names) ((BUpdateDescB var e (SOME (BVal_Imm v)) temp)::updates_imm) update_mem_opt
Proof
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
]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_mm_WF_REWR:
  !mu_b mu_e.
  WI_wfe (WI_end ((n2w mu_b):'a word) (n2w mu_e)) ==>
  (mu_e < dimword (:'a)) ==>
  !mm_b ml.
  ((mm_b + LENGTH (ml:'b word list) <= mu_e) /\ (mu_b <= mm_b)) ==>

   (bir_is_lifted_inst_block_COMPUTE_mm_WF (WI_end ((n2w mu_b):'a word) (n2w mu_e)) (n2w mm_b, ml))
Proof
SIMP_TAC arith_ss [bir_is_lifted_inst_block_COMPUTE_mm_WF_def,
  WF_bmr_ms_mem_contains_def, bmr_ms_mem_contains_interval_def,
  WI_wf_size_compute, word_ls_n2w, word_1comp_n2w] >>
REPEAT STRIP_TAC >>
`WI_wf (WI_end ((n2w mu_b):'a word) (n2w mu_e))` by FULL_SIMP_TAC std_ss [WI_wfe_def] >>
`WI_wf (WI_size ((n2w mm_b):'a word) (n2w (LENGTH ml)))` by (
  ASM_SIMP_TAC arith_ss [bir_interval_expTheory.WI_wf_size_compute, word_1comp_n2w,
    word_ls_n2w]
) >>
FULL_SIMP_TAC arith_ss [WI_size_def, WI_is_sub_compute,
  word_ls_n2w, word_add_n2w]
QED



Definition bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def:
  bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs il <=>

  (EVERY (\ (b:'a word, s, f1, f2, e).
     (s < dimword (:'a) /\ s <> 0) /\
     (FUNS_EQ_OUTSIDE_WI_size b s f1 f2) /\
     (bir_is_lifted_imm_exp bs.bst_environ e (w2bs b sz))) il)
End

Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_NIL:
  !sz bs. bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs ([]:('a word # num # ('a word -> 'b word) # ('a word -> 'b word) # bir_exp_t) list)
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def]
QED

Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_CONS:
  !sz bs il (b : 'a word) s (f1 : 'a word -> 'b word) f2 e.

      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs il ==>
      (FUNS_EQ_OUTSIDE_WI_size b s f1 f2) ==>
      (bir_is_lifted_imm_exp bs.bst_environ e (w2bs b sz)) ==>
      ((s < dimword (:'a) /\ s <> 0)) ==>
      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs ((b:'a word, s, f1, f2, e)::il)
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO:
  !(r : ('addr_ty, 'val_ty, 'ms) bir_lifting_machine_rec_t) sz.
   (dimindex (:'addr_ty) = size_of_bir_immtype sz) ==>
  !bs ms mu_b mu_e.
   (WI_wfe (WI_end ((n2w mu_b):'addr_ty word) (n2w mu_e))) ==>
   !(il : ('addr_ty word # num # ('addr_ty word -> 'val_ty word) # ('addr_ty word -> 'val_ty word) # bir_exp_t) list).
   bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs il ==>

   !ms'.
   (!a. EVERY (\ (b, s, f1, f2, e). f1 a = f2 a) il ==> (bmr_mem_lf r ms' a = bmr_mem_lf r ms a)) ==>
   bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK r (WI_end (n2w mu_b) (n2w mu_e)) bs ms ms' (MAP (\ (b, s, f1, f2, e). BAssertDesc (BExp_unchanged_mem_interval_distinct sz mu_b mu_e e s)
           (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mu_b) (n2w mu_e) b s)) il)
Proof
SIMP_TAC list_ss [bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def,
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_def,
  bir_is_lifted_inst_block_COMPUTE_al_mem_COND_def,
  EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++QUANT_INST_ss [pair_default_qp]) [] >>
SIMP_TAC std_ss [bir_assert_desc_value_def,   bir_assert_desc_OK_def,
  BExp_unchanged_mem_interval_distinct_eval] >>
Tactical.REVERSE (REPEAT STRIP_TAC) >- (
  `bir_is_lifted_imm_exp bs.bst_environ e (w2bs b sz)` by PROVE_TAC[] >>
  Cases_on `sz` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def, pairTheory.pair_case_thm] >>
    Cases_on `b` >> rename1 `bn:num < _` >> POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [
      WI_distinct_MEM_UNCHANGED_COMPUTE_def, w2w_def, word_lo_n2w, word_ls_n2w, dimword_def,
      w2n_n2w, word_add_n2w]
  )
) >>
Q.ABBREV_TAC `mem_chs = FLAT (MAP (\ (b, s, f1, f2, e). WI_ELEM_LIST b s) il)` >>

`!b s f1 f2 e. MEM (b, s, f1, f2, e) il ==>
      WI_wfe (WI_size b (n2w s)) /\
      WI_distinct (WI_end (n2w mu_b) (n2w mu_e)) (WI_size b (n2w s))` by (
  METIS_TAC [WI_distinct_compute_MEM_UNCHANGED]
) >>

`!a. MEM a mem_chs <=> ?b s f1 f2 e. (MEM (b, s, f1, f2, e) il) /\ (WI_MEM a (WI_size b (n2w s)))` by (
   Q.UNABBREV_TAC `mem_chs` >>
   SIMP_TAC std_ss [MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
   SIMP_TAC (std_ss++QUANT_INST_ss[pair_default_qp]) [] >>
   ConseqConv.REDEPTH_CONSEQ_CONV_TAC (K ConseqConv.EXISTS_EQ___CONSEQ_CONV) >>
   SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
   REPEAT STRIP_TAC >>
   `WI_wf (WI_size b (n2w s))` by METIS_TAC [WI_wfe_def] >>
   `s < dimword (:'addr_ty)` by METIS_TAC[] >>
   ASM_SIMP_TAC arith_ss [WI_MEM_WI_size, w2n_n2w]
) >>

Q.EXISTS_TAC `mem_chs` >>
ASM_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  Q.PAT_X_ASSUM `!a. _` MATCH_MP_TAC >>
  REPEAT STRIP_TAC >>
  `FUNS_EQ_OUTSIDE_WI_size b s f1 f2` by METIS_TAC[] >>
  `~WI_MEM a (WI_size b (n2w s))` by METIS_TAC[] >>
  `WI_wf (WI_size b (n2w s))` by METIS_TAC [WI_wfe_def] >>
  FULL_SIMP_TAC std_ss [FUNS_EQ_OUTSIDE_WI_size_def]
) >>

`WI_distinct (WI_end (n2w mu_b) (n2w mu_e)) (WI_size b (n2w s))` by METIS_TAC[] >>
FULL_SIMP_TAC std_ss [WI_distinct_def, WI_overlap_def] >>
METIS_TAC[]
QED




Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_MERGE_1:
  !sz bs il (b1 : 'a word) s1 (f : 'a word -> 'b word) f12 e1 b2 s2 f21 e2.

      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs
         ((b1:'a word, s1, f, f12, e1)::(b2, s2, f21, f, e2)::il) ==>

      ((s1 + s2 < dimword (:'a)) /\
      (b2 = b1 + (n2w s1))) ==>

      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs
         ((b1:'a word, s1+s2, f21, f12, e1)::il)
Proof
SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def] >>
REPEAT GEN_TAC >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `s1 + s2 < dimword (:'a)` ASSUME_TAC >>
FULL_SIMP_TAC arith_ss [FUNS_EQ_OUTSIDE_WI_size_def,
  WI_MEM_WI_size, w2n_n2w] >>
STRIP_TAC >>
`WI_wf (WI_size b1 (n2w s1))` by (
  IRULE_TAC WI_wf_size_LOWER_EQ >>
  Q.EXISTS_TAC `n2w (s1 + s2)` >>
  ASM_SIMP_TAC arith_ss [word_ls_n2w]
) >>
`WI_wf (WI_size (b1+n2w s1) (n2w s2))` by (
  Q.PAT_X_ASSUM `WI_wf (WI_size b1 (n2w (s1 + s2)))` MP_TAC >>
  Cases_on `b1` >>
  ASM_SIMP_TAC arith_ss [WI_wf_size_SUM_LT, w2n_n2w, word_add_n2w]
) >>
FULL_SIMP_TAC list_ss [WI_ELEM_LIST_ADD]
QED


Theorem bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_MERGE_2:
  !sz bs il (b1 : 'a word) s1 (f : 'a word -> 'b word) f12 e1 b2 s2 f21 e2.

      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs
         ((b1:'a word, s1, f, f12, e1)::(b2, s2, f21, f, e2)::il) ==>

      ((s1 + s2 < dimword (:'a)) /\
      (b1 = b2 + (n2w s2))) ==>

      bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS sz bs
         ((b2:'a word, s2+s1, f21, f12, e2)::il)
Proof
SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [
  bir_is_lifted_inst_block_COMPUTE_al_mem_INTERVALS_def] >>
REPEAT GEN_TAC >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `s1 + s2 < dimword (:'a)` ASSUME_TAC >>
FULL_SIMP_TAC arith_ss [FUNS_EQ_OUTSIDE_WI_size_def,
  WI_MEM_WI_size, w2n_n2w] >>
STRIP_TAC >>
`WI_wf (WI_size b2 (n2w s2))` by (
  IRULE_TAC WI_wf_size_LOWER_EQ >>
  Q.EXISTS_TAC `n2w (s1 + s2)` >>
  ASM_SIMP_TAC arith_ss [word_ls_n2w]
) >>
`WI_wf (WI_size (b2+n2w s2) (n2w s1))` by (
  Q.PAT_X_ASSUM `WI_wf (WI_size b2 (n2w (s1 + s2)))` MP_TAC >>
  Cases_on `b2` >>
  ASM_SIMP_TAC arith_ss [WI_wf_size_SUM_LT, w2n_n2w, word_add_n2w]
) >>
Q.SUBGOAL_THEN `s1 + s2 = s2 + s1` SUBST1_TAC >- DECIDE_TAC >>
REWRITE_TAC [WI_ELEM_LIST_ADD] >>
FULL_SIMP_TAC list_ss []
QED



(**********************************************)
(* Lifting a machine instruction to a program *)
(**********************************************)

Definition bir_is_lifted_inst_prog_def:
  bir_is_lifted_inst_prog
    (* machine description *)
    (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t)

    (* The label to start executing. Since, it is always an address label, we provide only
       the immediate. It is the only address label of the program. All auxiliary labels
       need to be identified by strings. *)
    l

    (* A region of memory not touched by the execution. Usually this is the part where
       the program code is stored. *)
    mu

    (* The code for the machine instruction stored somewhere (usually at the PC) stored
       in mem *)
    mm

    (* The program *)
    (p :'o bir_program_t)

    <=>

  (* Parameters are sensible *)
  (WI_wfe mu /\ WF_bmr_ms_mem_contains mm /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu /\
   bir_is_valid_labels p /\ (!l'. MEM (BL_Address l') (bir_labels_of_program p) <=> (l' = l)) /\
   bir_program_string_labels_guarded p) /\

  (!ms bs.

    (* The machine state and the bir state are related *)
    (bmr_rel r bs ms) ==>

    (* The PC points to where we expect *)
    (bs.bst_pc = bir_block_pc (BL_Address l)) ==>

    (* At this location in memory the expected instruction code is found *)
    bmr_ms_mem_contains r ms mm ==>

    (* The bir state is not terminated yet *)
    ~(bir_state_is_terminated bs) ==>

    (* Then executing till the next address label terminates and either
       violates an assertion or results in a state that corresponds to
       the machine state after one step. *)
    ?lo c c' bs'.
      (bir_exec_to_addr_label p bs = BER_Ended lo c c' bs') /\

      (~(bs'.bst_status = BST_AssertionViolated) ==>
      (?ms'. (r.bmr_step_fun ms = SOME ms') /\
             (bmr_ms_mem_unchanged r ms ms' mu) /\
             (bmr_rel r bs' ms'))))
End


(* The simplest and most common situation is that an instruction is implemented by
   a single block *)
Theorem bir_is_lifted_inst_prog_SINGLE_INTRO:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) li hc mu mm (bl:'o bir_block_t) extra_cond.

  bir_is_lifted_inst_block r extra_cond (BL_Address_HC li hc) mu mm bl ==>
  (bl.bb_label = BL_Address li) /\ (!ms. extra_cond ms) ==>
  bir_is_lifted_inst_prog r li mu mm (BirProgram [bl])
Proof
SIMP_TAC (list_ss++bir_TYPES_ss) [bir_is_lifted_inst_block_def, bir_is_lifted_inst_prog_def,
  bir_is_valid_labels_def, bir_labels_of_program_def, bir_program_string_labels_guarded_def,
  BL_recognisers, BL_Address_HC_def] >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!ms bs p. _` (MP_TAC o Q.SPECL [`ms`, `bs`, `BirProgram [bl]`]) >>
`?lo c bs'. (bir_exec_block (BirProgram [bl]) bl bs = (lo,c,bs'))` by
  METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC list_ss [bir_is_valid_labels_def,
  bir_labels_of_program_def] >>
STRIP_TAC >>

MP_TAC (ISPECL [``{l | IS_BL_Address l}``, ``(BirProgram [bl]):'o bir_program_t``, ``bs:bir_state_t``, ``bl:'o bir_block_t``] bir_exec_to_labels_block) >>

`bir_get_current_block (BirProgram [bl]) bs.bst_pc = SOME bl` by (
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_get_current_block_def, bir_block_pc_def,
    bir_get_program_block_info_by_label_def, INDEX_FIND_def]
) >>
ASM_SIMP_TAC std_ss [bir_exec_to_addr_label_def] >>
DISCH_TAC >> POP_ASSUM (K ALL_TAC) >>

ASM_SIMP_TAC (std_ss ++ boolSimps.LIFT_COND_ss++bir_TYPES_ss) [LET_THM] >>
Cases_on `bs'.bst_status = BST_AssertionViolated` >- (
  `bir_state_is_terminated bs'` by ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_to_labels_def, bir_exec_to_labels_n_REWR_TERMINATED]
) >>
DISJ1_TAC >>
CONJ_TAC >- (
  CCONTR_TAC >>
  `c = 0` by DECIDE_TAC >>
  FULL_SIMP_TAC std_ss [bir_exec_block_REWR_NO_STEP]
) >- (
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [bmr_rel_IMPL_IS_BL_Block_Address]
)
QED



(******************************************)
(* Lifting a machine program to a program *)
(******************************************)


Definition bir_is_lifted_prog_def:
  bir_is_lifted_prog
    (* machine description *)
    (r: ('a, 'b, 'ms) bir_lifting_machine_rec_t)

    (* A region of memory not touched by the execution. Usually this is the part where
       the program code is stored. *)
    (mu : 'a word_interval_t)

    (* The code for the machine instruction stored somewhere (usually at the PC) stored
       in mem. This can be in multiple blocks. Moreover, you might want to add data blocks.
       Therefore a list is provided. *)
    (mms : ('a word # 'b word list) list)

    (* The program *)
    (p :'o bir_program_t)

    <=>

  (* Parameters are sensible *)
  (WI_wfe mu /\ EVERY (\mm. WF_bmr_ms_mem_contains mm /\
   WI_is_sub (bmr_ms_mem_contains_interval mm) mu) mms /\ (bir_is_valid_labels p) /\
   bir_program_string_labels_guarded p) /\

  (!ms bs li.

    (* The machine state and the bir state are related *)
    (bmr_rel r bs ms) ==>

    (* The PC points to where we expect *)
    MEM (BL_Address li) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address li)) ==>


    (* At this location in memory the expected instruction code is found *)
    EVERY (bmr_ms_mem_contains r ms) mms ==>

    (* The bir state is not terminated yet *)
    ~(bir_state_is_terminated bs) ==>

    (* Then executing till the next address label terminates and either
       violates an assertion or results in a state that corresponds to
       the machine state after one step. *)
    ?lo c_st c_addr_labels bs'.
      (bir_exec_to_addr_label p bs = BER_Ended lo c_st c_addr_labels bs') /\

      (~(bs'.bst_status = BST_AssertionViolated) ==>
      (?ms'. (r.bmr_step_fun ms = SOME ms') /\
             (bmr_ms_mem_unchanged r ms ms' mu) /\
             (bmr_rel r bs' ms'))))
End



(* Just for clarity, a trivial case, where we lifted the empty program. *)
Theorem bir_is_lifted_prog_NO_INST:
  !r mu mms p. bir_is_lifted_prog r mu mms (BirProgram []) <=>
     WI_wfe mu /\
     EVERY
       (\mm.
          WF_bmr_ms_mem_contains mm /\
          WI_is_sub (bmr_ms_mem_contains_interval mm) mu) mms
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_def,
  bir_labels_of_program_def, bir_is_valid_labels_def,
  bir_program_string_labels_guarded_def]
QED


(* More interesting is lifting a single instruction. The definition
   bir_is_lifted_inst_prog is compatible *)
Theorem bir_is_lifted_prog_SINGLE_INST:
  !r mu mm li p.
     bir_is_lifted_inst_prog r li mu mm p ==>
     bir_is_lifted_prog r mu [mm] p
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_def, bir_is_lifted_inst_prog_def]
QED



(* If we have 2 lifted programs, we can combine them. *)
Theorem bir_is_lifted_prog_UNION:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mms1 mms2 (p1 : 'o bir_program_t) p2.
     bir_is_lifted_prog r mu mms1 p1 ==>
     bir_is_lifted_prog r mu mms2 p2 ==>
     (!i. MEM (BL_Address i) (bir_labels_of_program p1) ==> ~(MEM (BL_Address i) (bir_labels_of_program p2))) ==>
     bir_is_lifted_prog r mu (mms1++mms2) (bir_program_combine p1 p2)
Proof
SIMP_TAC std_ss [bir_is_lifted_prog_def] >>
REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
`bir_is_valid_labels (bir_program_combine p1 p2)` by (
  ASM_SIMP_TAC std_ss [bir_is_valid_labels_PROGRAM_COMBINE] >>
  Tactical.REVERSE Cases >- METIS_TAC[] >>
  rename1 `BL_Label s` >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `(?i1 s1'. (BL_Label s = BL_Label_of_addr i1 s1') /\
            MEM (BL_Address i1) (bir_labels_of_program p1)) /\
   (?i2 s2'. (BL_Label s = BL_Label_of_addr i2 s2') /\
              MEM (BL_Address i2) (bir_labels_of_program p2))` by (
    FULL_SIMP_TAC std_ss [bir_program_string_labels_guarded_def, EVERY_MEM] >>
    METIS_TAC[BL_recognisers]
  ) >>
  FULL_SIMP_TAC std_ss [BL_Label_of_addr_11] >>
  METIS_TAC[]
) >>
REPEAT STRIP_TAC >- (
  ASM_SIMP_TAC list_ss []
) >- (
  ASM_REWRITE_TAC[]
) >- (
  FULL_SIMP_TAC list_ss [bir_program_string_labels_guarded_def, bir_labels_of_program_PROGRAM_COMBINE, EVERY_MEM] >>
  METIS_TAC[]
) >>

REPEAT (Q.PAT_X_ASSUM `!ms bs li. _` (MP_TAC o Q.SPECL [`ms`, `bs`, `li`])) >>
FULL_SIMP_TAC std_ss [EVERY_APPEND, bir_labels_of_program_PROGRAM_COMBINE] >>

Q.ABBREV_TAC `p' = if MEM (BL_Address li) (bir_labels_of_program p1) then p1 else p2` >>
REPEAT STRIP_TAC >>
` ?lo c c' bs'.
    (bir_exec_to_addr_label p' bs = BER_Ended lo c c' bs') /\
    (bs'.bst_status <> BST_AssertionViolated ==>
    (?ms'.
       (r.bmr_step_fun ms = SOME ms') /\
       bmr_ms_mem_unchanged r ms ms' mu /\ bmr_rel r bs' ms'))` by (
   METIS_TAC[MEM_APPEND]
) >>
REPEAT (Q.PAT_X_ASSUM `MEM (BL_Address li) _ ==> _` (K ALL_TAC)) >>

Q.ABBREV_TAC `pc_cond = (F,
      (\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))` >>

`!(p:'o bir_program_t) st. bir_exec_steps_GEN pc_cond p st (SOME 1) =
        bir_exec_to_addr_label p st` by (
  ASM_SIMP_TAC std_ss [bir_exec_to_addr_label_def,
    bir_exec_to_labels_def, bir_exec_to_labels_n_def]
) >>

`bir_is_subprogram p' (bir_program_combine p1 p2)` by
  METIS_TAC [bir_program_combine_SUBPROGRAMS] >>

`bir_is_valid_pc p' (bir_block_pc (BL_Address li))` by (
  CCONTR_TAC >>
  `bs' = bs with bst_status := BST_Failed` by (
     `bir_get_current_statement p' (bir_block_pc (BL_Address li)) = NONE` by
       METIS_TAC[bir_get_current_statement_IS_SOME, optionTheory.option_CLAUSES] >>
     Q.PAT_X_ASSUM `_ = BER_Ended _ _ _ _` MP_TAC >>
     SIMP_TAC bool_ss [bir_exec_to_addr_label_def, bir_exec_to_labels_def,
       bir_exec_to_labels_n_def] >>
     ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_steps_GEN_REWR_STEP,
       bir_exec_step_def, LET_THM, bir_state_set_failed_def,
       bir_exec_steps_GEN_REWR_TERMINATED, bir_state_is_terminated_def]
  ) >>
  Cases_on `r.bmr_pc` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bmr_rel_def, bir_machine_lifted_pc_def]
) >>

`!l. bs.bst_status <> BST_JumpOutside l` by
   FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>


Cases_on `bs'.bst_status = BST_AssertionViolated` >- (
  MP_TAC (Q.SPECL [`pc_cond`, `bs`, `SOME 1`] (ISPECL [``p':'o bir_program_t``, ``(bir_program_combine p1 p2):'o bir_program_t``] bir_exec_steps_GEN_Ended_SUBPROGRAM_EQ)) >>

  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>

MP_TAC (Q.SPECL [`pc_cond`, `bs`, `SOME 1`] (ISPECL [``p':'o bir_program_t``, ``(bir_program_combine p1 p2):'o bir_program_t``] bir_exec_steps_GEN_Ended_SUBPROGRAM)) >>

FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>

`bir_state_COUNT_PC pc_cond bs'` by (
  Cases_on `r.bmr_pc` >>
  Q.UNABBREV_TAC `pc_cond` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bmr_rel_def, bir_machine_lifted_pc_def,
      bir_state_COUNT_PC_def, bir_block_pc_def, GSPECIFICATION,
      IS_BL_Address_def]
) >>

`c' = 1` by (
  Q.PAT_X_ASSUM `_ = BER_Ended _ _ _ _` MP_TAC >>
  SIMP_TAC std_ss [bir_exec_to_addr_label_def,
    bir_exec_to_labels_def, bir_exec_to_labels_n_def,
    bir_exec_steps_GEN_1_EQ_Ended] >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `c` >> FULL_SIMP_TAC arith_ss [bir_exec_infinite_steps_fun_REWRS] >>
  METIS_TAC[]
) >>

ASM_SIMP_TAC std_ss [] >>
Tactical.REVERSE STRIP_TAC >- (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
rename1 `bs''.bst_status <> BST_AssertionViolated ==> _` >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_jumped_outside_termination_cond_def] >>
METIS_TAC[bmr_rel_RECOVER_FROM_JUMP_OUTSIDE]
QED



(* We can add extra data regions in memory *)
Theorem bir_is_lifted_prog_ADD_DATA_MEM_REGION:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mms (p : 'o bir_program_t) mm.
     bir_is_lifted_prog r mu mms p ==>
     ((WF_bmr_ms_mem_contains mm /\ WI_is_sub (bmr_ms_mem_contains_interval mm) mu)) ==>
     bir_is_lifted_prog r mu (mm::mms) p
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_def] >>
METIS_TAC[]
QED


(* The semantics of bir_is_lifted_prog uses 1-step relations. Multistep relations are
   implied. *)
Theorem bir_is_lifted_prog_MULTI_STEP_EXEC:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mms (p : 'o bir_program_t).
     bir_is_lifted_prog r mu mms p ==>
     !n ms bs.
       (bmr_rel r bs ms ==>
        (?li. MEM (BL_Address li) (bir_labels_of_program p) /\
              (bs.bst_pc = bir_block_pc (BL_Address li))) ==>
        EVERY (bmr_ms_mem_contains r ms) mms ==>
       ~bir_state_is_terminated bs ==>

       ?lo c_st c_addr_labels bs'.
         (bir_exec_to_addr_label_n p bs n = BER_Ended lo c_st c_addr_labels bs') /\
         (bs'.bst_status <> BST_AssertionViolated ==>
          ?ms'.
            (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
            bmr_ms_mem_unchanged r ms ms' mu /\
            EVERY (bmr_ms_mem_contains r ms') mms /\
            (case bs'.bst_status of
              | BST_Running =>
                  (?li. MEM (BL_Address li) (bir_labels_of_program p) /\
                        (bs'.bst_pc = bir_block_pc (BL_Address li)))
              | BST_JumpOutside ll =>
                  ~(MEM ll (bir_labels_of_program p)) /\
                  (IS_BL_Address ll)
              | _ => F) /\
            bmr_rel r bs' ms'))
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
Induct >- (
  SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_to_addr_label_n_REWR_0,
    FUNPOW_OPT_REWRS, bir_state_is_terminated_def, bmr_ms_mem_unchanged_def]
) >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_exec_to_addr_label_n_REWR_SUC] >>
FULL_SIMP_TAC std_ss [bir_is_lifted_prog_def] >>
Q.PAT_X_ASSUM `!ms bs l. _ ` (MP_TAC o Q.SPECL [`ms`, `bs`, `li`]) >>
ASM_SIMP_TAC std_ss [] >> STRIP_TAC >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
Cases_on `bs'.bst_status = BST_AssertionViolated` >- (
  `bir_state_is_terminated bs'` by ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [bir_exec_to_addr_label_n_REWR_TERMINATED]
) >>

FULL_SIMP_TAC std_ss [] >>

`(c_addr_labels = 1) /\ (?d. c_st = SUC d)` by (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_def,
    bir_exec_to_labels_n_def, bir_exec_to_labels_def, bir_exec_steps_GEN_1_EQ_Ended] >>
  `bir_state_COUNT_PC (F,
    (\pc.(pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))
    (bir_exec_infinite_steps_fun p bs c_st)` by METIS_TAC[bmr_rel_IMPL_IS_BL_Block_Address] >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `c_st` >> FULL_SIMP_TAC arith_ss [] >>
  REV_FULL_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_REWRS]
) >>

`EVERY (bmr_ms_mem_contains r ms') mms` by (
  FULL_SIMP_TAC std_ss [EVERY_MEM] >>
  METIS_TAC[bmr_ms_mem_contains_UNCHANGED]
) >>
REPEAT BasicProvers.VAR_EQ_TAC >>

Cases_on `bir_state_is_terminated bs'` >- (
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss)
               [bir_exec_to_addr_label_n_REWR_TERMINATED,
                FUNPOW_OPT_compute, bir_block_pc_11 (* Does nothing? *)] >>
  Q.PAT_X_ASSUM `bmr_rel r bs' ms'` MP_TAC >>
  Cases_on `r.bmr_pc` >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss)
               [bmr_rel_def, bir_machine_lifted_pc_def] >>
  REPEAT STRIP_TAC >| [
    FULL_SIMP_TAC std_ss [bir_state_is_terminated_def],

    ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [IS_BL_Address_def] >>
    `bir_exec_step_n p bs (SUC d) = (lo,SUC d,bs')` suffices_by
      METIS_TAC [bir_program_terminationTheory.bir_exec_step_n_status_jumped] >>
    MATCH_MP_TAC bir_exec_steps_GEN_TO_bir_exec_step_n >>
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_def,
                          bir_exec_to_labels_def,
                          bir_exec_to_labels_n_def] >>
    METIS_TAC[]
  ]
) >>

`?li.
   MEM (BL_Address li) (bir_labels_of_program p) /\
   (bs'.bst_pc = bir_block_pc (BL_Address li))` by (

  Q.PAT_X_ASSUM `bmr_rel r bs' ms'` MP_TAC >>
  Cases_on `r.bmr_pc` >>
  FULL_SIMP_TAC std_ss [bir_state_is_terminated_def] >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bmr_rel_def,
                                       bir_machine_lifted_pc_def,
                                       bir_state_is_terminated_def,
                                       bir_block_pc_11] >>
  `bir_is_valid_pc p bs'.bst_pc` suffices_by METIS_TAC [bir_is_valid_pc_block_pc] >>

  FULL_SIMP_TAC std_ss [bir_exec_to_labels_n_def, bir_exec_to_addr_label_def,
    bir_exec_to_labels_def, bir_exec_steps_GEN_1_EQ_Ended] >>
  ASM_SIMP_TAC std_ss [bir_exec_infinite_steps_fun_valid_pc, bir_is_valid_pc_block_pc]
) >>

Q.PAT_X_ASSUM `!ms' bs'. _ ` (MP_TAC o Q.SPECL [`ms'`, `bs'`]) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_block_pc_11] >>
STRIP_TAC >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [] >>
STRIP_TAC >>
rename1 `(1:num) + c'` >>
Q.SUBGOAL_THEN `1 + c' = SUC c'` SUBST1_TAC >- DECIDE_TAC >>
ASM_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
FULL_SIMP_TAC std_ss [bmr_ms_mem_unchanged_def]
QED


(* ----------------------*)
(* Efficient computation *)
(* ----------------------*)

(* If bir_is_lifted_prog_UNION is used naively, the set of labels of the program
   is computed over and over again. It is more efficient to ignore the disjointness
   during mergeing of the labels and just show it at the very end. *)


Definition bir_is_lifted_prog_LABELS_DISTINCT_def:
  bir_is_lifted_prog_LABELS_DISTINCT r mu mms ps <=>
   (ALL_DISTINCT (FILTER IS_BL_Address (bir_labels_of_program (BirProgram (FLAT ps)))) ==>
    bir_is_lifted_prog r mu (FLAT mms) (BirProgram (FLAT ps)))
End

Theorem bir_is_lifted_prog_LABELS_DISTINCT_SINGLE_INST:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mm li (bl:'o bir_block_t list).
     bir_is_lifted_inst_prog r li mu mm (BirProgram bl) ==>
     bir_is_lifted_prog_LABELS_DISTINCT r mu [[mm]] [bl]
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_LABELS_DISTINCT_def] >>
METIS_TAC[bir_is_lifted_prog_SINGLE_INST]
QED


(* A dummy program used if we can't translate a hexcode. In this case
   just the memory region is added, but no BIR block. As a result, we don't need to
   be careful about data blocks mixed with the program code. If the data is machine code
   for a valid instruction, we just get an extra part of the program we never execute.
   If it is not valid, we get a warning at runtime but can still translate the whole program.
   If the bir program tries to execute the failed hex-code, it just stops and tells the user
   "I'm at PC ... and don't know what to do!". *)

Theorem bir_is_lifted_prog_LABELS_DISTINCT_DATA:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mm.
     WI_wfe mu ==>
     bir_is_lifted_inst_block_COMPUTE_mm_WF mu mm ==>
     bir_is_lifted_prog_LABELS_DISTINCT r mu [[mm]] ([]:'o bir_block_t list list)
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_LABELS_DISTINCT_def,
  bir_is_lifted_prog_NO_INST, bir_is_lifted_inst_block_COMPUTE_mm_WF_def]
QED

(* A base case for starting with UNION *)
Theorem bir_is_lifted_prog_LABELS_DISTINCT_EMPTY:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mm.
     WI_wfe mu ==>
     bir_is_lifted_prog_LABELS_DISTINCT r mu [] ([]:'o bir_block_t list list)
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_LABELS_DISTINCT_def,
  bir_is_lifted_prog_def, bir_labels_of_program_def,
  bir_is_valid_labels_def, bir_program_string_labels_guarded_def]
QED


Theorem bir_is_lifted_prog_LABELS_DISTINCT_UNION:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mms1 mms2 (ps1 : 'o bir_block_t list list) ps2.
     bir_is_lifted_prog_LABELS_DISTINCT r mu mms1 ps1 ==>
     bir_is_lifted_prog_LABELS_DISTINCT r mu mms2 ps2 ==>
     bir_is_lifted_prog_LABELS_DISTINCT r mu (mms1++mms2) (ps1 ++ ps2)
Proof
SIMP_TAC list_ss [bir_is_lifted_prog_LABELS_DISTINCT_def] >>
REPEAT STRIP_TAC >>
`BirProgram (FLAT ps1 ++ FLAT ps2) = bir_program_combine
  (BirProgram (FLAT ps1)) (BirProgram (FLAT ps2))` by SIMP_TAC std_ss [bir_program_combine_def] >>

FULL_SIMP_TAC std_ss [bir_labels_of_program_PROGRAM_COMBINE, FILTER_APPEND, ALL_DISTINCT_APPEND,
  MEM_FILTER, IS_BL_Address_EXISTS, PULL_EXISTS] >>
METIS_TAC[bir_is_lifted_prog_UNION]
QED


Theorem bir_is_lifted_prog_LABELS_DISTINCT_ELIM:
  !(r: ('a, 'b, 'ms) bir_lifting_machine_rec_t) mu mmss (ps : 'o bir_block_t list list).
     bir_is_lifted_prog_LABELS_DISTINCT r mu mmss ps ==>
     !p mms. (BirProgram (FLAT ps) = p) ==>
             (FLAT mmss = mms) ==>
     bir_program_addr_labels_sorted p ==>
     bir_is_lifted_prog r mu mms p
Proof
SIMP_TAC std_ss [bir_is_lifted_prog_LABELS_DISTINCT_def, bir_program_addr_labels_sorted_def] >>
REPEAT STRIP_TAC >>
Q.ABBREV_TAC `p = BirProgram (FLAT ps)` >>
`ALL_DISTINCT (FILTER IS_BL_Address (bir_labels_of_program p))` suffices_by METIS_TAC[] >>

`ALL_DISTINCT (bir_label_addresses_of_program p)` by (
  IRULE_TAC sortingTheory.SORTED_ALL_DISTINCT >>
  Q.EXISTS_TAC `$<` >>
  ASM_SIMP_TAC arith_ss [relationTheory.irreflexive_def, relationTheory.transitive_def]
) >>
FULL_SIMP_TAC std_ss [bir_label_addresses_of_program_def, bir_label_addresses_of_program_labels_def] >>
METIS_TAC[ALL_DISTINCT_MAP]
QED



(* ----------------------*)
(* Merging mem regions   *)
(* ----------------------*)

Definition bmr_mem_contains_regions_EQUIV_def:
  bmr_mem_contains_regions_EQUIV r mu mms1 mms2 <=>
  (EVERY (\mm. WF_bmr_ms_mem_contains mm /\
               WI_is_sub (bmr_ms_mem_contains_interval mm) mu) mms1 =
   EVERY (\mm. WF_bmr_ms_mem_contains mm /\
               WI_is_sub (bmr_ms_mem_contains_interval mm) mu) mms2) /\
  (!ms. EVERY (bmr_ms_mem_contains r ms) mms1 =
        EVERY (bmr_ms_mem_contains r ms) mms2)
End


Theorem bir_is_lifted_prog_MMS_EQUIV:
  !r mu p mms1 mms2.
       bmr_mem_contains_regions_EQUIV r mu mms1 mms2 ==>
       (bir_is_lifted_prog r mu mms1 p <=> bir_is_lifted_prog r mu mms2 p)
Proof
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_lifted_prog_def,
  bmr_mem_contains_regions_EQUIV_def]
QED


Theorem bmr_mem_contains_regions_EQUIV_REFL:
  !r mu mms. bmr_mem_contains_regions_EQUIV r mu mms mms
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_def]
QED

Theorem bmr_mem_contains_regions_EQUIV_SYM:
  !r mu mms1 mms2. bmr_mem_contains_regions_EQUIV r mu mms1 mms2 <=>
                     bmr_mem_contains_regions_EQUIV r mu mms2 mms1
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_def] >> METIS_TAC[]
QED

Theorem bmr_mem_contains_regions_EQUIV_TRANS:
  !r mu mms1 mms2 mms3.
       bmr_mem_contains_regions_EQUIV r mu mms1 mms2 ==>
       bmr_mem_contains_regions_EQUIV r mu mms2 mms3 ==>
       bmr_mem_contains_regions_EQUIV r mu mms1 mms3
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_def] >> METIS_TAC[]
QED


Theorem bmr_mem_contains_regions_EQUIV_APPEND:
  !r mu mms1 mms1' mms2 mms2'.
       bmr_mem_contains_regions_EQUIV r mu mms1 mms1' ==>
       bmr_mem_contains_regions_EQUIV r mu mms2 mms2' ==>
       bmr_mem_contains_regions_EQUIV r mu (mms1++mms2) (mms1'++mms2')
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_def, EVERY_APPEND] >> METIS_TAC[]
QED


Theorem bmr_mem_contains_regions_EQUIV_PERM:
  !r mu mms1 mms2.
       PERM mms1 mms2 ==>
       bmr_mem_contains_regions_EQUIV r mu mms1 mms2
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_def, EVERY_MEM] >> METIS_TAC[sortingTheory.MEM_PERM]
QED


Theorem bmr_mem_contains_APPEND:
  !r ms b l1 l2. bmr_ms_mem_contains r ms (b, (l1 ++ l2)) <=>
  bmr_ms_mem_contains r ms (b, l1) /\
  bmr_ms_mem_contains r ms (b + n2w (LENGTH l1), l2)
Proof
NTAC 2 GEN_TAC >>
Induct_on `l1` >- SIMP_TAC list_ss [bmr_ms_mem_contains_def, WORD_ADD_0] >>

ASM_SIMP_TAC (list_ss++wordsLib.WORD_ss++boolSimps.EQUIV_EXTRACT_ss) [bmr_ms_mem_contains_def, n2w_SUC]
QED


Theorem WI_MEM_bmr_ms_mem_contains_interval_APPEND:
  !b l1 (l2 : 'b word list) (w:'a word).
   ((w2n b + (LENGTH (l1 ++ l2))) < dimword (:'a)) ==>

  (WI_MEM w (bmr_ms_mem_contains_interval (b,l1 ++ l2)) <=>
  WI_MEM w (bmr_ms_mem_contains_interval (b, l1)) \/
  WI_MEM w (bmr_ms_mem_contains_interval (b + n2w (LENGTH l1), l2)))
Proof
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bmr_ms_mem_contains_interval_def, WI_size_def, WI_MEM_def] >>
Cases_on `b` >> Cases_on `w` >>
rename1 `n2w b <=+ n2w w` >>
ASM_SIMP_TAC list_ss [word_ls_n2w, word_add_n2w,
  n2w_11, word_lo_n2w, w2n_n2w]
QED



Theorem bmr_mem_contains_regions_EQUIV_merge2:
  !r mu b1 l1 b2 l2.

    ((b1:'a word) + n2w (LENGTH l1) = b2) ==>
    (bmr_mem_contains_regions_EQUIV r mu [(b1, l1); (b2, l2)] [(b1, l1++l2)])
Proof
SIMP_TAC list_ss [bmr_mem_contains_regions_EQUIV_def,
  bmr_ms_mem_contains_def, bmr_mem_contains_APPEND,
  WF_bmr_ms_mem_contains_ALT_DEF] >>
REPEAT GEN_TAC >>
Cases_on `b1` >> rename1 `b1 < dimword _` >>
ASM_SIMP_TAC (arith_ss++boolSimps.CONJ_ss) [w2n_n2w, word_add_n2w] >>
SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
STRIP_TAC >>

MP_TAC (Q.SPECL [`n2w b1`, `l1`, `l2`] WI_MEM_bmr_ms_mem_contains_interval_APPEND) >>
ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [w2n_n2w, WI_is_sub_def, DISJ_IMP_THM, FORALL_AND_THM, word_add_n2w]
QED


Definition bmr_mem_contains_regions_EQUIV_MERGE_def:
  (bmr_mem_contains_regions_EQUIV_MERGE acc NONE [] = REVERSE acc) /\
   (bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b, l, b')) [] = REVERSE ((b, FLAT (REVERSE l))::acc)) /\

   (bmr_mem_contains_regions_EQUIV_MERGE acc NONE ((b, l)::mms) =
    bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b, [l], b + n2w (LENGTH l))) mms) /\

   (bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b, l, b')) ((b2, l2)::mms) =
      if (b' = b2) then
        bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b, l2::l, (b2+n2w (LENGTH l2)))) mms
      else
        bmr_mem_contains_regions_EQUIV_MERGE ((b,FLAT (REVERSE l))::acc) (SOME (b2, [l2], (b2+n2w (LENGTH l2)))) mms)
End


Theorem bmr_mem_contains_regions_EQUIV_MERGE_THM_RAW:
  !r mu acc ci mms.
      (case ci of NONE => T | SOME (b, l, b') => (b' = b + n2w (LENGTH (FLAT l)))) ==>
      bmr_mem_contains_regions_EQUIV r mu (case ci of NONE => ((REVERSE acc)++mms) | SOME (b, l, _) =>
         ((REVERSE acc)++(b, FLAT (REVERSE l))::mms))
        (bmr_mem_contains_regions_EQUIV_MERGE acc ci mms)
Proof
GEN_TAC >> GEN_TAC >>
Induct_on `mms` >- (
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >> (
    SIMP_TAC list_ss [bmr_mem_contains_regions_EQUIV_MERGE_def,
      bmr_mem_contains_regions_EQUIV_REFL]
  )
) >>
REPEAT STRIP_TAC >>
rename1 `mm::mms` >>
`?b2 l2. mm = (b2, l2)` by METIS_TAC[pairTheory.PAIR] >>
`(ci = NONE) \/ (?b l. ci = SOME (b, l, b + n2w (LENGTH (FLAT l))))` by (
  Q.PAT_X_ASSUM `option_CASE ci _ _` MP_TAC >>
  REPEAT CASE_TAC
) >- (
  Q.PAT_X_ASSUM `!acc ci. _` (MP_TAC o Q.SPECL [`acc`, `SOME (b2, [l2], b2 + n2w (LENGTH l2))`]) >>
  FULL_SIMP_TAC list_ss [bmr_mem_contains_regions_EQUIV_MERGE_def, pairTheory.pair_case_thm]
) >- (
  FULL_SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_MERGE_def, pairTheory.pair_case_thm] >>
  Cases_on `b + n2w (LENGTH (FLAT l)) = b2` >- (
    Q.PAT_X_ASSUM `!acc ci. _` (MP_TAC o Q.SPECL [`acc`, `SOME (b, l2::l, b2 + n2w (LENGTH l2))`]) >>
    REPEAT BasicProvers.VAR_EQ_TAC >>
    ASM_SIMP_TAC (list_ss++wordsLib.WORD_ss) [pairTheory.pair_case_thm, GSYM word_add_n2w] >>
    REPEAT STRIP_TAC >>
    `bmr_mem_contains_regions_EQUIV r mu
       (REVERSE acc ++ (b,FLAT (REVERSE l))::(b + n2w (LENGTH (FLAT l)),l2)::mms)
       (REVERSE acc ++ (b,FLAT (REVERSE l) ++ l2)::mms)` suffices_by METIS_TAC [
       bmr_mem_contains_regions_EQUIV_TRANS, bmr_mem_contains_regions_EQUIV_SYM] >>

    `bmr_mem_contains_regions_EQUIV r mu [(b,FLAT (REVERSE l)); (b + n2w (LENGTH (FLAT l)),l2)] [(b, FLAT (REVERSE l) ++ l2)]` by (
       MATCH_MP_TAC bmr_mem_contains_regions_EQUIV_merge2 >>
       ASM_SIMP_TAC list_ss [LENGTH_FLAT, MAP_REVERSE, rich_listTheory.SUM_REVERSE]
    ) >>
    IRULE_TAC bmr_mem_contains_regions_EQUIV_APPEND >> REPEAT CONJ_TAC >- (
      REWRITE_TAC [bmr_mem_contains_regions_EQUIV_REFL]
    ) >>
    MP_TAC (Q.SPECL [`r`, `mu`,
      `[(b,FLAT (REVERSE l)); (b + n2w (LENGTH (FLAT l)),l2)]`, `[(b,(FLAT (REVERSE l)) ++ l2)]`, `mms`, `mms`]
      bmr_mem_contains_regions_EQUIV_APPEND) >>
    ASM_SIMP_TAC list_ss [bmr_mem_contains_regions_EQUIV_REFL]
  ) >- (
    ASM_SIMP_TAC std_ss [] >>
    Q.PAT_X_ASSUM `!acc ci. _` (MP_TAC o Q.SPECL [`(b, FLAT (REVERSE l))::acc`, `SOME (b2, [l2], b2 + n2w (LENGTH l2))`]) >>
    ASM_SIMP_TAC list_ss [pairTheory.pair_case_thm] >>
    SIMP_TAC std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.REVERSE_DEF,
      listTheory.APPEND]
  )
)
QED



Theorem bmr_mem_contains_regions_EQUIV_MERGE_THM:
  !r mu mms.
      bmr_mem_contains_regions_EQUIV r mu mms
        (bmr_mem_contains_regions_EQUIV_MERGE [] NONE mms)
Proof
REPEAT GEN_TAC >>
MP_TAC (Q.SPECL [`r`, `mu`, `[]`, `NONE`, `mms`] bmr_mem_contains_regions_EQUIV_MERGE_THM_RAW) >>
SIMP_TAC list_ss []
QED


Theorem bir_is_lifted_prog_MMS_EQUIV_COMPUTE:
  !(r : ('addr_ty, 'val_ty, 'ms) bir_lifting_machine_rec_t) mu (p : 'o bir_program_t) mms1.
       bir_is_lifted_prog r mu mms1 p ==>
       (!mms2. (bmr_mem_contains_regions_EQUIV_MERGE [] NONE mms1 = mms2) ==>
               bir_is_lifted_prog r mu mms2 p)
Proof
METIS_TAC[bmr_mem_contains_regions_EQUIV_MERGE_THM, bmr_mem_contains_regions_EQUIV_SYM,
  bir_is_lifted_prog_MMS_EQUIV]
QED



Theorem bmr_mem_contains_regions_EQUIV_MERGE_REWRS:
  (!acc.
      bmr_mem_contains_regions_EQUIV_MERGE acc NONE [] = REV acc []) /\
   (!l (b':'a word) b acc.
      bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b,l,b')) [] =
      REV ((b,FLAT (REV l []))::acc) []) /\
   (!mms l b acc.
      bmr_mem_contains_regions_EQUIV_MERGE acc NONE ((n2w b,l)::mms) =
      (let b' = n2w (b + LENGTH l) in
      bmr_mem_contains_regions_EQUIV_MERGE acc
        (SOME (n2w b,[l],b')) mms)) /\
   (!mms l2 l b2 b' b acc.
     bmr_mem_contains_regions_EQUIV_MERGE acc (SOME (b,l,n2w b'))
       ((n2w b2,l2)::mms) =
     let (b2':'a word) = n2w (b2 + LENGTH l2) in
     if b' = b2 then
       bmr_mem_contains_regions_EQUIV_MERGE acc
         (SOME (b,l2::l,b2')) mms
     else if b' MOD dimword (:'a) = b2 MOD dimword (:'a) then
       bmr_mem_contains_regions_EQUIV_MERGE acc
         (SOME (b,l2::l,b2')) mms
     else
       bmr_mem_contains_regions_EQUIV_MERGE ((b,FLAT (REV l []))::acc)
         (SOME (n2w b2,[l2],b2')) mms)
Proof
SIMP_TAC std_ss [bmr_mem_contains_regions_EQUIV_MERGE_def,
  listTheory.REVERSE_REV, LET_THM, n2w_11, word_add_n2w] >>
METIS_TAC[]
QED


val _ = export_theory();
