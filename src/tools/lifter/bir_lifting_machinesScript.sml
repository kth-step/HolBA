open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_imm_expTheory
open bir_immSyntax wordsTheory
open bir_mem_expTheory bir_bool_expTheory
open bir_exp_liftingTheory
open bir_temp_varsTheory
open bir_programTheory
open bir_program_labelsTheory;

open arm8Theory arm8_stepTheory
open m0Theory m0_stepTheory

(* The lifting library is in principle able to lift
   machine code for multiple architectures. However,
   it needs instantiating for each architecture. This
   is provided by this library. *)

val _ = new_theory "bir_lifting_machines";


(*****************)
(* General stuff *)
(*****************)

(*--------------*)
(* Lifting Imms *)
(*--------------*)

val _ = Datatype `bir_machine_lifted_imm_t = BMLI bir_var_t ('ms -> bir_imm_t)`

val bir_machine_lifted_imm_OK_def = Define `bir_machine_lifted_imm_OK (BMLI v (lf : 'ms -> bir_imm_t)) <=>
(~(bir_is_temp_var_name (bir_var_name v))) /\
(!ms. BType_Imm (type_of_bir_imm (lf ms)) = (bir_var_type v))`;


val bir_machine_lifted_imm_def = Define `bir_machine_lifted_imm (BMLI v lf) bs ms <=>

(bir_env_read v bs.bst_environ = BVal_Imm (lf ms)) /\
(bir_env_var_is_declared bs.bst_environ (bir_temp_var T v))`;


val bir_machine_lifted_imm_OK_IMPLIES_NO_TEMP_VAR = store_thm ("bir_machine_lifted_imm_OK_IMPLIES_NO_TEMP_VAR",
  ``!v lf. bir_machine_lifted_imm_OK (BMLI v lf) ==>
               ~(bir_is_temp_var_name (bir_var_name v))``,
SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def]);


val bir_machine_lifted_imm_INITIALISED = store_thm ("bir_machine_lifted_imm_INITIALISED",
  ``!v lf bs ms. bir_machine_lifted_imm_OK (BMLI v lf) ==>
                 bir_machine_lifted_imm (BMLI v lf) bs ms ==>
                 (bir_env_var_is_initialised bs.bst_environ v)``,
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def, bir_machine_lifted_imm_OK_def,
  bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_UNKNOWN,
  type_of_bir_val_def]);


val bir_machine_lifted_imm_DECLARED = store_thm ("bir_machine_lifted_imm_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_imm (BMLI v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def, bir_env_var_is_declared_def,
  bir_env_read_NEQ_UNKNOWN, bir_env_lookup_type_def]);


val bir_machine_lifted_imm_DECLARED_TEMP = store_thm ("bir_machine_lifted_imm_DECLARED_TEMP",
  ``!v ty lf bs ms use_temp.
       bir_machine_lifted_imm (BMLI v lf) bs ms ==>
       (bir_env_var_is_declared bs.bst_environ (bir_temp_var use_temp v))``,
Cases_on `use_temp` >- SIMP_TAC std_ss [bir_machine_lifted_imm_def] >>
REWRITE_TAC[bir_temp_var_REWRS] >>
METIS_TAC[bir_machine_lifted_imm_DECLARED]);


val bir_machine_lifted_imm_LIFTED = store_thm ("bir_machine_lifted_imm_LIFTED",
  ``!v lf bs ms. bir_machine_lifted_imm_OK (BMLI v lf) ==>
                 bir_machine_lifted_imm (BMLI v lf) bs ms ==>
                 (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Imm (lf ms)))
``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def,
  bir_machine_lifted_imm_OK_def,
  bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def,
  bir_eval_exp_def, type_of_bir_exp_def,
  bir_var_type_def, bir_vars_of_exp_def,
  bir_env_vars_are_initialised_INSERT,
  bir_env_vars_are_initialised_EMPTY,
  bir_env_var_is_initialised_def,
  bir_env_read_NEQ_UNKNOWN, type_of_bir_val_def]);


val bir_machine_lifted_imms_def = Define `bir_machine_lifted_imms vl bs ms =
EVERY (\vlf. bir_machine_lifted_imm vlf bs ms) vl`;


(*-------------*)
(* Lifting Mem *)
(*-------------*)


val _ = Datatype `bir_machine_lifted_mem_t = BMLM bir_var_t ('ms -> 'a word -> 'b word)`

val bir_machine_lifted_mem_OK_def = Define `bir_machine_lifted_mem_OK (BMLM v (lf : 'ms -> 'a word -> 'b word)) <=>
  (?sa sb.
     (bir_var_type v = BType_Mem sa sb) /\
     (size_of_bir_immtype sa = (dimindex (:'a))) /\
     (size_of_bir_immtype sb = (dimindex (:'b))) /\
     (~(bir_is_temp_var_name (bir_var_name v))))`;


val bir_machine_lifted_mem_def = Define `bir_machine_lifted_mem (BMLM v lf) bs ms <=>

?sa sb mem_n. (bir_var_type v = BType_Mem sa sb) /\
(bir_env_read v bs.bst_environ = BVal_Mem sa sb mem_n) /\
(lf ms = (\a. n2w (mem_n (w2n a)))) /\
(bir_env_var_is_declared bs.bst_environ (bir_temp_var T v))`;


val bir_machine_lifted_mem_OK_IMPLIES_NO_TEMP_VAR = store_thm ("bir_machine_lifted_mem_OK_IMPLIES_NO_TEMP_VAR",
  ``!v lf. bir_machine_lifted_mem_OK (BMLM v lf) ==>
               ~(bir_is_temp_var_name (bir_var_name v))``,
SIMP_TAC std_ss [bir_machine_lifted_mem_OK_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_INITIALISED = store_thm ("bir_machine_lifted_mem_INITIALISED",
  ``!v lf bs ms. bir_machine_lifted_mem_OK (BMLM v lf) ==>
                 bir_machine_lifted_mem (BMLM v lf) bs ms ==>
                 (bir_env_var_is_initialised bs.bst_environ v)``,
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def, bir_machine_lifted_mem_OK_def,
  bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_UNKNOWN,
  type_of_bir_val_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_DECLARED = store_thm ("bir_machine_lifted_mem_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_mem (BMLM v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def, bir_env_var_is_declared_def,
  bir_env_read_NEQ_UNKNOWN, bir_env_lookup_type_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_DECLARED_TEMP = store_thm ("bir_machine_lifted_mem_DECLARED_TEMP",
  ``!v ty lf bs ms use_temp.
       bir_machine_lifted_mem (BMLM v lf) bs ms ==>
       (bir_env_var_is_declared bs.bst_environ (bir_temp_var use_temp v))``,
Cases_on `use_temp` >- SIMP_TAC std_ss [bir_machine_lifted_mem_def, GSYM LEFT_FORALL_IMP_THM] >>
REWRITE_TAC[bir_temp_var_REWRS] >>
METIS_TAC[bir_machine_lifted_mem_DECLARED]);


val bir_machine_lifted_mem_LIFTED = store_thm ("bir_machine_lifted_mem_LIFTED",
  ``!v lf bs ms. bir_machine_lifted_mem_OK (BMLM v lf) ==>
                 bir_machine_lifted_mem (BMLM v lf) bs ms ==>
                 (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Mem (lf ms)))
``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def,
  bir_machine_lifted_mem_OK_def,
  bir_is_lifted_exp_def, bir_is_lifted_mem_exp_def,
  bir_eval_exp_def, type_of_bir_exp_def,
  bir_var_type_def, bir_vars_of_exp_def,
  bir_env_vars_are_initialised_INSERT,
  bir_env_vars_are_initialised_EMPTY,
  bir_env_var_is_initialised_def,
  bir_env_read_NEQ_UNKNOWN, type_of_bir_val_def,
  GSYM LEFT_FORALL_IMP_THM]);




(*----*)
(* PC *)
(*----*)


val _ = Datatype `bir_machine_lifted_pc_t = BMLPC bir_var_t bir_var_t ('ms -> bir_imm_t)`

val bir_machine_lifted_pc_OK_def = Define `bir_machine_lifted_pc_OK (BMLPC v_pc v_pc_cond (lf : 'ms -> bir_imm_t)) <=>
  (bir_is_temp_var_name (bir_var_name v_pc)) /\
  (bir_is_temp_var_name (bir_var_name v_pc_cond)) /\
  (!ms. BType_Imm (type_of_bir_imm (lf ms)) = (bir_var_type v_pc)) /\
  (bir_var_type v_pc_cond = BType_Bool)`;


val bir_machine_lifted_pc_def = Define `bir_machine_lifted_pc (BMLPC v_pc v_pc_cond lf) bs ms <=>

(bir_env_var_is_declared bs.bst_environ v_pc) /\
(bir_env_var_is_declared bs.bst_environ v_pc_cond) /\
(((bs.bst_pc = bir_block_pc (BL_Address (lf ms))) /\ (bs.bst_status = BST_Running)) \/
(bs.bst_status = BST_JumpOutside (BL_Address (lf ms))))`;


val bir_machine_lifted_pc_DECLARED = store_thm ("bir_machine_lifted_pc_DECLARED",
  ``!v_pc v_pc_cond lf bs ms.
      bir_machine_lifted_pc (BMLPC v_pc v_pc_cond lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v_pc) /\
      (bir_env_var_is_declared bs.bst_environ v_pc_cond)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_pc_def]);



(***********************************************************)
(* A record linking a bir-state and the state of a machine *)
(***********************************************************)


val _ = Datatype `bir_lifting_machine_rec_t =
   <| (* a list of lifted immediate values *)
      bmr_imms : ('machine_state bir_machine_lifted_imm_t) list;

      (* The lifted memory *)
      bmr_mem : ('a, 'b, 'machine_state) bir_machine_lifted_mem_t;

      (* The PC *)
      bmr_pc : 'machine_state bir_machine_lifted_pc_t;

      (* Well formed state conditions, like we are in user mode ... *)
      bmr_extra : 'machine_state -> bool;

      (* The step function for this machine *)
      bmr_step_fun : 'machine_state -> 'machine_state option
   |>`;

val bmr_ss = rewrites (
   (type_rws ``:('a, 'b, 'c) bir_lifting_machine_rec_t``) @
   (type_rws ``:'a bir_machine_lifted_pc_t``) @
   (type_rws ``:'a bir_machine_lifted_imm_t``) @
   (type_rws ``:('a, 'b, 'c) bir_machine_lifted_mem_t``)
)
;


val bmr_mem_lf_def = Define `bmr_mem_lf r = case r.bmr_mem of BMLM v lf => lf`
val bmr_mem_var_def = Define `bmr_mem_var r = case r.bmr_mem of BMLM v lf => v`
val bmr_pc_lf_def = Define `bmr_pc_lf r = case r.bmr_pc of BMLPC v_pc v_pc_cond lf => lf`
val bmr_pc_var_def = Define `bmr_pc_var r = case r.bmr_pc of BMLPC v_pc v_pc_cond lf => v_pc`
val bmr_pc_var_cond_def = Define `bmr_pc_var_cond r = case r.bmr_pc of BMLPC v_pc v_pc_cond lf => v_pc_cond`;

val bmr_mem_addr_sz_def = Define `bmr_mem_addr_sz r =
  (case (bir_var_type (bmr_mem_var r)) of
      (BType_Mem addr_sz _) => addr_sz)`;

val bmr_mem_val_sz_def = Define `bmr_mem_val_sz r =
  (case (bir_var_type (bmr_mem_var r)) of
      (BType_Mem _ val_sz) => val_sz)`;

val bmr_vars_def = Define `bmr_vars r =
  (case r.bmr_mem of (BMLM v _) => v)::
  (MAP (\i. case i of (BMLI v _) => v) r.bmr_imms)`;

val bmr_temp_vars_def = Define `bmr_temp_vars r =
  (case r.bmr_pc of BMLPC v1 v2 _ => [v1;v2]) ++
  (MAP (bir_temp_var T) (bmr_vars r))`;

val bmr_varnames_distinct_def = Define `
  bmr_varnames_distinct r <=>
  ALL_DISTINCT (MAP bir_var_name (bmr_vars r ++ bmr_temp_vars r))`

val bmr_ok_def = Define `bmr_ok r <=>
(EVERY bir_machine_lifted_imm_OK r.bmr_imms) /\
(bir_machine_lifted_mem_OK r.bmr_mem) /\
(bir_machine_lifted_pc_OK r.bmr_pc) /\
(bmr_varnames_distinct r)`;


val bmr_rel_def = Define `bmr_rel r bs ms <=>
(EVERY (\i. bir_machine_lifted_imm i bs ms) r.bmr_imms) /\
(bir_machine_lifted_mem r.bmr_mem bs ms) /\
(bir_machine_lifted_pc r.bmr_pc bs ms) /\
(r.bmr_extra ms)`

val bmr_rel_implies_extra = store_thm ("bmr_rel_implies_extra",
 ``!r bs ms. bmr_rel r bs ms ==> r.bmr_extra ms``,
SIMP_TAC std_ss [bmr_rel_def]);

val MEM_bmr_vars = store_thm ("MEM_bmr_vars",
``!r v. MEM v (bmr_vars r) <=> (?mf. r.bmr_mem = (BMLM v mf)) \/
                               (?lf. MEM (BMLI v lf) r.bmr_imms)``,

SIMP_TAC list_ss [bmr_vars_def, MEM_MAP] >>
REPEAT STRIP_TAC >> EQ_TAC >| [
  SIMP_TAC std_ss [DISJ_IMP_THM, PULL_EXISTS] >>
  CONJ_TAC >> REPEAT GEN_TAC >> REPEAT CASE_TAC >>
  METIS_TAC[],

  SIMP_TAC (std_ss++bmr_ss) [DISJ_IMP_THM, PULL_EXISTS] >>
  REPEAT STRIP_TAC >>
  DISJ2_TAC >>
  Q.EXISTS_TAC `BMLI v lf` >>
  ASM_SIMP_TAC (std_ss++bmr_ss) []
]);


val MEM_bmr_temp_vars = store_thm ("MEM_bmr_temp_vars",
``!r v. MEM v (bmr_temp_vars r) <=>

      (?v'. MEM v' (bmr_vars r) /\
            (v = bir_temp_var T v')) \/
      (?v_pc v_pc_cond lf. (r.bmr_pc = BMLPC v_pc v_pc_cond lf) /\
                           ((v = v_pc) \/ (v = v_pc_cond)))``,

SIMP_TAC list_ss [bmr_temp_vars_def, MEM_MAP] >>
REPEAT GEN_TAC >>
Cases_on `r.bmr_pc` >> rename1 `BMLPC v_pc v_pc_cond lf` >>
SIMP_TAC (list_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
METIS_TAC[]);



val bmr_vars_NO_TEMP_VAR = store_thm ("bmr_vars_NO_TEMP_VAR",
  ``!r. bmr_ok r ==>
    EVERY (\v. ~(bir_is_temp_var_name (bir_var_name v))) (bmr_vars r)``,

SIMP_TAC list_ss [bmr_ok_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  FULL_SIMP_TAC std_ss [bir_machine_lifted_mem_OK_def],

  `bir_machine_lifted_imm_OK (BMLI v lf)` by METIS_TAC[] >>
  FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def]
])


val bmr_temp_vars_TEMP_VAR = store_thm ("bmr_temp_vars_TEMP_VAR",
  ``!r. bmr_ok r ==>
    EVERY (\v. (bir_is_temp_var_name (bir_var_name v))) (bmr_temp_vars r)``,

SIMP_TAC list_ss [bmr_ok_def, EVERY_MEM, MEM_bmr_temp_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, bir_temp_var_REWRS,
  bir_is_temp_var_name_REWR] >>
REPEAT STRIP_TAC >> FULL_SIMP_TAC std_ss [bir_machine_lifted_pc_OK_def]);



val bmr_vars_IN_TEMP = store_thm ("bmr_vars_IN_TEMP",
``!r v. MEM v (bmr_vars r) ==> MEM (bir_temp_var T v) (bmr_temp_vars r)``,

SIMP_TAC list_ss [bmr_temp_vars_def, MEM_MAP] >>
METIS_TAC[]);



val bmr_vars_INITIALISED = store_thm ("bmr_vars_INITIALISED",
``!r bs ms. bmr_ok r ==> bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_initialised bs.bst_environ) (bmr_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_INITIALISED],
  METIS_TAC[bir_machine_lifted_imm_INITIALISED]
]);


val bmr_vars_DECLARED = store_thm ("bmr_vars_DECLARED",
``!r bs ms. bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_DECLARED],
  METIS_TAC[bir_machine_lifted_imm_DECLARED]
]);


val bmr_temp_vars_DECLARED = store_thm ("bmr_temp_vars_DECLARED",
``!r bs ms. bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_temp_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_temp_vars, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_DECLARED_TEMP],
  METIS_TAC[bir_machine_lifted_imm_DECLARED_TEMP],
  METIS_TAC[bir_machine_lifted_pc_DECLARED],
  METIS_TAC[bir_machine_lifted_pc_DECLARED]
]);


val bmr_lifted = store_thm ("bmr_lifted",
``!r.
   bmr_ok r ==>
   !bs ms. bmr_rel r bs ms ==>

     (EVERY (\i. case i of BMLI v lf =>
        (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Imm (lf ms)))) r.bmr_imms /\
     (case r.bmr_mem of BMLM v lf =>
        (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Mem (lf ms)))))``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM] >>
REPEAT STRIP_TAC >| [
  `bir_machine_lifted_imm_OK i /\ bir_machine_lifted_imm i bs ms` by METIS_TAC[] >>
  Cases_on `i` >>
  FULL_SIMP_TAC (std_ss++bmr_ss) [] >>
  METIS_TAC[bir_machine_lifted_imm_LIFTED],

  Cases_on `r.bmr_mem` >>
  FULL_SIMP_TAC (std_ss++bmr_ss) [] >>
  METIS_TAC[bir_machine_lifted_mem_LIFTED]
]);


val bmr_rel_IMPL_IS_BL_Block_Address = store_thm ("bmr_rel_IMPL_IS_BL_Block_Address",
  ``!r bs ms. bmr_rel r bs ms ==>
    bir_state_COUNT_PC
       (F,(\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l})) bs``,

SIMP_TAC std_ss [bmr_rel_def, bir_state_COUNT_PC_def] >>
REPEAT STRIP_TAC >>
Cases_on `r.bmr_pc` >> (
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_pc_def,
    bir_block_pc_def, pred_setTheory.GSPECIFICATION, IS_BL_Address_def]
));


val bmr_rel_RECOVER_FROM_JUMP_OUTSIDE = store_thm ("bmr_rel_RECOVER_FROM_JUMP_OUTSIDE",
  ``!r bs ms l.
      bmr_rel r bs ms ==>
      (bs.bst_status = BST_JumpOutside l) ==>
      (bmr_rel r (bs with <| bst_status := BST_Running; bst_pc := bir_block_pc l|>) ms)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bmr_rel_def, EVERY_MEM] >>
REPEAT STRIP_TAC >- (
  Q.PAT_X_ASSUM `!i. _` (MP_TAC o Q.SPEC `i`) >>
  Cases_on `i` >>
  ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def]
) >- (
  Cases_on `r.bmr_mem` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def]
) >- (
  Cases_on `r.bmr_pc` >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_pc_def]
));



(*-----------------------*)
(* Program stored in mem *)
(*-----------------------*)

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



(**********)
(* ARM 8  *)
(**********)

(* Lifting REGs *)

val arm8_REGS_lifted_imms_LIST_def = Define `
  arm8_REGS_lifted_imms_LIST =
    (MAP (\n. (BMLI (BVar (STRCAT "R" (n2s 10 HEX n)) (BType_Imm Bit64))
               (\ms:arm8_state. Imm64 (ms.REG (n2w n)))))  (COUNT_LIST 32))`;

val arm8_REGS_lifted_imms_LIST_EVAL = save_thm ("arm8_REGS_lifted_imms_LIST_EVAL",
  EVAL ``arm8_REGS_lifted_imms_LIST``);


(* Lifting PSTATE *)
val arm8_PSTATE_lifted_imms_LIST_def = Define `
  arm8_PSTATE_lifted_imms_LIST = [
    (BMLI (BVar "ProcState_C" BType_Bool) (\ms. bool2b (ms.PSTATE.C)));
    (BMLI (BVar "ProcState_N" BType_Bool) (\ms. bool2b (ms.PSTATE.N)));
    (BMLI (BVar "ProcState_V" BType_Bool) (\ms. bool2b (ms.PSTATE.V)));
    (BMLI (BVar "ProcState_Z" BType_Bool) (\ms:arm8_state. bool2b (ms.PSTATE.Z)))
]`;


(* Lifting special stuff *)
val arm8_EXTRA_lifted_imms_LIST_def = Define `
  arm8_EXTRA_lifted_imms_LIST = [
    (BMLI (BVar "SP_EL0" (BType_Imm Bit64)) (\ms:arm8_state. Imm64 (ms.SP_EL0)));
    (BMLI (BVar "SP_EL1" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL1)));
    (BMLI (BVar "SP_EL2" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL2)));
    (BMLI (BVar "SP_EL3" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL3)))
  ]`;


val arm8_lifted_mem_def = Define `
  arm8_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit64 Bit8)) (\ms:arm8_state. ms.MEM)`

val arm8_lifted_pc_def = Define `
  arm8_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit64))
                         (BVar (bir_temp_var_name "COND") BType_Bool)
                         (\ms:arm8_state. Imm64 (ms.PC))`

(* Well defined state *)
val arm8_state_is_OK_def = Define `arm8_state_is_OK (ms:arm8_state) <=> (
   ~ms.SCTLR_EL1.E0E ∧ (ms.PSTATE.EL = 0w) ∧ (ms.exception = NoException) /\
   ~ms.SCTLR_EL1.SA0 /\
   ~ms.TCR_EL1.TBI0 /\
   ~ms.TCR_EL1.TBI1)`

val arm8_bmr_def = Define `arm8_bmr = <|
  bmr_extra := \ms. arm8_state_is_OK ms;
  bmr_imms := (arm8_PSTATE_lifted_imms_LIST ++ arm8_REGS_lifted_imms_LIST ++ arm8_EXTRA_lifted_imms_LIST);
  bmr_mem := arm8_lifted_mem;
  bmr_pc := arm8_lifted_pc;
  bmr_step_fun := NextStateARM8 |>`;

val arm8_bmr_EVAL = save_thm ("arm8_bmr_EVAL",
  SIMP_CONV list_ss [arm8_bmr_def, arm8_state_is_OK_def,
    arm8_REGS_lifted_imms_LIST_EVAL, arm8_PSTATE_lifted_imms_LIST_def,
    arm8_EXTRA_lifted_imms_LIST_def, arm8_lifted_mem_def,
    arm8_lifted_pc_def, bir_temp_var_name_def, arm8_state_is_OK_def]
    ``arm8_bmr``
);


val arm8_bmr_vars_EVAL = save_thm ("arm8_bmr_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, bmr_vars_def] ``bmr_vars arm8_bmr``);

val arm8_bmr_temp_vars_EVAL = save_thm ("arm8_bmr_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
  bir_temp_var_def, bir_temp_var_name_def]
  ``bmr_temp_vars arm8_bmr``);

val arm8_bmr_varnames_distinct = prove (``
  bmr_varnames_distinct arm8_bmr``,
SIMP_TAC std_ss [bmr_varnames_distinct_def,
  arm8_bmr_vars_EVAL, arm8_bmr_temp_vars_EVAL, MAP, MAP, bir_var_name_def,
  APPEND] >>
SIMP_TAC (list_ss++stringSimps.STRING_ss) [ALL_DISTINCT]);


val arm8_bmr_OK = store_thm ("arm8_bmr_OK",
  ``bmr_ok arm8_bmr``,

SIMP_TAC std_ss [bmr_ok_def, arm8_bmr_varnames_distinct] >>
SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  arm8_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def,
  bmr_varnames_distinct_def]);

val arm8_bmr_rel_EVAL = save_thm ("arm8_bmr_rel_EVAL",
SIMP_CONV (list_ss++bmr_ss++holBACore_ss) [
  bmr_rel_def, arm8_bmr_EVAL,
  bir_machine_lifted_mem_def, bir_machine_lifted_imm_def,
  bir_is_temp_var_name_def, BType_Bool_def, bir_temp_var_name_def,
  bir_machine_lifted_pc_def, bir_temp_var_def,
  GSYM CONJ_ASSOC]
``bmr_rel arm8_bmr bs ms``);


val arm8_bmr_LIFTED = save_thm ("arm8_bmr_LIFTED",
let
  val thm0 = MATCH_MP bmr_lifted arm8_bmr_OK
  val c = SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
in
  thm1
end);


val arm8_bmr_label_thm = store_thm ("arm8_bmr_label_thm",
``!ms n. (BL_Address (bmr_pc_lf arm8_bmr ms) = BL_Address (Imm64 (n2w n))) ==>
         (ms.PC = n2w n)``,
SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, arm8_bmr_EVAL]);


val bmr_ms_mem_contains_ARM8 = store_thm ("bmr_ms_mem_contains_ARM8",
``!ms v1 v2 v3 v4.
  (bmr_ms_mem_contains arm8_bmr ms (ms.PC, [v1; v2; v3; v4]) <=>
  ((ms.MEM ms.PC = v1) /\ (ms.MEM (ms.PC + 1w) = v2) /\ (ms.MEM (ms.PC + 2w) = v3) /\
   (ms.MEM (ms.PC + 3w) = v4)))``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def,
  arm8_bmr_EVAL, bmr_mem_lf_def]);


val bmr_extra_ARM8 = store_thm ("bmr_extra_ARM8",
``!ms.
  arm8_bmr.bmr_extra ms = (~ms.SCTLR_EL1.E0E /\ (ms.PSTATE.EL = 0w) /\
  (ms.exception = NoException) /\ ~ms.SCTLR_EL1.SA0 /\
  ~ms.TCR_EL1.TBI0 /\ ~ms.TCR_EL1.TBI1)``,

SIMP_TAC (std_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss) [arm8_bmr_EVAL]);



(**********)
(* ARM M0 *)
(**********)
(* Lifting REGs *)

val m0_REGS_lifted_imms_LIST_def = Define `
  m0_REGS_lifted_imms_LIST = [
    (BMLI (BVar "R0" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 0w))));
    (BMLI (BVar "R1" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 1w))));
    (BMLI (BVar "R2" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 2w))));
    (BMLI (BVar "R3" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 3w))));
    (BMLI (BVar "R4" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 4w))));
    (BMLI (BVar "R5" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 5w))));
    (BMLI (BVar "R6" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 6w))));
    (BMLI (BVar "R7" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 7w))));
    (BMLI (BVar "R8" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 8w))));
    (BMLI (BVar "R9" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 9w))));
    (BMLI (BVar "R10" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 10w))));
    (BMLI (BVar "R11" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 11w))));
    (BMLI (BVar "R12" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 12w))));
    (BMLI (BVar "LR" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 14w))));
    (BMLI (BVar "SP_main" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name F 13w))));
    (BMLI (BVar "SP_process" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG (R_name T 13w))))]`;


val m0_REGS_lifted_imms_LIST_REWRS = save_thm ("m0_REGS_lifted_imms_LIST_REWRS",
  SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] m0_REGS_lifted_imms_LIST_def);


val m0_lifted_mem_def = Define `
  m0_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit32 Bit8)) (\ms:m0_state. ms.MEM)`

val m0_lifted_pc_def = Define `
  m0_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit32))
                       (BVar (bir_temp_var_name "COND") BType_Bool)
                       (\ms:m0_state. Imm32 (ms.REG RName_PC))`


(* Just a dummy for now *)
val m0_bmr_def = Define `m0_bmr = <|
  bmr_extra := \ms:m0_state. T;
  bmr_imms := m0_REGS_lifted_imms_LIST;
  bmr_mem := m0_lifted_mem;
  bmr_pc := m0_lifted_pc;
  bmr_step_fun := NextStateM0 |>`;


val m0_bmr_EVAL = save_thm ("m0_bmr_EVAL",
  SIMP_CONV list_ss [m0_bmr_def,
    m0_REGS_lifted_imms_LIST_def, m0_lifted_mem_def,
    m0_lifted_pc_def, bir_temp_var_name_def, arm8_state_is_OK_def]
    ``m0_bmr``
);

val m0_bmr_vars_EVAL = save_thm ("m0_bmr_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, bmr_vars_def] ``bmr_vars m0_bmr``);

val m0_bmr_temp_vars_EVAL = save_thm ("m0_bmr_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
  bir_temp_var_def, bir_temp_var_name_def]
  ``bmr_temp_vars m0_bmr``);

val m0_bmr_varnames_distinct = prove (``
  bmr_varnames_distinct m0_bmr``,
SIMP_TAC std_ss [bmr_varnames_distinct_def,
  m0_bmr_vars_EVAL, m0_bmr_temp_vars_EVAL, MAP, MAP, bir_var_name_def,
  APPEND] >>
SIMP_TAC (list_ss++stringSimps.STRING_ss) [ALL_DISTINCT]);


val m0_bmr_OK = store_thm ("m0_bmr_OK",
  ``bmr_ok m0_bmr``,

SIMP_TAC std_ss [bmr_ok_def, m0_bmr_varnames_distinct] >>
SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  m0_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def]);


val m0_bmr_label_thm = store_thm ("m0_bmr_label_thm",
``!ms n. (BL_Address (bmr_pc_lf m0_bmr ms) = BL_Address (Imm32 (n2w n))) ==>
         (ms.REG RName_PC = n2w n)``,
SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, m0_bmr_EVAL]);


val m0_bmr_LIFTED = save_thm ("m0_bmr_LIFTED",
let
  val thm0 = MATCH_MP bmr_lifted m0_bmr_OK
  val c = SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
  val thm2 = SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] thm1

  val thm3 = SIMP_RULE (std_ss++boolSimps.CONJ_ss) [GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM, GSYM CONJ_ASSOC] (CONJ thm1 thm2)
in
  thm3
end);



val _ = export_theory();
