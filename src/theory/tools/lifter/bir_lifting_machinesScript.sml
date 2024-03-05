(* For compilation: *)
open HolKernel Parse boolLib bossLib
(* Generic HOL theories: *)
open rich_listTheory listTheory wordsTheory
(* Architecture-specific theories from the examples/l3-machine-code
 * directory. *)
open arm8Theory arm8_stepTheory
     m0_mod_stepTheory
     m0Theory m0_stepTheory
     riscvTheory riscv_stepTheory
(* Theories from HolBA/src/core: *)
open bir_expTheory bir_typing_expTheory bir_valuesTheory
     bir_envTheory bir_immTheory bir_exp_immTheory 
     bir_exp_memTheory bir_programTheory
(* Theories from HolBA/src/core-props: *)
open bir_bool_expTheory bir_program_labelsTheory
     bir_interval_expTheory bir_temp_varsTheory
(* Local theories: *)
open bir_exp_liftingTheory
(* Syntaxes from HolBA/src/core: *)
open bir_immSyntax
(* HolBA simplification set: *)
open HolBACoreSimps

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

(bir_env_read v bs.bst_environ = SOME (BVal_Imm (lf ms))) /\
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
  bir_env_oldTheory.bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_NONE,
  type_of_bir_val_def]);


val bir_machine_lifted_imm_DECLARED = store_thm ("bir_machine_lifted_imm_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_imm (BMLI v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def, bir_env_oldTheory.bir_env_var_is_declared_def,
  bir_env_read_NEQ_NONE, bir_env_lookup_type_def]);


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
  bir_env_oldTheory.bir_env_vars_are_initialised_INSERT,
  bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  bir_env_oldTheory.bir_env_var_is_initialised_def,
  bir_env_read_NEQ_NONE, type_of_bir_val_def]);


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
(bir_env_read v bs.bst_environ = SOME (BVal_Mem sa sb mem_n)) /\
(lf ms = (\a. n2w (bir_load_mmap mem_n (w2n a)))) /\
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
  bir_env_oldTheory.bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_NONE,
  type_of_bir_val_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_DECLARED = store_thm ("bir_machine_lifted_mem_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_mem (BMLM v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def, bir_env_read_def, GSYM bir_env_oldTheory.bir_env_var_is_declared_ALT_DEF] >>
REPEAT STRIP_TAC
);


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
  bir_env_oldTheory.bir_env_vars_are_initialised_INSERT,
  bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  bir_env_oldTheory.bir_env_var_is_initialised_def,
  bir_env_read_NEQ_NONE, type_of_bir_val_def,
  GSYM LEFT_FORALL_IMP_THM] >>
  REWRITE_TAC [n2w_bir_load_mmap_w2n_thm]
);




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
     ((bmr_mem_lf r ms ba = (v:'b word)) /\
     (bmr_ms_mem_contains r ms (ba+1w, vs))))`;

val bmr_ms_mem_contains_interval_def = Define `
  bmr_ms_mem_contains_interval (ba: 'a word, wl:'b word list) <=>
  (WI_size ba (n2w (LENGTH wl)))`;

val WF_bmr_ms_mem_contains_def = Define `WF_bmr_ms_mem_contains (ba: 'a word, wl:'b word list) <=>
  (LENGTH wl < dimword (:'a)) /\
  (WI_wf (bmr_ms_mem_contains_interval (ba, wl)))`;

val WF_bmr_ms_mem_contains_ALT_DEF = store_thm ("WF_bmr_ms_mem_contains_ALT_DEF",
 ``!(wl:'b word list) (b:'a word).
   WF_bmr_ms_mem_contains (b,wl) <=>
   (w2n b + LENGTH wl < dimword (:'a))``,

SIMP_TAC std_ss [WF_bmr_ms_mem_contains_def, WI_wf_def, bmr_ms_mem_contains_interval_def,
  WI_wf_size, bir_nzcv_expTheory.nzcv_BIR_ADD_C_CARRY_DEF, bir_nzcv_expTheory.awc_BIR_C_def,
  add_with_carry_def, LET_THM, n2w_w2n, w2n_n2w] >>
SIMP_TAC (arith_ss++boolSimps.CONJ_ss) []);


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
  val c =
    SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
in
  thm1
end);


val arm8_bmr_label_thm = store_thm ("arm8_bmr_label_thm",
``!ms n hc. (BL_Address (bmr_pc_lf arm8_bmr ms) = BL_Address_HC (Imm64 (n2w n)) hc) ==>
            (ms.PC = n2w n)``,
SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, arm8_bmr_EVAL,
  BL_Address_HC_def]);


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
    (BMLI (BVar "PSR_C" BType_Bool) (\ms:m0_state. bool2b (ms.PSR.C)));
    (BMLI (BVar "PSR_N" BType_Bool) (\ms:m0_state. bool2b (ms.PSR.N)));
    (BMLI (BVar "PSR_V" BType_Bool) (\ms:m0_state. bool2b (ms.PSR.V)));
    (BMLI (BVar "PSR_Z" BType_Bool) (\ms:m0_state. bool2b (ms.PSR.Z)));
    (BMLI (BVar "R0" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 0w))));
    (BMLI (BVar "R1" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 1w))));
    (BMLI (BVar "R2" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 2w))));
    (BMLI (BVar "R3" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 3w))));
    (BMLI (BVar "R4" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 4w))));
    (BMLI (BVar "R5" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 5w))));
    (BMLI (BVar "R6" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 6w))));
    (BMLI (BVar "R7" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 7w))));
    (BMLI (BVar "R8" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 8w))));
    (BMLI (BVar "R9" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 9w))));
    (BMLI (BVar "R10" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 10w))));
    (BMLI (BVar "R11" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 11w))));
    (BMLI (BVar "R12" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 12w))));
    (BMLI (BVar "LR" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 14w))));
    (BMLI (BVar "SP_main" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name F 13w))));
    (BMLI (BVar "SP_process" (BType_Imm Bit32)) (\ms:m0_state. Imm32 (ms.REG (R_name T 13w))));
    (BMLI (BVar "ModeHandler" BType_Bool) (\ms:m0_state. bool2b (ms.CurrentMode = Mode_Handler)))]`;


val m0_REGS_lifted_imms_LIST_REWRS = save_thm ("m0_REGS_lifted_imms_LIST_REWRS",
  SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] m0_REGS_lifted_imms_LIST_def);

val m0_lifted_mem_def = Define `
  m0_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit32 Bit8)) (\ms:m0_state. ms.MEM)`

val m0_lifted_pc_def = Define `
  m0_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit32))
                       (BVar (bir_temp_var_name "COND") BType_Bool)
                       (\ms:m0_state. Imm32 (ms.REG RName_PC))`

val m0_state_is_OK_def = Define `m0_state_is_OK (ef, sel) (s:m0_state) =
  ((s.AIRCR.ENDIANNESS <=> ef) /\ (s.CONTROL.SPSEL <=> sel) /\
  (s.exception = NoException))`

(* Just a dummy for now *)
val m0_bmr_def = Define `m0_bmr (ef, sel) = <|
  bmr_extra := \ms:m0_state. m0_state_is_OK (ef, sel) ms;
  bmr_imms := m0_REGS_lifted_imms_LIST;
  bmr_mem := m0_lifted_mem;
  bmr_pc := m0_lifted_pc;
  bmr_step_fun := NextStateM0 |>`;


val m0_bmr_EVAL = save_thm ("m0_bmr_EVAL",
  GENL [``ef:bool``, ``sel:bool``] (SIMP_CONV (list_ss++wordsLib.WORD_ss) [m0_bmr_def, R_name_def,
    m0_REGS_lifted_imms_LIST_def, m0_lifted_mem_def, m0_state_is_OK_def,
    m0_lifted_pc_def, bir_temp_var_name_def]
    ``m0_bmr (ef, sel)``)
);

val m0_bmr_vars_EVAL = save_thm ("m0_bmr_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, bmr_vars_def] ``bmr_vars (m0_bmr (ef, sel))``);

val m0_bmr_temp_vars_EVAL = save_thm ("m0_bmr_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
  bir_temp_var_def, bir_temp_var_name_def]
  ``bmr_temp_vars (m0_bmr (ef, sel))``);

val m0_bmr_varnames_distinct = prove (``
  bmr_varnames_distinct (m0_bmr (ef, sel))``,
SIMP_TAC std_ss [bmr_varnames_distinct_def,
  m0_bmr_vars_EVAL, m0_bmr_temp_vars_EVAL, MAP, MAP, bir_var_name_def,
  APPEND] >>
SIMP_TAC (list_ss++stringSimps.STRING_ss) [ALL_DISTINCT]);


val m0_bmr_OK = store_thm ("m0_bmr_OK",
  ``!ef sel. bmr_ok (m0_bmr (ef, sel))``,

SIMP_TAC std_ss [bmr_ok_def, m0_bmr_varnames_distinct] >>
SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  m0_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def]);


val m0_bmr_label_thm = store_thm ("m0_bmr_label_thm",
``!ef sel ms n hc. (BL_Address (bmr_pc_lf (m0_bmr (ef, sel)) ms) = BL_Address_HC (Imm32 (n2w n)) hc) ==>
                (ms.REG RName_PC = n2w n)``,
SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, m0_bmr_EVAL, BL_Address_HC_def]);


val m0_bmr_LIFTED = save_thm ("m0_bmr_LIFTED",
let
  val (vars, _) = strip_forall (concl m0_bmr_OK)
  val thm0 = MATCH_MP bmr_lifted (SPECL vars m0_bmr_OK)
  val c = SIMP_CONV (list_ss++bmr_ss) [m0_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
  val thm2 = SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] thm1

  val thm3 = SIMP_RULE (std_ss++boolSimps.CONJ_ss) [GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM, GSYM CONJ_ASSOC] (CONJ thm1 thm2)
in
  GENL vars thm3
end);

val bmr_extra_M0 = store_thm ("bmr_extra_M0",
``!ef sel ms. (m0_bmr (ef, sel)).bmr_extra ms = ((ms.AIRCR.ENDIANNESS ⇔ ef) ∧ (ms.CONTROL.SPSEL ⇔ sel) ∧
  (ms.exception = NoException))``,

SIMP_TAC (std_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss) [m0_bmr_EVAL]);


val bmr_ms_mem_contains_M0_4 = store_thm ("bmr_ms_mem_contains_M0_4",
``!ef sel ms v1 v2 v3 v4.
  (bmr_ms_mem_contains (m0_bmr (ef, sel)) ms ((ms.REG RName_PC), [v1; v2; v3; v4])) <=>
  ((ms.MEM (ms.REG RName_PC) = v1) /\ 
   (ms.MEM (ms.REG RName_PC + 1w) = v2) /\ 
   (ms.MEM (ms.REG RName_PC + 2w) = v3) /\
   (ms.MEM (ms.REG RName_PC + 3w) = v4))``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def, m0_bmr_EVAL, bmr_mem_lf_def]);


val bmr_ms_mem_contains_M0_2 = store_thm ("bmr_ms_mem_contains_M0_2",
``!ef sel ms v1 v2.
  (bmr_ms_mem_contains (m0_bmr (ef, sel)) ms ((ms.REG RName_PC), [v1; v2])) <=>
  ((ms.MEM (ms.REG RName_PC) = v1) /\ 
   (ms.MEM (ms.REG RName_PC + 1w) = v2))``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def, m0_bmr_EVAL, bmr_mem_lf_def]);

(**********)
(* RISC-V *)
(**********)
(* Hmmm.... Looking at riscv_state, it seems like everything except
 * clock, memory, done (whatever that is?), exception, log and
 * totalCore is dependent upon a process ID. procID is a 8-bit
 * field, meaning you could have up to 256 hardware processes.
 *
 * This is just a complete guess as to what the things mean though.
 *
 * These processes are typically known as hardware threads or
 * "harts". See https://wiki.osdev.org/RISC-V#Hardware_Threads
 * and Section 2.7 of the RISC-V User-Level ISA.
 *
 * c_gpr and c_fpr are the candidates for general-purpose registers,
 * but c_fpr is probably the registers in the extended RV64I base
 * integer instruction set. *)

(* With starting point in bir_lifting_machinesLib_instances.riscv_bmr_rec, 
 * we try to prove all the fields, starting from the top:

     bir_lifting_machinesScript.riscv_bmr_OK
     bir_lifting_machinesScript.riscv_bmr_LIFTED
     bir_lifting_machinesScript.riscv_bmr_EVAL
     bir_lifting_machinesScript.riscv_bmr_label_thm
*)

(**********************************************************************)
(* 1. riscv_bmr_OK                                                    *)
(**********************************************************************)

val riscv_state_is_OK_def = Define `
  riscv_state_is_OK (ms:riscv_state) <=> (
    (* Interpreted from https://github.com/SRI-CSL/l3riscv/blob/master/src/l3/riscv.spec
     * specifically from the older version https://github.com/SRI-CSL/l3riscv/blob/3d1cd4f8f922fb60a04f75ebcdbfd74919c4e585/src/l3/riscv.spec
*)
    (ms.exception = NoException) /\
(*   
     * MCSRs are machine mode control and status registers, mstatus is status register,
     * "VM" is "memory management and virtualization", 5 bits.
     * Page 23 of https://people.eecs.berkeley.edu/~krste/papers/riscv-privileged-v1.9.1.pdf
     * explains that memory management field being zero corresponds to "Mbare", no translation or
     * protection.
     * Don't know why this must always be 0 for a simple add, but it is checked only in
     * "translateAddr" in the Fetch step of Next. Perhaps it is some limitation of the model (version).
*)
    ((ms.c_MCSR ms.procID).mstatus.VM = 0w) /\
(* 
     * Fetch state from interpreter execution context must be NONE. Type is
     * TransferControl option:

         type SynchronousTrap = { badaddr: BitsN.nbit option, trap: ExceptionType }

           datatype TransferControl
             = BranchTo of BitsN.nbit | Ereturn | Mrts | Trap of SynchronousTrap

     * we see in riscv.sml that in the Next function, after Fetch-Decode-Run
     * "NextFetch" is accessed, which returns a tuple where the first element is a TransferControl
     * option. This has been written to NextFetch in the Run step. Effects on PC are resolved and
     * NextFetch is then set to NONE.
     * The reason for why this must be NONE in the initial state is likely that in regular situations
     * when non-control transfer instructions are executed, NextFetch is never written to (instead of
     * explicitly writing NONE).
*)
    (ms.c_NextFetch ms.procID = NONE) /\
(*

     * It seems the size of the general-purpose registers is hard-coded as 64-bit in the L3 model.
     * When trying to store values of 64-bit registers as 32-bit words, the lifter runs into
     * a lot of trouble. For this reason, we fix the architecture to 64-bit.

     * TODO: For technical reasons, we don't write this as

         ((ms.c_MCSR ms.procID).mcpuid.ArchBase = 2w)

     * which is a more direct representation of what is really stored, but rather as two separate
     * conjuncts to be able to lift without performing additional word arithmetic (effectively,
     * comparing 2w to 0w and 1w)
*)
     ((ms.c_MCSR ms.procID).mcpuid.ArchBase <> 0w) /\
     ((ms.c_MCSR ms.procID).mcpuid.ArchBase <> 1w)
  )
(* For ARM8:
    (* https://static.docs.arm.com/100878/0100/fundamentals_of_armv8_a_100878_0100_en.pdf
     * tells us that
     * ELn: Exception level n. EL0 is user, EL1 kernel, EL2 Hypervisor, EL3 firmware (p. 4 of PDF).
     * SCTLR: System control register; for EL1, EL2 and EL3 (p. 24 of PDF). 
     * PSTATE: Processor state flags, accessed through special-purpose registers. (p. 16 of PDF)
     * TCR: Translation Control Register; for EL1, EL2 and EL3. Determines
     *      Translation Table Base Register. *)

    (* Explicit data accesses at EL0 MUST be little-endian. *)
    ~ms.SCTLR_EL1.E0E /\
    (* Exception level must be 0 (user) *)
    (ms.PSTATE.EL = 0w) /\
    (* Exception must be NoException (as opposed to ALIGNMENT_FAULT,
     * UNDEFINED_FAULT and ASSERT).*)
    (ms.exception = NoException) /\
    (* Stack Alignment Check MUST NOT be enabled for EL0. *)
    ~ms.SCTLR_EL1.SA0 /\
    (* Translation control register for EL1 must not be TBI0 or TBI1,
     * meaning it must be "tcr_el1'rst", which is a 62-bit field.
     * TODO: What is TBI0 and TBI1? *)
    ~ms.TCR_EL1.TBI0 /\
    ~ms.TCR_EL1.TBI1
  )
*)
(* For Cortex-M0:
    (* AIRCR: Application Interrupt and Reset Control Register.
     * CONTROL: Special register in Cortex-M processor. Can be accessed using MSR and MRS. *)

    (* Endianness must match argument ef. *)
    (s.AIRCR.ENDIANNESS = ef) /\
    (* Stack pointer selection bit in the control register must match argument sel. *)
    (s.CONTROL.SPSEL = sel) /\
    (* Exception must be NoException. *)
    (s.exception = NoException)
*)
`;

(* Lifting RISC-V general-purpose registers. Note that while these are referred
 * to as "general-purpose", by convention they include hardwired zero, sp, gp, tp,
 * ra, and so on. *)
val riscv_GPRS_lifted_imms_LIST_def = Define `
  riscv_GPRS_lifted_imms_LIST =
    (MAP (\n. (BMLI (BVar (STRCAT "x" (n2s 10 HEX n)) (BType_Imm Bit64))
               (\ms:riscv_state. Imm64 (ms.c_gpr ms.procID (n2w n) ))))  (COUNT_LIST 32))
`;
val riscv_GPRS_lifted_imms_LIST_EVAL = save_thm("riscv_GPRS_lifted_imms_LIST_EVAL",
  EVAL ``riscv_GPRS_lifted_imms_LIST``
);

(* Lifting RISC-V HardFloat registers. *)
val riscv_FPRS_lifted_imms_LIST_def = Define `
  riscv_FPRS_lifted_imms_LIST =
    (MAP (\n. (BMLI (BVar (STRCAT "f" (n2s 10 HEX n)) (BType_Imm Bit64))
               (\ms:riscv_state. Imm64 (ms.c_fpr ms.procID (n2w n) ))))  (COUNT_LIST 32))
`;
val riscv_FPRS_lifted_imms_LIST_EVAL = save_thm("riscv_FPRS_lifted_imms_LIST_EVAL",
  EVAL ``riscv_FPRS_lifted_imms_LIST``
);

(* Note: For some reason, MEM is named MEM8 in the RISC-V state.
 * Since memory is shared between processes, this does not require
 * a process ID. *)
val riscv_lifted_mem_def = Define `
  riscv_lifted_mem = BMLM (BVar "MEM8" (BType_Mem Bit64 Bit8))
                          (\ms:riscv_state. ms.MEM8)
`;

(* Compared to the ARM8 version, this also has to take a procID from the
 * machine state. See riscv_state in riscvScript.sml in l3-machine-code. *)
val riscv_lifted_pc_def = Define `
  riscv_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit64))
                          (BVar (bir_temp_var_name "COND") BType_Bool)
                          (\ms:riscv_state. Imm64 (ms.c_PC ms.procID))
`;

(* HOL definition of RISC-V BIR machine record. *)
(* Prerequisites: riscv_lifted_pc, riscv_lifted_mem,
 * riscv_PSTATE_lifted_imms_LIST, riscv_REGS_lifted_imms_LIST,
 * riscv_EXTRA_lifted_imms_LIST *)
val riscv_bmr_def = Define `
  riscv_bmr = <|
    (* TODO: This needs to be expended upon, the definition of
     * OK state is now minimal. *)
    bmr_extra := \ms. riscv_state_is_OK ms;
    (* Registers are the 32 general-purpose registers as well as the
     * 32 fprs (fpr = floating point register?). *)
    bmr_imms := (riscv_GPRS_lifted_imms_LIST++riscv_FPRS_lifted_imms_LIST);
    (* Done! *)
    bmr_mem := riscv_lifted_mem;
    (* Done! *)
    bmr_pc := riscv_lifted_pc;
    (* Done! *)
    bmr_step_fun := NextRISCV
  |>
`;

(* Evaluation theorem of RISC-V BMR. *)
val riscv_bmr_EVAL = save_thm("riscv_bmr_EVAL",
SIMP_CONV list_ss [riscv_bmr_def, riscv_state_is_OK_def,
                   riscv_GPRS_lifted_imms_LIST_EVAL, riscv_FPRS_lifted_imms_LIST_EVAL,
                   riscv_lifted_mem_def,
                   riscv_lifted_pc_def, bir_temp_var_name_def]
          ``riscv_bmr``
);

(* Evaluation theorem of variables in a RISC-V BMR. *)
val riscv_bmr_vars_EVAL = save_thm("riscv_bmr_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [riscv_bmr_EVAL, bmr_vars_def] ``bmr_vars riscv_bmr``
);
(* Evaluation theorem of variables + temporary variables (???) in a RISC-V BMR. *)
val riscv_bmr_temp_vars_EVAL = save_thm ("riscv_bmr_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [riscv_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
                             bir_temp_var_def, bir_temp_var_name_def]
          ``bmr_temp_vars riscv_bmr``
);

(* The property of all varnames being distinct. *)
val riscv_bmr_varnames_distinct = prove(
``bmr_varnames_distinct riscv_bmr``,

SIMP_TAC std_ss [bmr_varnames_distinct_def,
                 riscv_bmr_vars_EVAL, riscv_bmr_temp_vars_EVAL,
                 MAP, bir_var_name_def,
                 APPEND] >>
SIMP_TAC (list_ss++stringSimps.STRING_ss) [ALL_DISTINCT]
);

(* Theorem stating that the BIR machine record stored in riscv_bmr is
 * OK (in the sense of bmr_ok). *)
val riscv_bmr_OK = store_thm ("riscv_bmr_OK",
  ``bmr_ok riscv_bmr``,

SIMP_TAC std_ss [bmr_ok_def, riscv_bmr_varnames_distinct] >>
SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss)
         [riscv_bmr_EVAL, bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
          bir_is_temp_var_name_def, BType_Bool_def,
          bir_machine_lifted_pc_OK_def,
          bmr_varnames_distinct_def]
);

val riscv_bmr_rel_EVAL = save_thm ("riscv_bmr_rel_EVAL",
SIMP_CONV (list_ss++bmr_ss++holBACore_ss) [
  bmr_rel_def, riscv_bmr_EVAL,
  bir_machine_lifted_mem_def, bir_machine_lifted_imm_def,
  bir_is_temp_var_name_def, BType_Bool_def, bir_temp_var_name_def,
  bir_machine_lifted_pc_def, bir_temp_var_def,
  GSYM CONJ_ASSOC]
``bmr_rel riscv_bmr bs ms``);

(**********************************************************************)
(* 2. riscv_bmr_LIFTED                                                *)
(**********************************************************************)

val riscv_bmr_LIFTED = save_thm ("riscv_bmr_LIFTED",
let
  val thm0 = MATCH_MP bmr_lifted riscv_bmr_OK
  val c =
    SIMP_CONV (list_ss++bmr_ss) [riscv_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
in
  thm1
end
);

(**********************************************************************)
(* 3. riscv_bmr_label_thm                                             *)
(**********************************************************************)

val riscv_bmr_label_thm = store_thm ("riscv_bmr_label_thm",
``!ms n hc.
    (BL_Address (bmr_pc_lf riscv_bmr ms) =
      BL_Address_HC (Imm64 (n2w n)) hc) ==>
    ((ms.c_PC ms.procID) = n2w n)
``,

SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, riscv_bmr_EVAL,
                                         BL_Address_HC_def]
);

(*******************************************************************)

(* This is documented further up, in the context of
 * riscv_state_is_OK_def *)
val bmr_extra_RISCV = store_thm ("bmr_extra_RISCV",
``!ms.
    riscv_bmr.bmr_extra ms = 
      ((ms.exception = NoException) /\
       ((ms.c_MCSR ms.procID).mstatus.VM = 0w) /\
       (ms.c_NextFetch ms.procID = NONE) /\
       ((ms.c_MCSR ms.procID).mcpuid.ArchBase <> 0w) /\
       ((ms.c_MCSR ms.procID).mcpuid.ArchBase <> 1w)
      )
``,

SIMP_TAC (std_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss)
         [riscv_bmr_EVAL]
);

val bmr_ms_mem_contains_RISCV =
  store_thm ("bmr_ms_mem_contains_RISCV",
``!ms v1 v2 v3 v4.
    (bmr_ms_mem_contains riscv_bmr ms (ms.c_PC ms.procID,
                                      [v1; v2; v3; v4]) <=>
      ((ms.MEM8 (ms.c_PC ms.procID) = v1) /\
       (ms.MEM8 ((ms.c_PC ms.procID) + 1w) = v2) /\
       (ms.MEM8 ((ms.c_PC ms.procID) + 2w) = v3) /\
       (ms.MEM8 ((ms.c_PC ms.procID) + 3w) = v4)
      )
    )
``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def,
                                             riscv_bmr_EVAL,
                                             bmr_mem_lf_def]
);





(**********)
(* ARM M0 MOD VERSION WITH COUNTW AND BASE M0 *)
(**********)
(* Lifting REGs *)

val m0_mod_REGS_lifted_imms_LIST_def = Define `
  m0_mod_REGS_lifted_imms_LIST = [
    (BMLI (BVar "PSR_C" BType_Bool) (\ms:m0_mod_state. bool2b (ms.base.PSR.C)));
    (BMLI (BVar "PSR_N" BType_Bool) (\ms:m0_mod_state. bool2b (ms.base.PSR.N)));
    (BMLI (BVar "PSR_V" BType_Bool) (\ms:m0_mod_state. bool2b (ms.base.PSR.V)));
    (BMLI (BVar "PSR_Z" BType_Bool) (\ms:m0_mod_state. bool2b (ms.base.PSR.Z)));
    (BMLI (BVar "R0" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 0w))));
    (BMLI (BVar "R1" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 1w))));
    (BMLI (BVar "R2" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 2w))));
    (BMLI (BVar "R3" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 3w))));
    (BMLI (BVar "R4" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 4w))));
    (BMLI (BVar "R5" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 5w))));
    (BMLI (BVar "R6" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 6w))));
    (BMLI (BVar "R7" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 7w))));
    (BMLI (BVar "R8" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 8w))));
    (BMLI (BVar "R9" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 9w))));
    (BMLI (BVar "R10" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 10w))));
    (BMLI (BVar "R11" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 11w))));
    (BMLI (BVar "R12" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 12w))));
    (BMLI (BVar "LR" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 14w))));
    (BMLI (BVar "SP_main" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name F 13w))));
    (BMLI (BVar "SP_process" (BType_Imm Bit32)) (\ms:m0_mod_state. Imm32 (ms.base.REG (R_name T 13w))));
    (BMLI (BVar "ModeHandler" BType_Bool) (\ms:m0_mod_state. bool2b (ms.base.CurrentMode = Mode_Handler)));
    (BMLI (BVar "countw" (BType_Imm Bit64)) (\ms:m0_mod_state. Imm64 (ms.countw)))]`;


val m0_mod_REGS_lifted_imms_LIST_REWRS = save_thm ("m0_mod_REGS_lifted_imms_LIST_REWRS",
  SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] m0_mod_REGS_lifted_imms_LIST_def);

val m0_mod_lifted_mem_def = Define `
  m0_mod_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit32 Bit8)) (\ms:m0_mod_state. ms.base.MEM)`

val m0_mod_lifted_pc_def = Define `
  m0_mod_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit32))
                       (BVar (bir_temp_var_name "COND") BType_Bool)
                       (\ms:m0_mod_state. Imm32 (ms.base.REG RName_PC))`

val m0_mod_state_is_OK_def = Define `m0_mod_state_is_OK (ef, sel) (s:m0_mod_state) =
  ((s.base.AIRCR.ENDIANNESS <=> ef) /\ (s.base.CONTROL.SPSEL <=> sel) /\
  (s.base.exception = NoException))`

(* Just a dummy for now *)
val m0_mod_bmr_def = Define `m0_mod_bmr (ef, sel) = <|
  bmr_extra := \ms:m0_mod_state. m0_mod_state_is_OK (ef, sel) ms;
  bmr_imms := m0_mod_REGS_lifted_imms_LIST;
  bmr_mem := m0_mod_lifted_mem;
  bmr_pc := m0_mod_lifted_pc;
  bmr_step_fun := NextStateM0_mod |>`;


val m0_mod_bmr_EVAL = save_thm ("m0_mod_bmr_EVAL",
  GENL [``ef:bool``, ``sel:bool``] (SIMP_CONV (list_ss++wordsLib.WORD_ss) [m0_mod_bmr_def, R_name_def,
    m0_mod_REGS_lifted_imms_LIST_def, m0_mod_lifted_mem_def, m0_mod_state_is_OK_def,
    m0_mod_lifted_pc_def, bir_temp_var_name_def]
    ``m0_mod_bmr (ef, sel)``)
);

val m0_mod_bmr_vars_EVAL = save_thm ("m0_mod_bmr_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_mod_bmr_EVAL, bmr_vars_def] ``bmr_vars (m0_mod_bmr (ef, sel))``);

val m0_mod_bmr_temp_vars_EVAL = save_thm ("m0_mod_bmr_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [m0_mod_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
  bir_temp_var_def, bir_temp_var_name_def]
  ``bmr_temp_vars (m0_mod_bmr (ef, sel))``);

val m0_mod_bmr_varnames_distinct = prove (``
  bmr_varnames_distinct (m0_mod_bmr (ef, sel))``,
SIMP_TAC std_ss [bmr_varnames_distinct_def,
  m0_mod_bmr_vars_EVAL, m0_mod_bmr_temp_vars_EVAL, MAP, MAP, bir_var_name_def,
  APPEND] >>
SIMP_TAC (list_ss++stringSimps.STRING_ss) [ALL_DISTINCT]);


val m0_mod_bmr_OK = store_thm ("m0_mod_bmr_OK",
  ``!ef sel. bmr_ok (m0_mod_bmr (ef, sel))``,

SIMP_TAC std_ss [bmr_ok_def, m0_mod_bmr_varnames_distinct] >>
SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  m0_mod_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def]);


val m0_mod_bmr_label_thm = store_thm ("m0_mod_bmr_label_thm",
``!ef sel ms n hc. (BL_Address (bmr_pc_lf (m0_mod_bmr (ef, sel)) ms) = BL_Address_HC (Imm32 (n2w n)) hc) ==>
                (ms.base.REG RName_PC = n2w n)``,
SIMP_TAC (std_ss++bir_TYPES_ss++bmr_ss) [bmr_pc_lf_def, m0_mod_bmr_EVAL, BL_Address_HC_def]);


val m0_mod_bmr_LIFTED = save_thm ("m0_mod_bmr_LIFTED",
let
  val (vars, _) = strip_forall (concl m0_mod_bmr_OK)
  val thm0 = MATCH_MP bmr_lifted (SPECL vars m0_mod_bmr_OK)
  val c = SIMP_CONV (list_ss++bmr_ss) [m0_mod_bmr_EVAL, GSYM CONJ_ASSOC]
  val thm1 = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV c)) thm0
  val thm2 = SIMP_RULE (std_ss++wordsLib.WORD_ss) [R_name_def] thm1

  val thm3 = SIMP_RULE (std_ss++boolSimps.CONJ_ss) [GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM, GSYM CONJ_ASSOC] (CONJ thm1 thm2)
in
  GENL vars thm3
end);

val bmr_extra_M0_mod = store_thm ("bmr_extra_M0_mod",
``!ef sel ms. (m0_mod_bmr (ef, sel)).bmr_extra ms = ((ms.base.AIRCR.ENDIANNESS ⇔ ef) ∧ (ms.base.CONTROL.SPSEL ⇔ sel) ∧
  (ms.base.exception = NoException))``,

SIMP_TAC (std_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss) [m0_mod_bmr_EVAL]);


val bmr_ms_mem_contains_M0_mod_4 = store_thm ("bmr_ms_mem_contains_M0_mod_4",
``!ef sel ms v1 v2 v3 v4.
  (bmr_ms_mem_contains (m0_mod_bmr (ef, sel)) ms ((ms.base.REG RName_PC), [v1; v2; v3; v4])) <=>
  ((ms.base.MEM (ms.base.REG RName_PC) = v1) /\ 
   (ms.base.MEM (ms.base.REG RName_PC + 1w) = v2) /\ 
   (ms.base.MEM (ms.base.REG RName_PC + 2w) = v3) /\
   (ms.base.MEM (ms.base.REG RName_PC + 3w) = v4))``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def, m0_mod_bmr_EVAL, bmr_mem_lf_def]);


val bmr_ms_mem_contains_M0_mod_2 = store_thm ("bmr_ms_mem_contains_M0_mod_2",
``!ef sel ms v1 v2.
  (bmr_ms_mem_contains (m0_mod_bmr (ef, sel)) ms ((ms.base.REG RName_PC), [v1; v2])) <=>
  ((ms.base.MEM (ms.base.REG RName_PC) = v1) /\ 
   (ms.base.MEM (ms.base.REG RName_PC + 1w) = v2))``,

SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ss) [bmr_ms_mem_contains_def, m0_mod_bmr_EVAL, bmr_mem_lf_def]);






val _ = export_theory();
