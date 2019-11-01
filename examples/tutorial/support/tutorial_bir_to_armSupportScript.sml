open HolKernel Parse boolLib bossLib;

open bir_programTheory;
open bir_wm_instTheory;
open bin_hoare_logicTheory;
open bin_hoare_logicSimps;
open bir_program_multistep_propsTheory;
open bir_auxiliaryTheory;

open bir_expSimps;
open HolBACoreSimps;
open bin_hoare_logicSimps;

open bir_auxiliaryLib;

val _ = new_theory "tutorial_bir_to_armSupport";

(* This part should be generalized *)
(*
val arm8_triple_def = Define `
  arm8_triple mms l ls pre post =
  !ms.
   (arm8_bmr.bmr_extra ms) ==>
   (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) ==>
   (ms.PC = l) ==>
   (pre ms) ==>
   ?c_addr_labels:num ms'.
    (FUNPOW_OPT arm8_bmr.bmr_step_fun c_addr_labels ms = SOME ms') /\     
    (ms'.PC IN ls) /\
    (post ms')
`;
*)
val arm_weak_trs_def = Define `
  arm_weak_trs ms ls ms' = 
        ?n.
          ((n > 0) /\
           (FUNPOW_OPT arm8_bmr.bmr_step_fun n ms = SOME ms') /\
           (ms'.PC IN ls)
          ) /\
          !n'.
            (((n' < n) /\ (n' > 0)) ==>
            ?ms''.
              (FUNPOW_OPT arm8_bmr.bmr_step_fun n' ms = SOME ms'') /\
              (~(ms''.PC IN ls))
            )`;


val arm_weak_model_def =
  Define `arm_weak_model  = <|
    trs  := arm8_bmr.bmr_step_fun;
    weak := arm_weak_trs;
    pc   := (\st. st.PC)
  |>`;


(* The main triple to be used for ARM composition *)
val arm8_triple_def = Define `
  arm8_triple mms l ls pre post =
    weak_triple arm_weak_model l ls
      (\ms. (arm8_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) /\
            (pre ms))         
      (\ms. (arm8_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) /\
            (post ms))         
`;


val same_var_is_bool_exp_env_eq_thm = prove(
  ``!pre pre' s.
    (bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre)) ==>
    (bir_vars_of_exp pre' = bir_vars_of_exp pre) ==>
    ((bir_is_bool_exp_env s.bst_environ pre') =
       (bir_is_bool_exp_env s.bst_environ pre))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_is_bool_exp_env_def,
                      bir_exp_tautologiesTheory.bir_exp_is_taut_def,
                      bir_bool_expTheory.bir_is_bool_exp_REWRS]
);


val bir_triple_weak_rule_thm = store_thm("bir_triple_weak_rule_thm",
  ``!pre pre' p l ls post.
    ((bir_vars_of_exp pre') SUBSET (bir_vars_of_program p)) ==>
    ((bir_vars_of_exp pre) SUBSET (bir_vars_of_program p)) ==>
    bir_triple p l ls pre post ==>
    bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre) ==>
    bir_triple p l ls pre' post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_triple_def, weak_triple_def, bir_exec_to_labels_triple_precond_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `(bir_vars_of_exp pre' = bir_vars_of_exp pre) ==>
         !s.
             bir_is_bool_exp_env s.bst_environ pre' <=>
             bir_is_bool_exp_env s.bst_environ pre` >- (
  IMP_RES_TAC same_var_is_bool_exp_env_eq_thm
) >>
REV_FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC std_ss [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
PAT_X_ASSUM ``!s. _`` (fn thm => ASSUME_TAC (Q.SPEC `s.bst_environ` thm)) >>
subgoal `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_exp
              (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre))` >- (
  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  IMP_RES_TAC bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >> 
ASSUME_TAC (Q.SPECL [`s.bst_environ`, `pre'`, `pre`]  bir_exp_equivTheory.bir_impl_equiv) >>
REV_FULL_SIMP_TAC std_ss [] >>
subgoal `bir_is_bool_exp_env s.bst_environ pre` >- (
  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_is_bool_exp_REWRS,
                        bir_typing_expTheory.bir_vars_of_exp_def,
                        bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
                        bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
FULL_SIMP_TAC std_ss [] >>
Q.EXISTS_TAC `s'` >>
FULL_SIMP_TAC std_ss []
);


val bir_pre_arm8_to_bir_def = Define `
  bir_pre_arm8_to_bir pre pre_bir =
    bir_is_bool_exp pre_bir /\
    !ms bs.
    bmr_rel arm8_bmr bs ms ==>
    bir_env_vars_are_initialised bs.bst_environ (bir_vars_of_exp pre_bir) ==>
    pre ms ==>
    (bir_eval_exp pre_bir bs.bst_environ = SOME bir_val_true)
`;

val bir_post_bir_to_arm8_def = Define `
  bir_post_bir_to_arm8 post post_bir ls =
    !ms bs l.
    l IN ls ==>
    bmr_rel arm8_bmr bs ms ==>
    (bir_eval_exp (post_bir l) bs.bst_environ = SOME bir_val_true) ==>
    post ms
`;


val arm8_load_64_def = Define `arm8_load_64 m a =
  (((m (a + 7w)) @@
  (((m (a + 6w)) @@
  (((m (a + 5w)) @@
  (((m (a + 4w)) @@
  (((m (a + 3w)) @@
   (((m (a + 2w)) @@
     ((m (a + 1w)) @@ (m (a + 0w))):bool[16]):bool[24])):bool[32])
    ):bool[40])):bool[48])):bool[56])):bool[64])
`;


val bload_64_to_arm8_load_64_thm = store_thm("bload_64_to_arm8_load_64_thm",
  ``!bs ms. (bmr_rel arm8_bmr bs ms) ==>
    (!a.
    ((bir_eval_load
      (bir_env_read (BVar "MEM" (BType_Mem Bit64 Bit8)) bs.bst_environ)
      (SOME (BVal_Imm (Imm64 a))) BEnd_LittleEndian Bit64) =
        SOME (BVal_Imm (Imm64 (arm8_load_64 ms.MEM a))))
    )``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN
  `?mem_n.
   (bir_env_read (BVar "MEM" (BType_Mem Bit64 Bit8)) bs.bst_environ =
     (SOME (BVal_Mem Bit64 Bit8 mem_n))) /\
   (ms.MEM = (\a. n2w (bir_load_mmap mem_n (w2n a)))) /\
   bir_env_var_is_declared bs.bst_environ
     (BVar "tmp_MEM" (BType_Mem Bit64 Bit8))` ASSUME_TAC >-(
  FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.arm8_bmr_rel_EVAL] >>
  EXISTS_TAC ``mem_n:num|->num`` >>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [bir_expTheory.bir_eval_load_FULL_REWRS, arm8_load_64_def] >>
FULL_SIMP_TAC (srw_ss()) []
);


val bool2w_and =
  prove(``!a b. ((bool2w a) && (bool2w b)) = (bool2w (a /\ b))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bool2w_def] >>
Cases_on `a` >>
Cases_on `b` >>
EVAL_TAC
);


val imm_eq_to_val_eq =
  prove(``!a b . ((BVal_Imm(Imm1 a)) = (BVal_Imm(Imm1 b))) = (a = b)``,

REPEAT STRIP_TAC >> EVAL_TAC);


val arm8_wf_varset_def = Define `
arm8_wf_varset vset =
  (vset = {
  (BVar "ProcState_C" (BType_Imm Bit1));
  (BVar "tmp_ProcState_C" (BType_Imm Bit1));
  (BVar "ProcState_N" (BType_Imm Bit1));
  (BVar "tmp_ProcState_N" (BType_Imm Bit1));
  (BVar "ProcState_V" (BType_Imm Bit1));
  (BVar "tmp_ProcState_V" (BType_Imm Bit1));
  (BVar "ProcState_Z" (BType_Imm Bit1));
  (BVar "tmp_ProcState_Z" (BType_Imm Bit1));
  (BVar "R0" (BType_Imm Bit64));
  (BVar "tmp_R0" (BType_Imm Bit64));
  (BVar "R1" (BType_Imm Bit64));
  (BVar "tmp_R1" (BType_Imm Bit64));
  (BVar "R2" (BType_Imm Bit64));
  (BVar "tmp_R2" (BType_Imm Bit64));
  (BVar "R3" (BType_Imm Bit64));
  (BVar "tmp_R3" (BType_Imm Bit64));
  (BVar "R4" (BType_Imm Bit64));
  (BVar "tmp_R4" (BType_Imm Bit64));
  (BVar "R5" (BType_Imm Bit64));
  (BVar "tmp_R5" (BType_Imm Bit64));
  (BVar "R6" (BType_Imm Bit64));
  (BVar "tmp_R6" (BType_Imm Bit64));
  (BVar "R7" (BType_Imm Bit64));
  (BVar "tmp_R7" (BType_Imm Bit64));
  (BVar "R8" (BType_Imm Bit64));
  (BVar "tmp_R8" (BType_Imm Bit64));
  (BVar "R9" (BType_Imm Bit64));
  (BVar "tmp_R9" (BType_Imm Bit64));
  (BVar "R10" (BType_Imm Bit64));
  (BVar "tmp_R10" (BType_Imm Bit64));
  (BVar "R11" (BType_Imm Bit64));
  (BVar "tmp_R11" (BType_Imm Bit64));
  (BVar "R12" (BType_Imm Bit64));
  (BVar "tmp_R12" (BType_Imm Bit64));
  (BVar "R13" (BType_Imm Bit64));
  (BVar "tmp_R13" (BType_Imm Bit64));
  (BVar "R14" (BType_Imm Bit64));
  (BVar "tmp_R14" (BType_Imm Bit64));
  (BVar "R15" (BType_Imm Bit64));
  (BVar "tmp_R15" (BType_Imm Bit64));
  (BVar "R16" (BType_Imm Bit64));
  (BVar "tmp_R16" (BType_Imm Bit64));
  (BVar "R17" (BType_Imm Bit64));
  (BVar "tmp_R17" (BType_Imm Bit64));
  (BVar "R18" (BType_Imm Bit64));
  (BVar "tmp_R18" (BType_Imm Bit64));
  (BVar "R19" (BType_Imm Bit64));
  (BVar "tmp_R19" (BType_Imm Bit64));
  (BVar "R20" (BType_Imm Bit64));
  (BVar "tmp_R20" (BType_Imm Bit64));
  (BVar "R21" (BType_Imm Bit64));
  (BVar "tmp_R21" (BType_Imm Bit64));
  (BVar "R22" (BType_Imm Bit64));
  (BVar "tmp_R22" (BType_Imm Bit64));
  (BVar "R23" (BType_Imm Bit64));
  (BVar "tmp_R23" (BType_Imm Bit64));
  (BVar "R24" (BType_Imm Bit64));
  (BVar "tmp_R24" (BType_Imm Bit64));
  (BVar "R25" (BType_Imm Bit64));
  (BVar "tmp_R25" (BType_Imm Bit64));
  (BVar "R26" (BType_Imm Bit64));
  (BVar "tmp_R26" (BType_Imm Bit64));
  (BVar "R27" (BType_Imm Bit64));
  (BVar "tmp_R27" (BType_Imm Bit64));
  (BVar "R28" (BType_Imm Bit64));
  (BVar "tmp_R28" (BType_Imm Bit64));
  (BVar "R29" (BType_Imm Bit64));
  (BVar "tmp_R29" (BType_Imm Bit64));
  (BVar "R30" (BType_Imm Bit64));
  (BVar "tmp_R30" (BType_Imm Bit64));
  (BVar "R31" (BType_Imm Bit64));
  (BVar "tmp_R31" (BType_Imm Bit64));
  (BVar "SP_EL0" (BType_Imm Bit64));
  (BVar "tmp_SP_EL0" (BType_Imm Bit64));
  (BVar "SP_EL1" (BType_Imm Bit64));
  (BVar "tmp_SP_EL1" (BType_Imm Bit64));
  (BVar "SP_EL2" (BType_Imm Bit64));
  (BVar "tmp_SP_EL2" (BType_Imm Bit64));
  (BVar "SP_EL3" (BType_Imm Bit64));
  (BVar "tmp_SP_EL3" (BType_Imm Bit64));
  (BVar "MEM" (BType_Mem Bit64 Bit8));
  (BVar "tmp_MEM" (BType_Mem Bit64 Bit8));
  (BVar "tmp_PC" (BType_Imm Bit64));
  (BVar "tmp_COND" (BType_Imm Bit1))
})`;

val default_arm8_bir_state_def = Define `default_arm8_bir_state ms =
 <|bst_pc :=  bir_block_pc (BL_Address (Imm64 ms.PC)); 
 bst_environ := BEnv (
 ("ProcState_C" =+ SOME(BVal_Imm (bool2b ms.PSTATE.C)))
 (("tmp_ProcState_C" =+ SOME(BVal_Imm (bool2b ms.PSTATE.C)))
 (("ProcState_N" =+ SOME(BVal_Imm (bool2b ms.PSTATE.N)))
 (("tmp_ProcState_N" =+ SOME(BVal_Imm (bool2b ms.PSTATE.N)))
 (("ProcState_V" =+ SOME(BVal_Imm (bool2b ms.PSTATE.V)))
 (("tmp_ProcState_V" =+ SOME(BVal_Imm (bool2b ms.PSTATE.V)))
 (("ProcState_Z" =+ SOME(BVal_Imm (bool2b ms.PSTATE.Z)))
 (("tmp_ProcState_Z" =+ SOME(BVal_Imm (bool2b ms.PSTATE.Z)))
 (("R0" =+ SOME(BVal_Imm (Imm64 (ms.REG 0w))))
 (("tmp_R0" =+ SOME(BVal_Imm (Imm64 (ms.REG 0w))))
 (("R1" =+ SOME(BVal_Imm (Imm64 (ms.REG 1w))))
 (("tmp_R1" =+ SOME(BVal_Imm (Imm64 (ms.REG 1w))))
 (("R2" =+ SOME(BVal_Imm (Imm64 (ms.REG 2w))))
 (("tmp_R2" =+ SOME(BVal_Imm (Imm64 (ms.REG 2w))))
 (("R3" =+ SOME(BVal_Imm (Imm64 (ms.REG 3w))))
 (("tmp_R3" =+ SOME(BVal_Imm (Imm64 (ms.REG 3w))))
 (("R4" =+ SOME(BVal_Imm (Imm64 (ms.REG 4w))))
 (("tmp_R4" =+ SOME(BVal_Imm (Imm64 (ms.REG 4w))))
 (("R5" =+ SOME(BVal_Imm (Imm64 (ms.REG 5w))))
 (("tmp_R5" =+ SOME(BVal_Imm (Imm64 (ms.REG 5w))))
 (("R6" =+ SOME(BVal_Imm (Imm64 (ms.REG 6w))))
 (("tmp_R6" =+ SOME(BVal_Imm (Imm64 (ms.REG 6w))))
 (("R7" =+ SOME(BVal_Imm (Imm64 (ms.REG 7w))))
 (("tmp_R7" =+ SOME(BVal_Imm (Imm64 (ms.REG 7w))))
 (("R8" =+ SOME(BVal_Imm (Imm64 (ms.REG 8w))))
 (("tmp_R8" =+ SOME(BVal_Imm (Imm64 (ms.REG 8w))))
 (("R9" =+ SOME(BVal_Imm (Imm64 (ms.REG 9w))))
 (("tmp_R9" =+ SOME(BVal_Imm (Imm64 (ms.REG 9w))))
 (("R10" =+ SOME(BVal_Imm (Imm64 (ms.REG 10w))))
 (("tmp_R10" =+ SOME(BVal_Imm (Imm64 (ms.REG 10w))))
 (("R11" =+ SOME(BVal_Imm (Imm64 (ms.REG 11w))))
 (("tmp_R11" =+ SOME(BVal_Imm (Imm64 (ms.REG 11w))))
 (("R12" =+ SOME(BVal_Imm (Imm64 (ms.REG 12w))))
 (("tmp_R12" =+ SOME(BVal_Imm (Imm64 (ms.REG 12w))))
 (("R13" =+ SOME(BVal_Imm (Imm64 (ms.REG 13w))))
 (("tmp_R13" =+ SOME(BVal_Imm (Imm64 (ms.REG 13w))))
 (("R14" =+ SOME(BVal_Imm (Imm64 (ms.REG 14w))))
 (("tmp_R14" =+ SOME(BVal_Imm (Imm64 (ms.REG 14w))))
 (("R15" =+ SOME(BVal_Imm (Imm64 (ms.REG 15w))))
 (("tmp_R15" =+ SOME(BVal_Imm (Imm64 (ms.REG 15w))))
 (("R16" =+ SOME(BVal_Imm (Imm64 (ms.REG 16w))))
 (("tmp_R16" =+ SOME(BVal_Imm (Imm64 (ms.REG 16w))))
 (("R17" =+ SOME(BVal_Imm (Imm64 (ms.REG 17w))))
 (("tmp_R17" =+ SOME(BVal_Imm (Imm64 (ms.REG 17w))))
 (("R18" =+ SOME(BVal_Imm (Imm64 (ms.REG 18w))))
 (("tmp_R18" =+ SOME(BVal_Imm (Imm64 (ms.REG 18w))))
 (("R19" =+ SOME(BVal_Imm (Imm64 (ms.REG 19w))))
 (("tmp_R19" =+ SOME(BVal_Imm (Imm64 (ms.REG 19w))))
 (("R20" =+ SOME(BVal_Imm (Imm64 (ms.REG 20w))))
 (("tmp_R20" =+ SOME(BVal_Imm (Imm64 (ms.REG 20w))))
 (("R21" =+ SOME(BVal_Imm (Imm64 (ms.REG 21w))))
 (("tmp_R21" =+ SOME(BVal_Imm (Imm64 (ms.REG 21w))))
 (("R22" =+ SOME(BVal_Imm (Imm64 (ms.REG 22w))))
 (("tmp_R22" =+ SOME(BVal_Imm (Imm64 (ms.REG 22w))))
 (("R23" =+ SOME(BVal_Imm (Imm64 (ms.REG 23w))))
 (("tmp_R23" =+ SOME(BVal_Imm (Imm64 (ms.REG 23w))))
 (("R24" =+ SOME(BVal_Imm (Imm64 (ms.REG 24w))))
 (("tmp_R24" =+ SOME(BVal_Imm (Imm64 (ms.REG 24w))))
 (("R25" =+ SOME(BVal_Imm (Imm64 (ms.REG 25w))))
 (("tmp_R25" =+ SOME(BVal_Imm (Imm64 (ms.REG 25w))))
 (("R26" =+ SOME(BVal_Imm (Imm64 (ms.REG 26w))))
 (("tmp_R26" =+ SOME(BVal_Imm (Imm64 (ms.REG 26w))))
 (("R27" =+ SOME(BVal_Imm (Imm64 (ms.REG 27w))))
 (("tmp_R27" =+  SOME(BVal_Imm (Imm64 (ms.REG 27w))))
 (("R28" =+ SOME(BVal_Imm (Imm64 (ms.REG 28w))))
 (("tmp_R28" =+ SOME(BVal_Imm (Imm64 (ms.REG 28w))))
 (("R29" =+ SOME(BVal_Imm (Imm64 (ms.REG 29w))))
 (("tmp_R29" =+ SOME(BVal_Imm (Imm64 (ms.REG 29w))))
 (("R30" =+ SOME(BVal_Imm (Imm64 (ms.REG 30w))))
 (("tmp_R30" =+ SOME(BVal_Imm (Imm64 (ms.REG 30w))))
 (("R31" =+ SOME(BVal_Imm (Imm64 (ms.REG 31w))))
 (("tmp_R31" =+ SOME(BVal_Imm (Imm64 (ms.REG 31w))))
 (("SP_EL0" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL0))))
 (("tmp_SP_EL0" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL0))))
 (("SP_EL1" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL1))))
 (("tmp_SP_EL1" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL1))))
 (("SP_EL2" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL2))))
 (("tmp_SP_EL2" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL2))))
 (("SP_EL3" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL3))))
 (("tmp_SP_EL3" =+ SOME(BVal_Imm (Imm64 (ms.SP_EL3))))
 (("tmp_PC" =+ SOME(BVal_Imm (Imm64 (ms.PC))))
 (("MEM" =+ SOME(BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM))))
 (("tmp_MEM" =+ SOME(BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM))))
 (* 83 parantheses!!! *)
 (("tmp_COND" =+ SOME(BVal_Imm (Imm1 0w))) bir_env_map_empty)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 );
  bst_status := BST_Running|>
`;


val default_arm8_bir_state_satisfies_rel_thm = prove(
  ``!ms.
    arm8_bmr.bmr_extra ms ==>
    bmr_rel arm8_bmr (default_arm8_bir_state ms) ms``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [default_arm8_bir_state_def,
  bir_lifting_machinesTheory.arm8_bmr_rel_EVAL,
  bir_env_oldTheory.bir_env_var_is_declared_def,
  bir_envTheory.bir_var_name_def] >>
FULL_SIMP_TAC (srw_ss()) [
              bir_envTheory.bir_env_read_UPDATE,
              bir_envTheory.bir_var_name_def,
              bir_envTheory.bir_env_lookup_UPDATE,
              bir_envTheory.bir_var_type_def,
              bir_envTheory.bir_env_lookup_type_def] >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_def,
                      type_of_bir_imm_def,
                      bir_immTheory.type_of_bool2b] >>
FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_extra_ARM8] >>
FULL_SIMP_TAC (srw_ss()) [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm] >>
METIS_TAC []
);


val exist_bir_of_arm8_thm = prove(
  ``!ms vars.
    arm8_wf_varset vars ==>
    arm8_bmr.bmr_extra ms ==>
    ?bs.
      (bmr_rel arm8_bmr bs ms /\ (bs.bst_status = BST_Running) /\
       bir_env_vars_are_initialised bs.bst_environ vars)``,

REPEAT STRIP_TAC >> 
EXISTS_TAC ``default_arm8_bir_state ms`` >>
ASSUME_TAC (SPEC ``ms:arm8_state`` default_arm8_bir_state_satisfies_rel_thm) >>
FULL_SIMP_TAC std_ss [] >>
STRIP_TAC >-  EVAL_TAC >>
PAT_X_ASSUM ``arm8_wf_varset vars``
  (fn thm=> REWRITE_TAC [SIMP_RULE std_ss [arm8_wf_varset_def] thm]) >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_var_is_initialised_def] >>
FULL_SIMP_TAC std_ss [bir_envTheory.bir_var_name_def, default_arm8_bir_state_def,
                        bir_envTheory.bir_env_lookup_UPDATE] >>
EVAL_TAC  >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_t_11,
                      bir_immTheory.type_of_bir_imm_def,
                      bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
);


val set_of_address_in_all_address_labels_thm = prove (
  ``!l adds.
    l IN {BL_Address (Imm64 ml') | ml' IN adds} ==>
    l IN {l | IS_BL_Address l}``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def]
);


val bir_block_pc_alt_thm = prove(
  ``!pc l.
    (pc.bpc_label = l) ==>
    (pc.bpc_index = 0) ==>
    (pc = bir_block_pc l)``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss)
  [bir_programTheory.bir_block_pc_def,
   bir_programTheory.bir_programcounter_t_component_equality]
);

val FUNPOW_OPT_prev_EXISTS = store_thm("FUNPOW_OPT_prev_EXISTS",
 ``!step_fun n n' s s'.
   n > 0 ==>
   (FUNPOW_OPT step_fun n s = SOME s') ==>
   n' < n ==>
   ?s''.
   (FUNPOW_OPT step_fun n' s = SOME s'')``,

cheat
);

val test_thm = store_thm("test_thm",
  ``!mls p bs bs' l n n0 n' lo c_st c_addr_labels.
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
         BER_Ended l n n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    (bs.bst_status = BST_Running) ==>
    (bs'.bst_status = BST_Running) ==>
    ((n' > 0) /\ (n' = c_addr_labels))
``,

cheat
);


val test_thm2 = store_thm("test_thm2",
  ``!pc_cond p st n1 n2 ol c_st c_pc st'.
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Ended ol c_st c_pc st') ==>
    (n2 < n1) ==>
    (?ol' c_st' c_pc' st''.
      bir_exec_steps_GEN pc_cond p st (SOME n2) = BER_Ended ol' c_st' c_pc' st'')``,

cheat
);


val test_thm3 = store_thm("test_thm3",
  ``!pc_cond p st n1 n2 ol ol' c_st c_st' c_pc c_pc' st' st''.
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Ended ol c_st c_pc st') ==>
    (n2 < n1) ==>
    (bir_exec_steps_GEN pc_cond p st (SOME n2) = BER_Ended ol' c_st' c_pc' st'') ==>
    (st''.bst_status = BST_Running) /\ (c_st' < c_st)``,

cheat
);


val test_thm4 = store_thm("test_thm4",
  ``!pc_cond p st n ol c_st c_pc st'.
    (bir_exec_steps_GEN pc_cond p st (SOME n) = BER_Ended ol c_st c_pc st') ==>
    (st'.bst_status = BST_Running) ==>
    (n = c_pc)``,

cheat
);

val test_thm5 = store_thm("test_thm5",
  ``!pc_cond pc_cond' p st n1 n2 ol ol' c_st c_st' c_pc c_pc' st'.
    (bir_exec_steps_GEN pc_cond p st (SOME n1) = BER_Ended ol c_st c_pc st') ==>
    (bir_exec_steps_GEN pc_cond' p st (SOME n2) = BER_Ended ol' c_st' c_pc' st') ==>
    (c_st' = c_st)``,

cheat
);


val test_thm6 = store_thm("test_thm6",
  ``!pc_cond p st n ol c_st c_pc st'.
    (bir_exec_steps_GEN pc_cond p st (SOME n) = BER_Ended ol c_st c_pc st') ==>
    (st'.bst_status = BST_Running) ==>
    (n > 0) ==>
    (c_st > 0)``,

cheat
);

val test_thm7 = store_thm("test_thm7",
  ``!(a:num).
    (a < 1) <=> (a = 0)``,

cheat
);

val test_thm8 = store_thm("test_thm8",
  ``!(a:num).
    (a > 0) ==>
    PRE a < a``,

cheat
);


val lift_contract_thm = store_thm("lift_contract_thm",
  ``!p mms ml mls mu mpre mpost bpre bpost.
      MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
      bir_triple p (BL_Address (Imm64 ml))
	{BL_Address (Imm64 ml') | ml' IN mls} bpre bpost ==>
      bir_is_lifted_prog arm8_bmr mu mms p ==>
      arm8_wf_varset (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
      bir_pre_arm8_to_bir mpre bpre ==>
      bir_post_bir_to_arm8 mpost bpost {BL_Address (Imm64 ml') | ml' IN mls} ==>
      arm8_triple mms ml mls mpre mpost``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [arm8_triple_def, weak_triple_def] >>
REPEAT STRIP_TAC >>
(* 1. Get bmr_rel arm8_bmr bs ms *)
(* The ARM state ms must be related to some Running BIR state with certain initialised variables
 * (will be called bs) *)
IMP_RES_TAC (SPECL [``ms:arm8_state``,
                   ``(bir_vars_of_program p) UNION (bir_vars_of_exp bpre)``]
                  exist_bir_of_arm8_thm) >>

(* 2. Expand BIR HT and identify the initial state as bs... *)
FULL_SIMP_TAC (std_ss++bir_wm_SS)
  [bir_triple_def, weak_triple_def,
   bir_exec_to_labels_triple_precond_def,
   bir_exec_to_labels_triple_postcond_def, bir_etl_wm_def] >>
PAT_X_ASSUM ``!s. _``
            (fn thm => ASSUME_TAC (SPEC ``bs:bir_state_t`` thm)) >>
(* ... then obtain antecedents: *)
(* variable initialisation *)
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
(* BIR precondition exp holding and is boolean *)
subgoal `bir_is_bool_exp_env bs.bst_environ bpre /\
         (bir_eval_exp bpre bs.bst_environ = SOME bir_val_true)` >- (
  METIS_TAC [bir_pre_arm8_to_bir_def, bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
(* PC of bs must be pointing to index 0 af a BIR address block *)
subgoal `(bs.bst_pc.bpc_index = 0) /\
         (bs.bst_pc.bpc_label = BL_Address (Imm64 ml))` >- (
  REPEAT (FULL_SIMP_TAC (srw_ss()) [arm8_bmr_rel_EVAL, bir_block_pc_def, arm_weak_model_def])
) >>
(* Then, knock out the BIR HT antecedents. This leaves us with a number of predicates on the final
 * state, which we will call bs'. *)
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
rename1 `bir_weak_trs {BL_Address (Imm64 ml') | ml' IN mls} p bs = SOME bs'` >>
(* Obtain that PC of bs' is in terminating label set, et.c. *)
FULL_SIMP_TAC std_ss [bir_weak_trs_EQ] >>
(* TODO: Clean-up? *)
Q.PAT_X_ASSUM `bs'.bst_status = BST_Running` (fn thm => ALL_TAC) >>

(* 3. Use bir_is_lifted_prog_MULTI_STEP_EXEC to obtain properties about the final machine state *)
ASSUME_TAC (ISPECL [``arm8_bmr``, ``mu:64 word_interval_t``,
                    ``mms:(word64# word8 list) list``,
                    ``p:'a bir_program_t``] bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Obtain bir_exec_address_n execution from bs to bs' *)
subgoal `?n' lo c_st c_addr_labels.
         bir_exec_to_addr_label_n p bs n' =
           BER_Ended lo c_st c_addr_labels bs'` >- (
  subgoal `bs'.bst_pc.bpc_label IN {l | IS_BL_Address l}` >- (
    METIS_TAC [set_of_address_in_all_address_labels_thm]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
                                        bir_exec_to_labels_n_def] >>
  subgoal `bir_pc_cond_impl (F,
	     (\pc.
	       (pc.bpc_index = 0) /\
	       pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls})) (F, (\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))` >- (
    FULL_SIMP_TAC std_ss [bir_pc_cond_impl_def] >>
    REPEAT STRIP_TAC >>
    METIS_TAC [set_of_address_in_all_address_labels_thm]
  ) >>
  IMP_RES_TAC bir_exec_steps_GEN_change_cond_Ended_SOME >>
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
(* Specialise with n' steps *)
QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC std_ss [] >>
Q.PAT_X_ASSUM `A ==> B` (fn thm => 
  Q.SUBGOAL_THEN `(?li.
		    MEM (BL_Address li) (bir_labels_of_program p) /\
		    (bs.bst_pc = bir_block_pc (BL_Address li)))`
                 (fn thm2 => ASSUME_TAC (SIMP_RULE std_ss [thm2] thm)) >- (
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``Imm64 ml`` >>
    FULL_SIMP_TAC (srw_ss()) [bir_block_pc_alt_thm]
  )
) >>
REV_FULL_SIMP_TAC std_ss [bir_programTheory.bir_state_is_terminated_def] >>
(* Fix naming inside bir_is_lifted_prog_MULTI_STEP_EXEC conclusion *)
RW_TAC (std_ss++holBACore_ss) [] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
(* Conclusion obtained, and with it the state ms' corresponding to bs'! *)

(* 4. Give ms' as witness to goal and prove the easy goal conjuncts *)
Q.EXISTS_TAC `ms'` >>
subgoal `arm8_bmr.bmr_extra ms'` >- (
  FULL_SIMP_TAC std_ss [bmr_rel_def]
) >>
subgoal `mpost ms'` >- (
  FULL_SIMP_TAC std_ss [bir_post_bir_to_arm8_def] >>
  QSPECL_X_ASSUM ``!ms. _``
    [`ms'`, `bs'`, `(bir_block_pc (BL_Address li)).bpc_label`] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >>

(* 5. Now the grande finale - execution goal! *)
(* 5a. Execution from initial to final state *)
SIMP_TAC (std_ss++bir_wm_SS) [arm_weak_model_def,
                              arm_weak_trs_def] >>
(* n in goal must be c_addr_labels *)
Q.EXISTS_TAC `c_addr_labels` >>
subgoal `c_addr_labels > 0` >- (
  (* This might follow from the fact that bir_exec_to_labels and bir_exec_to_addr_label_n
   * have same initial and final states, and bir_exec_to_labels must execute at least as
   * much as corresponds to one fulfilment of pc_cond in bir_exec_to_addr_label_n, as long as
   * initial and final states are Running.  *)
  IMP_RES_TAC test_thm >>
  FULL_SIMP_TAC arith_ss []
) >>
subgoal `ms'.PC IN mls` >- (
  subgoal `bs'.bst_pc = bir_block_pc (BL_Address (Imm64 ms'.PC))` >- (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [GEN_ALL bir_lifting_machinesTheory.arm8_bmr_rel_EVAL]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS) [bir_programTheory.bir_block_pc_def, arm_weak_model_def] >>
  RW_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (srw_ss()) []
) >>
FULL_SIMP_TAC std_ss [] >>

(* 5b. Intermediate execution steps *)
REPEAT STRIP_TAC >>
(* You now have a number of steps n'' to work with. You need to find the corresponding
 * BIR execution, prove that the resulting BIR state is Running with PC not in ls,
 * then use bir_is_lifted_prog_MULTI_STEP_EXEC *)
subgoal `n' = c_addr_labels` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  IMP_RES_TAC test_thm4
) >>
subgoal `?lo c_st c_addr_labels bs''.
         bir_exec_to_addr_label_n p bs n'' =
           BER_Ended lo c_st c_addr_labels bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  IMP_RES_TAC test_thm2 >>
  Q.EXISTS_TAC `ol'` >>
  Q.EXISTS_TAC `c_st'` >>
  Q.EXISTS_TAC `c_pc'` >>
  Q.EXISTS_TAC `st''` >>
  FULL_SIMP_TAC std_ss []
) >>
subgoal `bs''.bst_status = BST_Running` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  IMP_RES_TAC test_thm3
) >>
ASSUME_TAC (ISPECL [``arm8_bmr``, ``mu:64 word_interval_t``,
                    ``mms:(word64# word8 list) list``,
                    ``p:'a bir_program_t``]
                   bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
(* Specialise with n' steps *)
QSPECL_X_ASSUM ``!n ms bs. _`` [`n''`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC std_ss [bir_programTheory.bir_state_is_terminated_def] >>
(* TODO: WHY DOES THIS APPROACH NOT WORK HERE???
Q.PAT_X_ASSUM `A ==> B` (fn thm => 
  Q.SUBGOAL_THEN `(?li.
		    MEM (BL_Address li) (bir_labels_of_program p) /\
		    (bs.bst_pc = bir_block_pc (BL_Address li)))`
                 (fn thm2 => ASSUME_TAC (SIMP_RULE std_ss [thm2] thm)) >- (
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``Imm64 ml`` >>
    FULL_SIMP_TAC (srw_ss()) [bir_block_pc_alt_thm]
  )
) >>
*)
Q.SUBGOAL_THEN `(?li.
              MEM (BL_Address li) (bir_labels_of_program p) /\
              (bs.bst_pc = bir_block_pc (BL_Address li)))` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  Q.EXISTS_TAC `Imm64 (arm_weak_model.pc ms)` >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [] >>
    IMP_RES_TAC bir_block_pc_alt_thm
  )
) >>
REV_FULL_SIMP_TAC std_ss [] >>
RW_TAC (std_ss++holBACore_ss) [] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
(* Now, prove the goal using the conclusion... *)
(* ... execution: *)
Q.EXISTS_TAC `ms''` >>
subgoal `c_addr_labels' = n''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  IMP_RES_TAC test_thm4 >>
  FULL_SIMP_TAC std_ss []
) >>
RW_TAC std_ss [] >>
(* ... and ls non-membership: *)
subgoal `bs''.bst_pc.bpc_label NOTIN
           {BL_Address (Imm64 ml') | ml' IN mls}` >- (
  subgoal `n = c_st` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
                          bir_exec_to_labels_n_def] >>
    IMP_RES_TAC test_thm5
  ) >>
  subgoal `c_st' < c_st` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
                          bir_exec_to_labels_n_def] >>
    IMP_RES_TAC test_thm3
  ) >>
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def,
                        bir_exec_steps_GEN_SOME_EQ_Ended] >>
  QSPECL_X_ASSUM ``!(n:num). (n < c_st) ==> _`` [`c_st'`] >>
  REV_FULL_SIMP_TAC (arith_ss++holBACore_ss) [bir_exec_infinite_steps_fun_COUNT_PCs_def] >>
  subgoal `c_st' > 0` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
                          bir_exec_to_labels_n_def] >>
    IMP_RES_TAC test_thm6
  ) >>
  subgoal `~bir_state_COUNT_PC (F,
            (\pc.
                 (pc.bpc_index = 0) /\
                 pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}))
                (bir_exec_infinite_steps_fun p bs c_st')` >- (
    FULL_SIMP_TAC std_ss [test_thm7, bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
    QSPECL_X_ASSUM ``!j. _`` [`PRE c_st'`] >>
    SUBGOAL_THEN ``SUC (PRE (c_st':num)) = c_st'`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
      FULL_SIMP_TAC arith_ss []
    ) >>
    IMP_RES_TAC test_thm8 >>
    FULL_SIMP_TAC std_ss []
  ) >>
  subgoal `bs''.bst_pc.bpc_index = 0` >- (
    IMP_RES_TAC bir_exec_to_addr_label_n_ended_running >>
    REV_FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
  ) >>
  FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def] >>
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
                        bir_exec_steps_GEN_SOME_EQ_Ended] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
subgoal `bs''.bst_pc = bir_block_pc (BL_Address (Imm64 ms''.PC))` >- (
  (* TODO: WHY IS THE REPEAT NEEDED? *)
  REPEAT (REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [GEN_ALL bir_lifting_machinesTheory.arm8_bmr_rel_EVAL])
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS)
  [bir_programTheory.bir_block_pc_def, arm_weak_model_def] >>
RW_TAC (std_ss++holBACore_ss) [] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
FULL_SIMP_TAC (srw_ss()) []
);


val _ = export_theory();
