open HolKernel Parse boolLib bossLib;

open bir_immTheory;
open bir_programTheory;
open bir_tsTheory;
open bir_program_multistep_propsTheory;
open holba_auxiliaryTheory;

(* From lifter: *)
open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;

(* From comp: *)
open total_program_logicTheory;
open total_ext_program_logicTheory;

open bir_common_backlifterTheory;

open HolBASimps;
open HolBACoreSimps;
open program_logicSimps;

open holba_auxiliaryLib;

open m0_mod_stepLib;

val _ = new_theory "bir_arm8_backlifter";

(* This part should be generalized *)
(*
Definition arm8_cont_def:
  arm8_cont mms l ls pre post =
  !ms.
   (arm8_bmr.bmr_extra ms) ==>
   (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) ==>
   (ms.PC = l) ==>
   (pre ms) ==>
   ?c_addr_labels:num ms'.
    (FUNPOW_OPT arm8_bmr.bmr_step_fun c_addr_labels ms = SOME ms') /\     
    (ms'.PC IN ls) /\
    (post ms')
End
*)
Definition arm_weak_trs_def:
  arm_weak_trs ls ms ms' = 
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
            )
End


Definition arm_ts_def:
  arm_ts  = <|
    trs  := arm8_bmr.bmr_step_fun;
    weak := arm_weak_trs;
    ctrl   := (\st. st.PC)
  |>
End


(* The main contract to be used for ARM composition *)
Definition arm8_cont_def:
  arm8_cont mms l ls pre post =
    t_jgmt arm_ts l ls
      (\ms. (arm8_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) /\
            (pre ms))         
      (\ms. (arm8_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) /\
            (post ms))
End


Definition bir_pre_arm8_to_bir_def:
  bir_pre_arm8_to_bir pre pre_bir = (
    bir_is_bool_exp pre_bir /\
    !ms bs.
    bmr_rel arm8_bmr bs ms ==>
    bir_env_vars_are_initialised bs.bst_environ (bir_vars_of_exp pre_bir) ==>
    pre ms ==>
    (bir_eval_exp pre_bir bs.bst_environ = SOME bir_val_true))
End

Definition bir_post_bir_to_arm8_def:
  bir_post_bir_to_arm8 post post_bir ls =
    !ms bs l.
    l IN ls ==>
    bmr_rel arm8_bmr bs ms ==>
    (bir_eval_exp (post_bir l) bs.bst_environ = SOME bir_val_true) ==>
    post ms
End


Definition arm8_load_64_def:
  arm8_load_64 m a =
  (((m (a + 7w)) @@
  (((m (a + 6w)) @@
  (((m (a + 5w)) @@
  (((m (a + 4w)) @@
  (((m (a + 3w)) @@
   (((m (a + 2w)) @@
     ((m (a + 1w)) @@ (m (a + 0w))):bool[16]):bool[24])):bool[32])
    ):bool[40])):bool[48])):bool[56])):bool[64])
End

Theorem bload_64_to_arm8_load_64_thm:
  !bs ms. (bmr_rel arm8_bmr bs ms) ==>
    (!a.
    ((bir_eval_load
      (bir_env_read (BVar "MEM" (BType_Mem Bit64 Bit8)) bs.bst_environ)
      (SOME (BVal_Imm (Imm64 a))) BEnd_LittleEndian Bit64) =
        SOME (BVal_Imm (Imm64 (arm8_load_64 ms.MEM a))))
    )
Proof
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
QED




Definition arm8_vars_def:
  arm8_vars= {
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
  }
End

Definition arm8_wf_varset_def:
  arm8_wf_varset vset = (vset SUBSET arm8_vars)
End

Definition default_arm8_bir_state_def:
  default_arm8_bir_state ms =
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
End


Theorem default_arm8_bir_state_satisfies_rel_thm[local]:
  !ms.
    arm8_bmr.bmr_extra ms ==>
    bmr_rel arm8_bmr (default_arm8_bir_state ms) ms
Proof
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
QED


Theorem exist_bir_of_arm8_thm[local]:
  !ms vars.
    arm8_wf_varset vars ==>
    arm8_bmr.bmr_extra ms ==>
    ?bs.
      (bmr_rel arm8_bmr bs ms /\ (bs.bst_status = BST_Running) /\
       bir_env_vars_are_initialised bs.bst_environ vars)
Proof
REPEAT STRIP_TAC >> 
EXISTS_TAC ``default_arm8_bir_state ms`` >>
ASSUME_TAC (SPEC ``ms:arm8_state`` default_arm8_bir_state_satisfies_rel_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
STRIP_TAC >- (
  EVAL_TAC
) >>
irule bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
Q.EXISTS_TAC `arm8_vars` >>
FULL_SIMP_TAC std_ss [arm8_wf_varset_def] >>
SIMP_TAC std_ss [arm8_vars_def] >>
(* TODO: This proof is sloooow... *)
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_var_is_initialised_def] >>
FULL_SIMP_TAC std_ss [bir_envTheory.bir_var_name_def, default_arm8_bir_state_def,
                        bir_envTheory.bir_env_lookup_UPDATE] >>
EVAL_TAC  >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_t_11,
                      bir_immTheory.type_of_bir_imm_def,
                      bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
QED




Theorem bir_arm8_block_pc[local]:
  !bs ms ml.
    bmr_rel arm8_bmr bs ms ==>
    (arm_ts.ctrl ms = ml) ==>
    (bs.bst_status = BST_Running) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml)))
Proof
REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS)
  [arm8_bmr_rel_EVAL, bir_block_pc_def, arm_ts_def]
QED


Theorem bir_get_ht_conseq_from_m_ante[local]:
  !bs p bpre bpost mpre ms ml mls.
    bir_cont p bir_exp_true (BL_Address (Imm64 ml))
      {BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
    bir_pre_arm8_to_bir mpre bpre ==>
    mpre ms ==>
    bmr_rel arm8_bmr bs ms ==>
    (bs.bst_status = BST_Running) ==>
    bir_env_vars_are_initialised bs.bst_environ
      (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (?bs'.
     (bir_weak_trs {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       SOME bs') /\
     (bir_eval_exp (bpost bs'.bst_pc.bpc_label) bs'.bst_environ =
       SOME bir_val_true)
    )
Proof
REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
  [bir_cont_def, t_ext_jgmt_def, t_jgmt_def,
   bir_exec_to_labels_triple_precond_def,
   bir_exec_to_labels_triple_postcond_def, bir_ts_def] >>
PAT_X_ASSUM ``!s. _``
            (fn thm => ASSUME_TAC (SPEC ``bs:bir_state_t`` thm)) >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
subgoal `bir_is_bool_exp_env bs.bst_environ bpre /\
         (bir_eval_exp bpre bs.bst_environ = SOME bir_val_true)` >- (
  METIS_TAC [bir_pre_arm8_to_bir_def, bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
  [bir_bool_expTheory.bir_eval_exp_TF,
   bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
   bir_block_pc_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED


Theorem bir_arm8_exec_in_end_label_set[local]:
  !c_addr_labels ms' bs bs' mls p n n' lo li.
    (* Execution from BIR HT *)
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n c_addr_labels bs') ==>
    (n' > 0) ==>
    ~bir_state_is_terminated bs' ==>
    (bs'.bst_pc = bir_block_pc (BL_Address li)) ==>
    ((bir_block_pc (BL_Address li)).bpc_label IN
         {BL_Address (Imm64 ml') | ml' IN mls}) ==>
    (* BMR relation between the final states *)
    bmr_rel arm8_bmr bs' ms' ==>
    c_addr_labels > 0 /\
    ms'.PC IN mls
Proof
REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
subgoal `c_addr_labels > 0` >- (
  Cases_on `c_addr_labels = 0` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
                          bir_exec_steps_GEN_SOME_EQ_Ended] >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC arith_ss []
) >>
subgoal `ms'.PC IN mls` >- (
  subgoal `bs'.bst_pc = bir_block_pc (BL_Address (Imm64 ms'.PC))` >- (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_is_terminated_def,
       GEN_ALL bir_lifting_machinesTheory.arm8_bmr_rel_EVAL]
  ) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setLib.PRED_SET_ss)
    [bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
FULL_SIMP_TAC std_ss []
QED




Theorem bir_arm8_inter_exec[local]:
  !n' c_addr_labels n0 ms ml mls bs bs' p lo l c_st n mu mms.
    bir_is_lifted_prog arm8_bmr mu mms p ==>
    EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ==>
    (arm_ts.ctrl ms = ml) ==>
    (MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p)) ==>
    bmr_rel arm8_bmr bs ms ==>
    ~bir_state_is_terminated bs ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs = BER_Ended l c_st n0 bs') ==>
    ~bir_state_is_terminated bs' ==>
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo c_st c_addr_labels bs') ==>
    (!n''.
       n'' < c_addr_labels /\ n'' > 0 ==>
       ?ms''.
	 (FUNPOW_OPT arm8_bmr.bmr_step_fun n'' ms = SOME ms'') /\
	 ms''.PC NOTIN mls
    )
Proof
REPEAT STRIP_TAC >>
(* The given number of address labels has been reached by bir_exec_to_addr_label_n when
 * resulting Ended state bs' is not terminated *)
Q.SUBGOAL_THEN `c_addr_labels = n'` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
(* For some smaller number of address labels n'', bir_exec_to_addr_label_n also Ends
 * (in bs'') *)
subgoal `?lo' c_st' c_addr_labels' bs''.
         bir_exec_to_addr_label_n p bs n'' =
           BER_Ended lo' c_st' c_addr_labels' bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_SOME]
) >>
(* Since the later state bs' is Running, bs'' must be Running as well... *)
subgoal `~bir_state_is_terminated bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_terminated]
) >>
(* ... with the given number of address labels reached. *)
Q.SUBGOAL_THEN `c_addr_labels' = n''` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
(* Now, prove that there is some state ms'' such that ms'' and bs'' are related in the
 * sense of bmr_rel, with some additional sanity statements on PC and memory.
 * Furthermore, ms'' is reached from ms by n'' applications of the machine step. *)
subgoal `?ms'' li.
         bmr_rel arm8_bmr bs'' ms'' /\
         EVERY (bmr_ms_mem_contains arm8_bmr ms'') mms /\
         bmr_ms_mem_unchanged arm8_bmr ms ms'' mu /\
         MEM (BL_Address li) (bir_labels_of_program p) /\
         (bs''.bst_pc = bir_block_pc (BL_Address li)) /\
         (FUNPOW_OPT arm8_bmr.bmr_step_fun n'' ms = SOME ms'')` >- (
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
  METIS_TAC []
) >>
(* We have proven how some ms'' (in fact, the free variable ms'') can be reached
 * from ms by n'' applications of the machine step. It remains to prove that ms'' cannot
 * be a member of the Ending label set mls.
 * First, we prove a similar property for the label of bs'', then we translate this to
 * ms''. This can be easily done since both are word64 terms in different wrapping. *)
subgoal `bs''.bst_pc.bpc_label NOTIN
           {BL_Address (Imm64 ml') | ml' IN mls}` >- (
  subgoal `c_st' < c_st` >- (
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
	       bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_decrease_max_steps_Ended_steps_taken]
  ) >>
  METIS_TAC [bir_inter_exec_notin_end_label_set]
) >>
Q.EXISTS_TAC `ms''` >>
(* Prove correspondence between the labels of the machine state PC and the BIR PC. *)
subgoal `bs''.bst_pc = bir_block_pc (BL_Address (Imm64 ms''.PC))` >- (
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
    [GEN_ALL arm8_bmr_rel_EVAL, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS++pred_setLib.PRED_SET_ss)
  [bir_block_pc_def]
QED


Theorem arm8_lift_contract_thm:
  !p mms ml mls mu mpre mpost bpre bpost.
    MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
    bir_cont p bir_exp_true (BL_Address (Imm64 ml))
      {BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
    bir_is_lifted_prog arm8_bmr mu mms p ==>
    arm8_wf_varset (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
    bir_pre_arm8_to_bir mpre bpre ==>
    bir_post_bir_to_arm8 mpost bpost {BL_Address (Imm64 ml') | ml' IN mls} ==>
    arm8_cont mms ml mls mpre mpost
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [arm8_cont_def, t_jgmt_def] >>
REPEAT STRIP_TAC >>
(* 1. Among the assumptions we now also have the antecedents of the arm8
 *    HT. Combining these, exist_bir_of_arm8_thm gives that there is a
 *    Running BIR state bs where the variables of arm8_wf_varset are
 *    initialised which is related to (in the sense of bmr_rel) the the
 *    arm8 machine state ms. *)
IMP_RES_TAC (SPECL [``ms:arm8_state``,
                    ``(bir_vars_of_program p) UNION (bir_vars_of_exp bpre)``]
                  exist_bir_of_arm8_thm) >>

(* 2. The assumptions now allow us to prove the antecedents of the BIR HT
 *    and obtain the consequent. This states that the BIR weak transition
 *    from bs to some state in the Ending label set mls results in some
 *    state bs', in which the BIR postcondition bpost holds.
 *    Furthermore, the PC of bs points to the first statement in the block
 *    with label ml. *)
IMP_RES_TAC bir_arm8_block_pc >>
IMP_RES_TAC bir_get_ht_conseq_from_m_ante >>
FULL_SIMP_TAC std_ss [bir_weak_trs_EQ] >>

(* 3. Then, bir_is_lifted_prog_MULTI_STEP_EXEC is used to obtain the
 *    existence of some arm8 machine state ms' related to bs'
 *    (in the sense of bmr_rel) and some properties related to it. *)
IMP_RES_TAC bir_exec_to_labels_TO_exec_to_addr_label_n >>
IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

(* 4. Give ms' as witness to goal and prove the easy goal conjuncts -
 *    all but arm_ts.weak ms mls ms', which is a statement on how ms
 *    and ms' are related through a weak transition *)
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

(* 5. Show that the weak transition in the goal exists *)
SIMP_TAC (std_ss++bir_wm_SS) [arm_ts_def,
                              arm_weak_trs_def] >>
Q.EXISTS_TAC `c_addr_labels` >>
(* 5a. Weak transition from initial state ms ends in final state ms':
 *     Machine-stepping from ms to ms' already exists among assumptions,
 *     PC of final state ms' must be in Ending label set mls due to BIR HT
 *     execution, plus the fact that bs' and ms' are related *)
IMP_RES_TAC bir_arm8_exec_in_end_label_set >>
FULL_SIMP_TAC std_ss [] >>

(* 5b. Machine steps from ms up until ms' is reached:
 *     This part of the proof is complex, see proof of lemma used *)
METIS_TAC [bir_state_is_terminated_def, bir_arm8_inter_exec]
QED

val _ = export_theory();
