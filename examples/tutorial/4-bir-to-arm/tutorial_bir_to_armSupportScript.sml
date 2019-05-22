open HolKernel Parse boolLib bossLib;
open bir_expSimps;
open HolBACoreSimps;

val _ = new_theory "tutorial_bir_to_armSupport";

(* This part should be generalized *)

val arm8_triple_def = Define `
  arm8_triple mms l ls pre post =
  ! ms .
   (arm8_bmr.bmr_extra ms) ==>
   (EVERY (bmr_ms_mem_contains arm8_bmr ms) mms) ==>
   (ms.PC = l) ==>
   (pre ms) ==>
   ? c_addr_labels:num ms'.
    (FUNPOW_OPT arm8_bmr.bmr_step_fun c_addr_labels ms = SOME ms') /\     
    (ms'.PC IN ls) /\
    (post ms')
`;

val bir_triple_def = Define `
bir_triple p l ls pre post ⇔
 ! s.
  bir_env_vars_are_initialised s.bst_environ
    (bir_vars_of_program p) ⇒
  (s.bst_pc.bpc_index = 0) ∧ (s.bst_pc.bpc_label = l) ⇒
  (s.bst_status = BST_Running) ⇒
  bir_is_bool_exp_env s.bst_environ pre ⇒
  (bir_eval_exp pre s.bst_environ = bir_val_true) ⇒
  ?n l1 c1 c2 s'. 
      ((bir_exec_block_n p s n) = (l1, c1, c2, s')) ∧
      (s'.bst_status = BST_Running) ∧
      bir_is_bool_exp_env s'.bst_environ post ∧
      (bir_eval_exp post s'.bst_environ = bir_val_true) ∧
      (s'.bst_pc.bpc_index = 0) ∧ s'.bst_pc.bpc_label ∈ ls
`;


val same_var_is_bool_exp_env_eq_thm = prove(``
(bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre)) ==>
(bir_vars_of_exp pre' = bir_vars_of_exp pre) ==>
((bir_is_bool_exp_env s.bst_environ pre') =
 (bir_is_bool_exp_env s.bst_environ pre))
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_is_bool_exp_env_def,
bir_exp_tautologiesTheory.bir_exp_is_taut_def,
bir_bool_expTheory.bir_is_bool_exp_REWRS]);


val bir_triple_weak_rule_thm = store_thm("bir_triple_weak_rule_thm",  ``
  ((bir_vars_of_exp pre') = (bir_vars_of_exp pre)) ==>
  (bir_triple p l ls pre post) ==>
  (bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre)) ==>
  (bir_triple p l ls pre' post)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!s.p`` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
REV_FULL_SIMP_TAC (std_ss) [] >>
ASSUME_TAC same_var_is_bool_exp_env_eq_thm >>
REV_FULL_SIMP_TAC (std_ss) [] >>
FULL_SIMP_TAC (std_ss) [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
PAT_X_ASSUM ``!s.p`` (fn thm => ASSUME_TAC (Q.SPEC `s.bst_environ` thm)) >>
Q.SUBGOAL_THEN `bir_env_vars_are_initialised s.bst_environ
           (bir_vars_of_exp
              (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not pre') pre))` ASSUME_TAC >-
 FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.bir_vars_of_exp_def, pred_setTheory.UNION_IDEMPOT, bir_bool_expTheory.bir_is_bool_exp_env_def] >>
FULL_SIMP_TAC (std_ss) [] >> 
ASSUME_TAC (Q.SPECL [`s.bst_environ`, `pre'`, `pre`]  bir_exp_equivTheory.bir_impl_equiv) >>
REV_FULL_SIMP_TAC (std_ss) []
);


bir_triple p l ls pre post ⇔
 ! s.
  bir_env_vars_are_initialised s.bst_environ
    (bir_vars_of_program p) ⇒
  (s.bst_pc.bpc_index = 0) ∧ (s.bst_pc.bpc_label = l) ⇒
  (s.bst_status = BST_Running) ⇒
  bir_is_bool_exp_env s.bst_environ pre ⇒
  (bir_eval_exp pre s.bst_environ = bir_val_true) ⇒
  ?n l1 c1 c2 s'. 
      ((bir_exec_block_n p s n) = (l1, c1, c2, s')) ∧
      (s'.bst_status = BST_Running) ∧
      bir_is_bool_exp_env s'.bst_environ post ∧
      (bir_eval_exp post s'.bst_environ = bir_val_true) ∧
      (s'.bst_pc.bpc_index = 0) ∧ s'.bst_pc.bpc_label ∈ ls
`;


val bir_pre_arm8_to_bir_def = Define `
  bir_pre_arm8_to_bir pre pre_bir =
  bir_is_bool_exp pre_bir /\
  ! ms bs.
  (bmr_rel arm8_bmr bs ms) ==>
  (bir_env_vars_are_initialised bs.bst_environ (bir_vars_of_exp pre_bir)) ==>
  (pre ms) ==>
  (bir_eval_exp pre_bir bs.bst_environ = bir_val_true)`;

val bir_post_bir_to_arm8_def = Define `
  bir_post_bir_to_arm8 post post_bir =
  ! ms bs.
  (bmr_rel arm8_bmr bs ms) ==>
  (bir_eval_exp post_bir bs.bst_environ = bir_val_true) ==>
  (post ms)
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


val bload_64_to_arm8_load_64_thm = store_thm("bload_64_to_arm8_load_64_thm", ``
!bs ms. (bmr_rel arm8_bmr bs ms) ==>
(!a.
((bir_eval_load
        (bir_env_read (BVar "MEM" (BType_Mem Bit64 Bit8)) bs.bst_environ)
        (BVal_Imm (Imm64 a)) BEnd_LittleEndian Bit64) =
 (BVal_Imm (Imm64 (arm8_load_64 ms.MEM a)))))
 ``,
 REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `(∃mem_n.
       (bir_env_read (BVar "MEM" (BType_Mem Bit64 Bit8)) bs.bst_environ =
        BVal_Mem Bit64 Bit8 mem_n) ∧
       (ms.MEM = (λa. n2w (bir_load_mmap mem_n (w2n a)))) ∧
       bir_env_var_is_declared bs.bst_environ
         (BVar "tmp_MEM" (BType_Mem Bit64 Bit8)))` ASSUME_TAC >-
   (FULL_SIMP_TAC (std_ss) [bir_lifting_machinesTheory.arm8_bmr_rel_EVAL] >>
    EXISTS_TAC `` mem_n:num|->num`` >>
    FULL_SIMP_TAC (std_ss) []
   ) >>
FULL_SIMP_TAC (std_ss) [bir_expTheory.bir_eval_load_FULL_REWRS, arm8_load_64_def] >>
 FULL_SIMP_TAC (srw_ss()) []
 );

val bool2w_and = prove(``!a b. ((bool2w a) && (bool2w b)) = (bool2w (a /\ b))``,
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss) [bool2w_def] >>
    Cases_on `a` >>
    Cases_on `b` >>
    EVAL_TAC);

val imm_eq_to_val_eq = prove(``!a b . ((BVal_Imm(Imm1 a)) = (BVal_Imm(Imm1 b))) = (a = b)``,
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
 bst_environ := BEnv (FEMPTY
 |+ ("ProcState_C",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.C)))
 |+ ("tmp_ProcState_C",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.C)))
 |+ ("ProcState_N",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.N)))
 |+ ("tmp_ProcState_N",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.N)))
 |+ ("ProcState_V",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.V)))
 |+ ("tmp_ProcState_V",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.V)))
 |+ ("ProcState_Z",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.Z)))
 |+ ("tmp_ProcState_Z",BType_Imm Bit1, SOME(BVal_Imm (bool2b ms.PSTATE.Z)))
 |+ ("R0",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 0w))))
 |+ ("tmp_R0",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 0w))))
 |+ ("R1",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 1w))))
 |+ ("tmp_R1",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 1w))))
 |+ ("R2",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 2w))))
 |+ ("tmp_R2",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 2w))))
 |+ ("R3",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 3w))))
 |+ ("tmp_R3",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 3w))))
 |+ ("R4",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 4w))))
 |+ ("tmp_R4",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 4w))))
 |+ ("R5",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 5w))))
 |+ ("tmp_R5",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 5w))))
 |+ ("R6",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 6w))))
 |+ ("tmp_R6",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 6w))))
 |+ ("R7",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 7w))))
 |+ ("tmp_R7",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 7w))))
 |+ ("R8",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 8w))))
 |+ ("tmp_R8",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 8w))))
 |+ ("R9",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 9w))))
 |+ ("tmp_R9",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 9w))))
 |+ ("R10",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 10w))))
 |+ ("tmp_R10",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 10w))))
 |+ ("R11",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 11w))))
 |+ ("tmp_R11",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 11w))))
 |+ ("R12",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 12w))))
 |+ ("tmp_R12",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 12w))))
 |+ ("R13",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 13w))))
 |+ ("tmp_R13",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 13w))))
 |+ ("R14",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 14w))))
 |+ ("tmp_R14",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 14w))))
 |+ ("R15",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 15w))))
 |+ ("tmp_R15",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 15w))))
 |+ ("R16",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 16w))))
 |+ ("tmp_R16",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 16w))))
 |+ ("R17",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 17w))))
 |+ ("tmp_R17",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 17w))))
 |+ ("R18",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 18w))))
 |+ ("tmp_R18",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 18w))))
 |+ ("R19",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 19w))))
 |+ ("tmp_R19",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 19w))))
 |+ ("R20",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 20w))))
 |+ ("tmp_R20",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 20w))))
 |+ ("R21",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 21w))))
 |+ ("tmp_R21",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 21w))))
 |+ ("R22",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 22w))))
 |+ ("tmp_R22",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 22w))))
 |+ ("R23",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 23w))))
 |+ ("tmp_R23",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 23w))))
 |+ ("R24",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 24w))))
 |+ ("tmp_R24",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 24w))))
 |+ ("R25",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 25w))))
 |+ ("tmp_R25",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 25w))))
 |+ ("R26",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 26w))))
 |+ ("tmp_R26",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 26w))))
 |+ ("R27",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 27w))))
 |+ ("tmp_R27",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 27w))))
 |+ ("R28",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 28w))))
 |+ ("tmp_R28",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 28w))))
 |+ ("R29",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 29w))))
 |+ ("tmp_R29",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 29w))))
 |+ ("R30",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 30w))))
 |+ ("tmp_R30",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 30w))))
 |+ ("R31",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 31w))))
 |+ ("tmp_R31",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.REG 31w))))
 |+ ("SP_EL0",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL0))))
 |+ ("tmp_SP_EL0",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL0))))
 |+ ("SP_EL1",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL1))))
 |+ ("tmp_SP_EL1",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL1))))
 |+ ("SP_EL2",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL2))))
 |+ ("tmp_SP_EL2",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL2))))
 |+ ("SP_EL3",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL3))))
 |+ ("tmp_SP_EL3",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.SP_EL3))))
 |+ ("tmp_PC",BType_Imm Bit64, SOME(BVal_Imm (Imm64 (ms.PC))))
 |+ ("MEM", (BType_Mem Bit64 Bit8), SOME(BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM))))
 |+ ("tmp_MEM", (BType_Mem Bit64 Bit8), SOME(BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM))))
 |+ ("tmp_COND",BType_Imm Bit1, SOME(BVal_Imm (Imm1 0w)))
 );
  bst_status := BST_Running|>
`;


val default_arm8_bir_state_satisfies_rel_thm = prove(``
!ms .
(arm8_bmr.bmr_extra ms) ==>
   (bmr_rel arm8_bmr (default_arm8_bir_state ms) ms)
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [default_arm8_bir_state_def,
 bir_lifting_machinesTheory.arm8_bmr_rel_EVAL,
 bir_envTheory.bir_env_var_is_declared_def,
 bir_envTheory.bir_var_name_def] >>
FULL_SIMP_TAC (srw_ss()) [
              bir_envTheory.bir_env_read_UPDATE, bir_envTheory.bir_var_name_def,
              bir_envTheory.bir_env_lookup_UPDATE,
              bir_envTheory.bir_var_type_def, bir_envTheory.bir_env_lookup_type_def] >>
FULL_SIMP_TAC (std_ss) [bir_lifting_machinesTheory.bmr_extra_ARM8] >>
FULL_SIMP_TAC (srw_ss()) [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm] >>
METIS_TAC []
);


val exist_bir_of_arm8_thm = prove(``
!ms vars .
(arm8_wf_varset vars) ==>
(arm8_bmr.bmr_extra ms) ==>
? bs .((bmr_rel arm8_bmr bs ms) /\ (bs.bst_status = BST_Running) /\ (bir_env_vars_are_initialised bs.bst_environ vars))
``,
REPEAT STRIP_TAC >> 
EXISTS_TAC ``default_arm8_bir_state ms`` >>
ASSUME_TAC (SPEC ``ms:arm8_state`` default_arm8_bir_state_satisfies_rel_thm) >>
FULL_SIMP_TAC (std_ss) [] >>
STRIP_TAC >-  EVAL_TAC >>
PAT_X_ASSUM ``arm8_wf_varset vars`` (fn thm=> REWRITE_TAC [SIMP_RULE std_ss [arm8_wf_varset_def] thm]) >>
FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_env_vars_are_initialised_INSERT] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_env_var_is_initialised_def] >>
FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_var_name_def, default_arm8_bir_state_def, bir_envTheory.bir_env_lookup_UPDATE] >>
EVAL_TAC>>
FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_t_11, bir_immTheory.type_of_bir_imm_def, bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
);

val set_of_address_in_all_address_labels_thm = prove (``
!l adds.
(l ∈ {BL_Address (Imm64 ml') | ml' ∈ adds}) ==>
(l ∈ {l | IS_BL_Address l})
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def]
);

(*
val bir_block_pc_alt_thm = prove(``
! pc l.
(pc.bpc_label = l) ==>
(pc.bpc_index = 0) ==>
(pc = (bir_block_pc l))
``,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [bir_programTheory.bir_block_pc_def] >>
cheat);

prove(``
! p mms ml mls mu
mpre mpost bpre bpost .
(MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p)) ==>
bir_triple p (BL_Address (Imm64 ml)) {(BL_Address (Imm64 ml')) | ml' IN mls} bpre bpost ==>
bir_is_lifted_prog arm8_bmr mu mms p ==>
(arm8_wf_varset ((bir_vars_of_program p) ∪ (bir_vars_of_exp bpre))) ==>
bir_pre_arm8_to_bir mpre bpre ==>
bir_post_bir_to_arm8 mpost bpost ==>
arm8_triple mms ml mls mpre mpost
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [arm8_triple_def] >> 
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``ms:arm8_state``, ``(bir_vars_of_program p) ∪  (bir_vars_of_exp bpre)``] exist_bir_of_arm8_thm) >>
REV_FULL_SIMP_TAC (std_ss) [] >>
FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_env_vars_are_initialised_UNION] >>

Q.SUBGOAL_THEN `(bir_eval_exp bpre bs.bst_environ = bir_val_true)` ASSUME_TAC >-
  (METIS_TAC [bir_pre_arm8_to_bir_def]) >>

(FULL_SIMP_TAC (std_ss) [bir_triple_def]) >>
(PAT_X_ASSUM ``!s.P`` (fn thm => ASSUME_TAC (SPEC ``bs:bir_state_t`` thm))) >>

Q.SUBGOAL_THEN ` (bs.bst_pc.bpc_index = 0) ∧
         (bs.bst_pc.bpc_label = BL_Address (Imm64 ml))` ASSUME_TAC >-
  (REPEAT (FULL_SIMP_TAC (srw_ss()) [bir_lifting_machinesTheory.arm8_bmr_rel_EVAL, bir_programTheory.bir_block_pc_def])) >>
FULL_SIMP_TAC (std_ss) [] >>
REV_FULL_SIMP_TAC (std_ss) [] >>

Q.SUBGOAL_THEN `bir_is_bool_exp_env bs.bst_environ bpre` ASSUME_TAC >-
  (REPEAT (FULL_SIMP_TAC (srw_ss()) [bir_bool_expTheory.bir_is_bool_exp_env_def, bir_pre_arm8_to_bir_def])) >>
FULL_SIMP_TAC (std_ss) [] >>

(Q.SUBGOAL_THEN `
    s'.bst_pc.bpc_label ∈ {l | IS_BL_Address l}` ASSUME_TAC) >-
    (METIS_TAC [set_of_address_in_all_address_labels_thm]) >>

ASSUME_TAC (ISPECL [``p:'a bir_program_t``, ``bs:bir_state_t``, ``n:num``,
       ``l1:'a list``,``c1:num``, ``c2:num``, ``s':bir_state_t``,
       ``{l | IS_BL_Address l}``]exec_n_to_label_thm) >>
REV_FULL_SIMP_TAC (std_ss) [] >>


ASSUME_TAC (ISPECL [`` arm8_bmr``, ``mu:64 word_interval_t``,
           ``mms:(word64# word8 list) list``, ``p:'a bir_program_t``]
           bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC (std_ss) [] >>

PAT_X_ASSUM ``!n.p`` (fn thm => ASSUME_TAC (SPECL [``n':num``, ``ms:arm8_state``, ``bs:bir_state_t``] thm)) >>
REV_FULL_SIMP_TAC (std_ss) [] >>

(Q.SUBGOAL_THEN `
    (∃li.
              MEM (BL_Address li) (bir_labels_of_program p) ∧
              (bs.bst_pc = bir_block_pc (BL_Address li)))` ASSUME_TAC) >-
 (REPEAT STRIP_TAC >>
  EXISTS_TAC ``(Imm64 ml)`` >>
  FULL_SIMP_TAC (srw_ss()) [bir_block_pc_alt_thm]) >>
FULL_SIMP_TAC (std_ss) [] >>

REV_FULL_SIMP_TAC (std_ss) [bir_programTheory.bir_state_is_terminated_def] >>
REV_FULL_SIMP_TAC (std_ss) [bir_inst_liftingTheory.bir_exec_to_addr_label_n_def] >>

(Q.SUBGOAL_THEN `bs'=s'` ASSUME_TAC >- RW_TAC (std_ss) []) >>
FULL_SIMP_TAC (srw_ss()) [] >>
REV_FULL_SIMP_TAC (srw_ss()) [] >>

EXISTS_TAC ``c_addr_labels':num`` >>
EXISTS_TAC ``ms':arm8_state`` >>
FULL_SIMP_TAC (srw_ss()) [] >>

Q.SUBGOAL_THEN `mpost ms'` ASSUME_TAC >-
  (METIS_TAC [bir_post_bir_to_arm8_def]) >>
FULL_SIMP_TAC (srw_ss()) [] >>

Q.SUBGOAL_THEN `(s'.bst_pc = bir_block_pc (BL_Address (Imm64 ms'.PC)))` ASSUME_TAC >-
  (FULL_SIMP_TAC (std_ss++holBACore_ss) [GEN_ALL bir_lifting_machinesTheory.arm8_bmr_rel_EVAL]) >>

FULL_SIMP_TAC (std_ss) [bir_programTheory.bir_block_pc_def] >>
FULL_SIMP_TAC (srw_ss()) [] >>



FULL_SIMP_TAC (std_ss) [bir_lifting_machinesTheory.bmr_rel_def,
              bir_lifting_machinesTheory.bir_machine_lifted_pc_def,
              bir_lifting_machinesTheory.arm8_bmr_def] >>

cheat);
*)


val _ = export_theory();
