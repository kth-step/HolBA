open HolKernel Parse boolLib bossLib;
open examplesBinaryTheory;
open bir_expSimps;

val _ = new_theory "tutorial_lift";

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
      ∨      (s'.bst_status = BST_AssumptionViolated)
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



(* Code specific for the example *)


val arm8_sqrt_I_def = Define `arm8_sqrt_I m =
  (((arm8_load_64 m.MEM (m.SP_EL0+16w)) * (arm8_load_64 m.MEM (m.SP_EL0+16w))) <=+ (arm8_load_64 m.MEM (m.SP_EL0+8w))) /\
  (m.PSTATE.C = ((((arm8_load_64 m.MEM (m.SP_EL0+16w)) + 1w) * ((arm8_load_64 m.MEM (m.SP_EL0+16w))+1w)) <+ (arm8_load_64 m.MEM (m.SP_EL0+8w))))
`;

val get_y = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 16w))) BEnd_LittleEndian
                        Bit64)``;
val get_x = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                        Bit64)``;


val b_sqrt_I_def = Define `b_sqrt_I =
(BExp_BinExp BIExp_And 
   (BExp_BinPred BIExp_LessOrEqual
      (BExp_BinExp BIExp_Mult (^get_y) (^get_y)
      )(^get_x)
   )
   ((BExp_BinPred BIExp_Equal
     (BExp_BinPred BIExp_LessThan
        (BExp_BinExp BIExp_Mult (BExp_BinExp BIExp_Plus (^get_y) (BExp_Const (Imm64 1w))) (BExp_BinExp BIExp_Plus (^get_y) (BExp_Const (Imm64 1w)))
        )(^get_x)
     )
     (BExp_Den (BVar "ProcState_C" BType_Bool))
     )))
   `;


val bir_I_is_bool_pred_thm = prove(
  ``bir_is_bool_exp b_sqrt_I``,

FULL_SIMP_TAC (std_ss++bir_is_bool_ss) [b_sqrt_I_def]
);

val arm8I_imp_bI_thm = store_thm("arm8I_imp_bI_thm", 
``bir_pre_arm8_to_bir arm8_sqrt_I b_sqrt_I``
,
FULL_SIMP_TAC (std_ss) [bir_pre_arm8_to_bir_def, bir_I_is_bool_pred_thm] >>
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss) [b_sqrt_I_def, bir_expTheory.bir_eval_exp_def] >>
(SIMP_TAC (std_ss) (((CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE) bir_lifting_machinesTheory.arm8_bmr_rel_EVAL) @
  [bir_expTheory.bir_eval_bin_exp_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] @
  [bir_expTheory.bir_eval_bin_pred_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def,
         bir_immTheory.bool2b_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
cheat
);


val bI_imp_arm8I_thm = store_thm("bI_imp_arm8I_thm",
``
bir_post_bir_to_arm8  arm8_sqrt_I b_sqrt_I 
``,
FULL_SIMP_TAC (std_ss) [bir_post_bir_to_arm8_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [b_sqrt_I_def, bir_expTheory.bir_eval_exp_def] >>
(FULL_SIMP_TAC (std_ss) (((CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE) bir_lifting_machinesTheory.arm8_bmr_rel_EVAL) @
  [bir_expTheory.bir_eval_bin_exp_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] @
  [bir_expTheory.bir_eval_bin_pred_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
cheat
);


val _ = export_theory();
