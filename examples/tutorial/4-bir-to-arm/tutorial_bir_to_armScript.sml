(* Code specific for the example *)
open HolKernel Parse boolLib bossLib;
open bir_expSimps;
open tutorial_bir_to_armSupportTheory;

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
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS, bir_valuesTheory.BType_Bool_def ])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
FULL_SIMP_TAC (std_ss) [bool2w_def, bir_bool_expTheory.bir_val_true_def] >>
EVAL_TAC
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
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def,
         bir_immTheory.bool2b_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS, bir_valuesTheory.BType_Bool_def ])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
FULL_SIMP_TAC (std_ss) [bir_immTheory.bool2w_11, bool2w_and, bir_bool_expTheory.bir_val_true_def, imm_eq_to_val_eq, bir_bool_expTheory.bool2w_ELIMS] 
);









(*
open bir_subprogramLib;
open bir_programSyntax;

val (_, bir_prog) =
         dest_comb
           (concl examples_arm8_program_THM);

val tutorial_prog_def = Define `tutorial_prog = ^bir_prog`;

EVAL ``MEM (BL_Address (Imm64 0x70cw)) (bir_labels_of_program tutorial_prog)``;
EVAL ``arm8_wf_varset (bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_program tutorial_prog)``;
*)

val _ = export_theory();
