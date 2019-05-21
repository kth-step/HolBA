(* Code specific for the example *)
open HolKernel Parse boolLib bossLib;
open bir_expSimps;
open tutorial_bir_to_armSupportTheory;
open bslSyntax;

val y_addr = ``24w:word64``;
val x_addr = ``8w:word64``;
val y_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^y_addr)))``;
val x_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^x_addr)))``;



(* unsigned comparison *)
EVAL ``255w <=+ (0w:word8)``;
(* Signed comparison *)
EVAL ``255w <= (0w:word8)``;


val arm8_sp_ok = ``(m.SP_EL0 >=+ 0xC0000000w) /\ (m.SP_EL0 <+ 0xD0000000w)``;

val arm8_sqrt_pre_def = Define `arm8_sqrt_pre m =
  ((^x_var) >= 0w) /\
  (^arm8_sp_ok)
`;
val arm8_sqrt_post_def = Define `arm8_sqrt_post m =
  (((^y_var)  * (^y_var)) <= (^x_var)) /\
  ((((^y_var)+1w)  * ((^y_var)+1w)) > (^x_var)) /\
  (^arm8_sp_ok)
`;

val get_y = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^y_addr)))) BEnd_LittleEndian
                        Bit64)``;
val get_x = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^x_addr)))) BEnd_LittleEndian
                        Bit64)``;


val bir_sp_ok = 
band (
     bnot (blt((bden (bvar "SP_EL0" ``(BType_Imm Bit64)``)),(bconst64 0xC0000000))),
     blt((bden (bvar "SP_EL0" ``(BType_Imm Bit64)``)),(bconst64 0xD0000000))
     );



val bir_sqrt_pre_def = Define `bir_sqrt_pre =
^(band
  (bnot (bslt(get_x, bconst64 0)),
   bir_sp_ok ))
`;

val bir_sqrt_post_def = Define `bir_sqrt_post =
^(bandl [
      (bsle(bmult(get_y, get_y), get_x)),
      (bnot (bsle(bmult(bplus(get_y, bconst64 1), bplus(get_y, bconst64 1)), get_x))),
      bir_sp_ok
      ])`;


val original_loop_condition = (bsle(bmult(bplus(get_y, bconst64 1), bplus(get_y, bconst64 1)), get_x));
val bir_loop_condition =  beq ((bden (bvar "ProcState_N" ``BType_Bool``)),
                               (bden (bvar "ProcState_V" ``BType_Bool``)));


val bir_sqrt_I_def = Define `bir_sqrt_I =
^(bandl [
      (bsle(bmult(get_y, get_y), get_x)),
   (beq (original_loop_condition, bir_loop_condition)),
   bir_sp_ok
   ])
`;


(* contract one *)
(* from function entry (we avoid stack pointer operations) to cjmp *)
val bir_contract_1_pre_def = Define `bir_contract_1_pre =
 (bir_sqrt_pre)
`;
val bir_contract_1_post_def = Define `bir_contract_1_post =
 (bir_sqrt_I)
`;


(* contract two: loop body *)
(* from cjmp to cjmp *)
val bir_contract_2_pre_def = Define `bir_contract_2_pre =
^(band(``bir_sqrt_I``, bir_loop_condition))
`;
val bir_contract_2_post_def = Define `bir_contract_2_post =
 bir_sqrt_I
`;

(* contract three: loop exit *)
(* from cjmp to end of function except ret and sp operations *)
val bir_contract_3_pre_def = Define `bir_contract_3_pre =
^(band(``bir_sqrt_I``, bnot bir_loop_condition))
`;
val bir_contract_3_post_def = Define `bir_contract_3_post =
 bir_sqrt_post
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
