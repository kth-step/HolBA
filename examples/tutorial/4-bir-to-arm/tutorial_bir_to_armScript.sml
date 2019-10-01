(* Code specific for the example *)
open HolKernel Parse boolLib bossLib;
open bir_expSimps;
open tutorial_bir_to_armSupportTheory;
open bslSyntax;

val _ = new_theory "tutorial_bir_to_arm";

(* unsigned comparison *)
EVAL ``255w <=+ (0w:word8)``;
(* Signed comparison *)
EVAL ``255w <= (0w:word8)``;

(* register add *)
val y_var = ``(m.REG 5w)``;
val x_var = ``(m.REG 4w)``;
val ly_var = ``(m.REG 3w)``;
val lx_var = ``(m.REG 2w)``;

val arm8_add_reg_pre_def = Define `arm8_add_reg_pre m =
  ((^x_var) >= 0w) /\
  ((^x_var = ^lx_var) /\ (^y_var = ^ly_var))
`;
val arm8_add_reg_post_def = Define `arm8_add_reg_post m =
  ((^x_var+^y_var) = (^ly_var))
`;

val get_y = bden (bvar "R5" ``(BType_Imm Bit64)``);
val get_x = bden (bvar "R4" ``(BType_Imm Bit64)``);
val get_ly = bden (bvar "R3" ``(BType_Imm Bit64)``);
val get_lx = bden (bvar "R2" ``(BType_Imm Bit64)``);
val get_sp = bden (bvar "SP_EL0" ``(BType_Imm Bit64)``);
val get_r0 = bden (bvar "R0" ``(BType_Imm Bit64)``);


val bir_add_reg_pre_def = Define `bir_add_reg_pre =
^(bandl[
        bnot (bslt(get_x, bconst64 0)),
        beq(get_lx, get_x),
         beq(get_ly, get_y)
         ]
)
`;

val bir_add_reg_post_def = Define `bir_add_reg_post =
(\(l:bir_label_t). (^(beq (bplus(get_y, get_x), get_ly))))`;


val original_add_reg_loop_condition =  (bnot (bsle(get_lx, bconst64 0)));

(* Note: "BIR cjmp exits the loop is `C`, where C is the BIR ump condition*)
val bir_add_reg_loop_condition =  bnot ``(BExp_BinExp BIExp_Or
                       (BExp_UnaryExp BIExp_Not
                          (BExp_BinPred BIExp_Equal
                             (BExp_Den (BVar "ProcState_N" BType_Bool))
                             (BExp_Den (BVar "ProcState_V" BType_Bool))))
                       (BExp_Den (BVar "ProcState_Z" BType_Bool)))``;


val bir_add_reg_loop_condition_def = Define `
 bir_add_reg_loop_condition = ^bir_add_reg_loop_condition`;

val bir_add_reg_I_def = Define `bir_add_reg_I =
^(bandl [
   (beq (bplus(get_y, get_x), bplus(get_ly, get_lx))),
   (bsle(bconst64 0, get_lx)),
   (beq (original_add_reg_loop_condition, bir_add_reg_loop_condition))
   ])
`;


(* contract one *)
(* from function entry (we avoid stack pointer operations) to cjmp *)
val bir_add_reg_contract_1_pre_def = Define `bir_add_reg_contract_1_pre =
 (bir_add_reg_pre)
`;
val bir_add_reg_contract_1_post_def = Define `bir_add_reg_contract_1_post =
 (\(l:bir_label_t). (bir_add_reg_I))
`;


(* contract two: loop body *)
(* from loop body start to cjmp *)
val bir_add_reg_contract_2_pre_def = Define `bir_add_reg_contract_2_pre =
^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_2_post_def = Define `bir_add_reg_contract_2_post =
 (\(l:bir_label_t). bir_add_reg_I)
`;

(* contract three: loop continue *)
(* from cjmp to loop body start *)
val bir_add_reg_contract_3_pre_def = Define `bir_add_reg_contract_3_pre =
^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_3_post_def = Define `bir_add_reg_contract_3_post =
 (\(l:bir_label_t). ^(band(``bir_add_reg_I``, bir_add_reg_loop_condition)))
`;

(* contract four: loop exit *)
(* from cjmp to end of function except ret and sp operations *)
val bir_add_reg_contract_4_pre_def = Define `bir_add_reg_contract_4_pre =
^(band(``bir_add_reg_I``, bnot bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_4_post_def = Define `bir_add_reg_contract_4_post =
 bir_add_reg_post
`;





(* VARIANT *)
(* contract two: loop body with variant *)
(* from loop body start to cjmp *)
val bir_add_reg_contract_2_pre_variant_def = Define `bir_add_reg_contract_2_pre_variant v =
^(bandl[``bir_add_reg_I``, bir_add_reg_loop_condition,
  beq(get_lx, ``(BExp_Const (Imm64 v))``)
])
`;
val bir_add_reg_contract_2_post_variant_def = Define `bir_add_reg_contract_2_post_variant v  =
 (\(l:bir_label_t). ^(bandl[``bir_add_reg_I``,
  bnot(bsle(``(BExp_Const (Imm64 v))``, get_lx)),
  (bsle(bconst64 0, get_lx))
]))
`;
(* contract three: loop continue *)
(* from cjmp to loop body start *)
val bir_add_reg_contract_3_pre_variant_def = Define `bir_add_reg_contract_3_pre_variant v =
^(bandl[``bir_add_reg_I``, bir_add_reg_loop_condition, beq(get_lx, ``(BExp_Const (Imm64 v))``)])
`;
val bir_add_reg_contract_3_post_variant_def = Define `bir_add_reg_contract_3_post_variant v =
 (\(l:bir_label_t). ^(bandl[``bir_add_reg_I``, bir_add_reg_loop_condition, beq(get_lx, ``(BExp_Const (Imm64 v))``)]))
`;


(* contract entry mem *)
val bir_add_reg_contract_0_pre_def = Define `bir_add_reg_contract_0_pre =
^(bandl[
        bnot (bslt(get_r0, bconst64 0)),
        ``(BExp_Aligned Bit64 3
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))))``,
        bnot(blt(get_sp, bconst64 0xC0000000)),
        blt(get_sp, bconst64 0xD0000000)
         ]
)
`;

val bir_add_reg_contract_0_post_def = Define `bir_add_reg_contract_0_post =
(\(l:bir_label_t). bir_add_reg_pre)
`;




(* Here we prove that the contracts transfer properties between the two models *)
(* We first show that the bir contract is a boolean property *)
val bir_add_reg_pre_is_bool_pred_thm = prove(
  ``bir_is_bool_exp bir_add_reg_pre``,
  FULL_SIMP_TAC (std_ss++bir_is_bool_ss) [bir_add_reg_pre_def]
);

val arm_to_bir_exp_thms = (((CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE) bir_lifting_machinesTheory.arm8_bmr_rel_EVAL) @
  [bir_expTheory.bir_eval_bin_exp_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] @
  [bir_expTheory.bir_eval_bin_pred_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def,
         bir_immTheory.bool2b_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS, bir_valuesTheory.BType_Bool_def ] @
  [bir_expTheory.bir_eval_exp_def] @ [bir_expTheory.bir_eval_unary_exp_REWRS,
  bir_exp_immTheory.bir_unary_exp_GET_OPER_def,  bir_exp_immTheory.bir_unary_exp_REWRS] @
  [bool2w_def, bir_bool_expTheory.bir_val_true_def]);


(* Then we show that the arm precondition entails the bir precondition *)
val arm8_pre_imp_bir_pre_thm = store_thm("arm8_pre_imp_bir_pre_thm", 
  ``bir_pre_arm8_to_bir arm8_add_reg_pre bir_add_reg_pre``,

FULL_SIMP_TAC std_ss [bir_pre_arm8_to_bir_def, bir_add_reg_pre_is_bool_pred_thm] >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_add_reg_pre_def] >>
SIMP_TAC std_ss arm_to_bir_exp_thms >>
EVAL_TAC >>
UNDISCH_TAC ``arm8_add_reg_pre ms`` >>
FULL_SIMP_TAC std_ss [arm8_add_reg_pre_def] >>
Q.ABBREV_TAC `a = ms.REG 2w` >>
Q.ABBREV_TAC `b = ms.REG 3w` >>
Q.ABBREV_TAC `c = ms.REG 4w` >>
Q.ABBREV_TAC `d = ms.REG 5w` >>
(fn (asl,goal) => ASSUME_TAC (HolSmtLib.Z3_ORACLE_PROVE  goal)(asl,goal)) >>
FULL_SIMP_TAC std_ss []
);


val arm8_post_imp_bir_post_thm = store_thm("arm8_post_imp_bir_post_thm", 
  ``!(ls:bir_label_t -> bool).
    bir_post_bir_to_arm8 arm8_add_reg_post bir_add_reg_post ls``,

FULL_SIMP_TAC std_ss [bir_post_bir_to_arm8_def] >>
REPEAT STRIP_TAC >>
UNDISCH_TAC ``bir_eval_exp (bir_add_reg_post l) bs.bst_environ = SOME bir_val_true`` >>
SIMP_TAC std_ss [bir_add_reg_post_def] >>
SIMP_TAC std_ss arm_to_bir_exp_thms >>
EVAL_TAC >>
Q.ABBREV_TAC `a = ms.REG 2w` >>
Q.ABBREV_TAC `b = ms.REG 3w` >>
Q.ABBREV_TAC `c = ms.REG 4w` >>
Q.ABBREV_TAC `d = ms.REG 5w` >>
(fn (asl,goal) => ASSUME_TAC (HolSmtLib.Z3_ORACLE_PROVE goal)(asl,goal)) >>
FULL_SIMP_TAC std_ss []
);





EVAL ``arm8_wf_varset (bir_vars_of_exp bir_add_reg_contract_1_pre)``;




(* old proofs *)


(*
open bir_subprogramLib;
open bir_programSyntax;

val (_, bir_prog) =
         dest_comb
           (concl examples_arm8_program_THM);

val tutorial_prog_def = Define `tutorial_prog = ^bir_prog`;

EVAL ``arm8_wf_varset (bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_program tutorial_prog)``;
*)

val _ = export_theory();
