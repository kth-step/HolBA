(* Code specific for the example *)
open HolKernel Parse boolLib bossLib;
open HolBASimps;
open bir_backlifterTheory;
open bslSyntax;

val _ = new_theory "tutorial_bir_to_riscv";

(* TODO: Adapt this from ARMv8 to RISC-V *)

(* unsigned comparison *)
EVAL ``255w <=+ (0w:word8)``;
(* Signed comparison *)
EVAL ``255w <= (0w:word8)``;

(* TODO: why reg. names x10 instead of a0 in BIR *)

(* register add *)
(* x10 = a0 *)
(* x11 = a1 *)
(* x12 = a2 *)
(* x13 = a3 *)
(* unused x14 = a4 *)
(* x15 = a5 *)
val x_var = ``(m.c_gpr 0w 12w)``;
val y_var = ``(m.c_gpr 0w 13w)``;
val lx_var = ``(m.c_gpr 0w 10w)``;
val ly_var = ``(m.c_gpr 0w 11w)``;
val tmp_var = ``(m.c_gpr 02 15w)``;

(* Precondition implies verification from 0x24 to 0x4c *)
val riscv_add_reg_pre_def = Define `riscv_add_reg_pre m = (
  ((^x_var) >= 0w) /\
  ((^x_var = ^lx_var) /\ (^y_var = ^ly_var)))
`;
val riscv_add_reg_post_def = Define `riscv_add_reg_post m =
  ((^x_var+^y_var) = (^ly_var))
`;


(* BIR variables *)
val get_x = bden (bvar "x12" ``(BType_Imm Bit64)``);
val get_y = bden (bvar "x13" ``(BType_Imm Bit64)``);
val get_lx = bden (bvar "x10" ``(BType_Imm Bit64)``);
val get_ly = bden (bvar "x11" ``(BType_Imm Bit64)``);
val get_tmp = bden (bvar "x15" ``(BType_Imm Bit64)``);
val get_sp = bden (bvar "x2" ``(BType_Imm Bit64)``);
val get_r0 = bden (bvar "x1" ``(BType_Imm Bit64)``);

(* BIR constants *)
val get_v = bconst ``v:word64``;


val bir_add_reg_pre_def = Define `bir_add_reg_pre =
^(bandl [bnot (bslt(get_x, bconst64 0)),
         beq(get_lx, get_x),
         beq(get_ly, get_y)
        ]
)
`;

val bir_add_reg_post_def = Define `bir_add_reg_post =
 ^(beq (bplus(get_y, get_x), get_ly))`;


val original_add_reg_loop_condition =  (bnot (bsle(get_tmp, bconst64 0)));

(* Note: "BIR cjmp exits the loop is `C`, where C is the BIR jump condition*)
(* TODO: this in RISC-V *)
(*
val bir_add_reg_loop_condition =  bnot ``(BExp_BinExp BIExp_Or
                       (BExp_UnaryExp BIExp_Not
                          (BExp_BinPred BIExp_Equal
                             (BExp_Den (BVar "ProcState_N" BType_Bool))
                             (BExp_Den (BVar "ProcState_V" BType_Bool))))
                       (BExp_Den (BVar "ProcState_Z" BType_Bool)))``;

val bir_add_reg_loop_condition_def = Define `
 bir_add_reg_loop_condition = ^bir_add_reg_loop_condition`;
*)

val bir_add_reg_I_def = Define `bir_add_reg_I =
^(bandl [
   (beq (bplus(get_y, get_x), bplus(get_ly, get_lx))),
   (bsle(bconst64 0, get_lx))
   ])
`;


(* contract one *)
(* from function entry (we avoid stack pointer operations) to cjmp *)
val bir_add_reg_contract_1_pre_def = Define `bir_add_reg_contract_1_pre =
 (bir_add_reg_pre)
`;
val bir_add_reg_contract_1_post_def = Define `bir_add_reg_contract_1_post =
  bir_add_reg_I
`;


(* contract two: loop body *)
(* from loop body start to cjmp *)
val bir_add_reg_contract_2_pre_def = Define `bir_add_reg_contract_2_pre =
^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_2_post_def = Define `bir_add_reg_contract_2_post =
  bir_add_reg_I
`;

(* contract three: loop continue *)
(* from cjmp to loop body start *)
val bir_add_reg_contract_3_pre_def = Define `bir_add_reg_contract_3_pre =
^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_3_post_def = Define `bir_add_reg_contract_3_post =
  ^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
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
  beq(get_lx, get_v)
])
`;
val bir_add_reg_contract_2_post_variant_def = Define `bir_add_reg_contract_2_post_variant v  =
 ^(bandl[``bir_add_reg_I``,
  bslt(get_lx, get_v),
  (bsle(bconst64 0, get_lx))
])
`;

(* contract three: loop continue *)
(* from cjmp to loop body start *)
val bir_add_reg_contract_3_pre_variant_def = Define `bir_add_reg_contract_3_pre_variant v =
^(bandl[``bir_add_reg_I``, bir_add_reg_loop_condition, beq(get_lx, get_v)])
`;
val bir_add_reg_contract_3_post_variant_def = Define `bir_add_reg_contract_3_post_variant v =
 ^(bandl[``bir_add_reg_I``, bir_add_reg_loop_condition, beq(get_lx, get_v)])
`;


(* contract entry mem *)
(*
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
bir_add_reg_pre
`;
*)




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

FULL_SIMP_TAC std_ss [bir_pre_arm8_to_bir_def,
                      bir_add_reg_pre_is_bool_pred_thm] >>
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
Cases_on `a < 0w` >> (
  blastLib.FULL_BBLAST_TAC
)
);


val arm8_post_imp_bir_post_thm = store_thm("arm8_post_imp_bir_post_thm", 
  ``!(ls:bir_label_t -> bool).
    bir_post_bir_to_arm8 arm8_add_reg_post (\(l:bir_label_t). bir_add_reg_post) ls``,

FULL_SIMP_TAC std_ss [bir_post_bir_to_arm8_def] >>
REPEAT STRIP_TAC >>
UNDISCH_TAC ``bir_eval_exp bir_add_reg_post bs.bst_environ = SOME bir_val_true`` >>
SIMP_TAC std_ss [bir_add_reg_post_def] >>
SIMP_TAC std_ss arm_to_bir_exp_thms >>
EVAL_TAC >>
Q.ABBREV_TAC `a = ms.REG 2w` >>
Q.ABBREV_TAC `b = ms.REG 3w` >>
Q.ABBREV_TAC `c = ms.REG 4w` >>
Q.ABBREV_TAC `d = ms.REG 5w` >>
Cases_on `d + c = b` >> (
  blastLib.FULL_BBLAST_TAC
)
);




(*
EVAL ``arm8_wf_varset (bir_vars_of_exp bir_add_reg_contract_1_pre)``;
*)



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
