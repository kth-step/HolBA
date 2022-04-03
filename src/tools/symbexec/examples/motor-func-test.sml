open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open bin_motor_funcTheory;

(*
val _ = print_term (concl bin_motor_func_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_motor_func_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb08w))``;
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm32 0xb08w); bpc_index := 7|>``];
*)
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb0aw))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb12w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb20w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb22w))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb2ew))``];
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0xb46w))``];


(* ---------------------------------------------------------------------------------------------------------------- *)
(* TODO: the following is copied from transfer-test script (MODIFIED FOR TEMP VARS) *)
(* ---------------------------------------------------------------------------------------------------------------- *)
val m0_mod_vars_def = Define `
    m0_mod_vars = APPEND (bmr_vars (m0_mod_bmr (T,T))) (bmr_temp_vars (m0_mod_bmr (T,T)))
`;

val m0_mod_vars_thm = store_thm(
   "m0_mod_vars_thm", ``
!ef sel.
  m0_mod_vars = APPEND (bmr_vars (m0_mod_bmr (ef,sel))) (bmr_temp_vars (m0_mod_bmr (ef,sel)))
``,
  METIS_TAC [m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL, bir_lifting_machinesTheory.m0_mod_bmr_temp_vars_EVAL]
);

val birenvtyl_def = Define `
    birenvtyl = MAP BVarToPair m0_mod_vars
`;
(*    birenvtyl = [("R7", BType_Imm Bit32); ("SP_process", BType_Imm Bit32); ("countw", BType_Imm Bit64)]*)
(*
bir_lifting_machinesTheory.m0_mod_REGS_lifted_imms_LIST_def
m0_mod_REGS_lifted_imms_LIST
m0_mod_lifted_mem
bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL
*)
val birenvtyl_EVAL_thm = save_thm(
   "birenvtyl_EVAL_thm",
  (REWRITE_CONV [birenvtyl_def, m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL, bir_lifting_machinesTheory.m0_mod_bmr_temp_vars_EVAL] THENC EVAL) ``birenvtyl``
);
(* ---------------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------------------- *)


(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)


val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
|>``;
(* TODO: probably need this later in the path condition: 
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;
 *)
(* ........................... *)

val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
val birs_rule_STEP_fun_spec = (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o birs_rule_tryjustassert_fun true o birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm);
(* now the composition *)
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
(* ........................... *)


val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
(* ........................... *)



(* and also the sequential composition *)
val birs_rule_STEP_SEQ_thm = MATCH_MP birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_SEQ_fun_spec = birs_rule_STEP_SEQ_fun (birs_rule_SUBST_thm, birs_rule_STEP_SEQ_thm);
(* ........................... *)

(*
val tree = build_tree (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = print "done building the tree\n";
*)

val _ = print "now reducing it to one sound structure\n";
val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;

val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);
