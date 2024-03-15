open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open bin_rv_swapTheory;

open bir_program_transfTheory;

val _ = new_theory "se_swap";

(*
val _ = print_term (concl bin_rv_swap_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_rv_swap_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
Definition bprog_def:
  bprog = ^(bprog)
End
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x00w))``;
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm64 0x08w); bpc_index := 7|>``];
*)
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x14w))``];




(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
Definition riscv_vars_def:
  riscv_vars = APPEND (bmr_vars riscv_bmr) (bmr_temp_vars riscv_bmr)
End

Definition birenvtyl_riscv_def:
  birenvtyl_riscv = MAP BVarToPair riscv_vars
End
(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)



(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)

val mem_addrs_aligned_prog_disj_x10 = ``
  BExp_BinExp BIExp_And
    (BExp_Aligned Bit64 3 (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))))
    (BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual
        (BExp_Const (Imm64 0x1000w))
        (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))))
      (BExp_BinPred BIExp_LessThan
        (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0x100000000w)))
    )``;
val mem_addrs_aligned_prog_disj_x11 = ``
  BExp_BinExp BIExp_And
    (BExp_Aligned Bit64 3 (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))))
    (BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual
        (BExp_Const (Imm64 0x1000w))
        (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))))
      (BExp_BinPred BIExp_LessThan
        (BExp_Den (BVar "sy_x11" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0x100000000w)))
    )``;


val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl_riscv;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinExp BIExp_And ^mem_addrs_aligned_prog_disj_x10 ^mem_addrs_aligned_prog_disj_x11
|>``;
(* TODO: probably need this later in the path condition: 
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;

                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))

BExp_Const (Imm1 1w)

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

val timer = bir_miscLib.timer_start 0;
val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;

val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);



Theorem bin_rv_swap_analysis_thm = result


val _ = export_theory();
