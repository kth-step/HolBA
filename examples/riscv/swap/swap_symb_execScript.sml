open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open swapTheory;

val _ = new_theory "swap_symb_exec";

(* ........................... *)

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x00w))``;

val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x14w))``];

val mem_addrs_aligned_prog_disj_x10 = ``BExp_BinExp BIExp_And
    (BExp_Aligned Bit64 3 (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))))
    (BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual
        (BExp_Const (Imm64 0x1000w))
        (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))))
      (BExp_BinPred BIExp_LessThan
        (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0x100000000w))))``;

val mem_addrs_aligned_prog_disj_x11 = ``BExp_BinExp BIExp_And
    (BExp_Aligned Bit64 3 (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))))
    (BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual
        (BExp_Const (Imm64 0x1000w))
        (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))))
      (BExp_BinPred BIExp_LessThan
        (BExp_Den (BVar "sy_x11" (BType_Imm Bit64)))
        (BExp_Const (Imm64 0x100000000w))))``;

val birs_pcond = ``BExp_BinExp
 BIExp_And
  ^mem_addrs_aligned_prog_disj_x10
  ^mem_addrs_aligned_prog_disj_x11``;

(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

Definition swap_prog_vars_def:
  swap_prog_vars = [
    BVar "MEM8" (BType_Mem Bit64 Bit8);
    BVar "x15" (BType_Imm Bit64);
    BVar "x14" (BType_Imm Bit64);
    BVar "x11" (BType_Imm Bit64);
    BVar "x10" (BType_Imm Bit64);
    BVar "x1" (BType_Imm Bit64)
  ]
End

Theorem swap_prog_vars_thm:
  set swap_prog_vars = bir_vars_of_program (bir_swap_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_swap_prog_def, swap_prog_vars_def] >>
  EVAL_TAC
QED

Definition swap_birenvtyl_def:
  swap_birenvtyl = MAP BVarToPair swap_prog_vars
End

(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list swap_birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := ^birs_pcond
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

val bprog_tm = (snd o dest_eq o concl) bir_swap_prog_def;

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

Theorem swap_symb_analysis_thm = result

val _ = export_theory ();
