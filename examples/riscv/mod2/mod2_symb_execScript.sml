open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open mod2Theory;

val _ = new_theory "mod2_symb_exec";

val bprog_tm = (snd o dest_eq o concl) bir_mod2_prog_def;

(* ........................... *)

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x00w))``;

val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x4w))``];

(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)
Definition riscv_vars_def:
  riscv_vars = APPEND (bmr_vars riscv_bmr) (bmr_temp_vars riscv_bmr)
End

Definition mod2_prog_vars_def:
  mod2_prog_vars = [BVar "x10" (BType_Imm Bit64); BVar "x1" (BType_Imm Bit64)]
End

Theorem mod2_prog_vars_thm:
  set mod2_prog_vars = bir_vars_of_program (bir_mod2_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [bir_mod2_prog_def, mod2_prog_vars_def]
QED

Definition birenvtyl_riscv_def:
  birenvtyl_riscv = MAP BVarToPair (mod2_prog_vars)
End
(* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl_riscv;
  bsst_status   := BST_Running;
  bsst_pcond    :=
    BExp_BinPred
      BIExp_Equal
      (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
      (BExp_Const (Imm64 pre_x10))
|>``;

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

Theorem mod2_symb_analysis_thm = result

val _ = export_theory ();
