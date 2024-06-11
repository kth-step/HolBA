structure bir_symbLib :> bir_symbLib =
struct

open Abbrev;

local
  open HolKernel Parse boolLib bossLib;
  open bitTheory;
  open birs_stepLib;
  open birs_composeLib;
  open birs_driveLib;
  open birs_auxTheory;
in

fun mem_addrs_prog_disj_bir_tm rn = ``BExp_BinExp BIExp_And
 (BExp_BinPred BIExp_LessOrEqual
  (BExp_Const (Imm64 0x1000w))
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64))))
 (BExp_BinPred BIExp_LessThan
  (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
  (BExp_Const (Imm64 0x100000000w)))``;

fun mem_addrs_aligned_prog_disj_bir_tm rn = ``BExp_BinExp BIExp_And
  (BExp_Aligned Bit64 3 (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64))))
  (^(mem_addrs_prog_disj_bir_tm rn))``;

fun mem_addrs_aligned_prog_disj_riscv_tm vn =
 let
   val var_tm = mk_var (vn, wordsSyntax.mk_int_word_type 64)
 in
  ``^var_tm && 7w = 0w /\ 0x1000w <=+ ^var_tm /\ ^var_tm <+ 0x100000000w``
 end;

fun pre_vals_reg_bir_tm rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
      (BExp_Const (Imm64 `@ [QUOTE fv] @`)))
`);

fun pre_vals_mem_reg_bir_tm mn rn fv = Parse.Term (`
    (BExp_BinPred
      BIExp_Equal
      (BExp_Load
        (BExp_Den (BVar ^(stringSyntax.fromMLstring mn) (BType_Mem Bit64 Bit8)))
        (BExp_Den (BVar ^(stringSyntax.fromMLstring rn) (BType_Imm Bit64)))
        BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 `@ [QUOTE fv] @`)))
`);

fun pre_vals_bir_tm mn rn fvr fvmd =
 bslSyntax.band (pre_vals_reg_bir_tm rn fvr, pre_vals_mem_reg_bir_tm mn rn fvmd);

fun bir_symb_analysis bprog_tm birs_state_init_lbl
  birs_end_lbls bprog_envtyl birs_pcond =
 let
   val birs_state_init = ``<|
     bsst_pc       := ^birs_state_init_lbl;
     bsst_environ  := bir_senv_GEN_list ^bprog_envtyl;
     bsst_status   := BST_Running;
     bsst_pcond    := ^birs_pcond
   |>``;
   val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
   val birs_rule_STEP_fun_spec =
     (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o
      birs_rule_tryjustassert_fun true o birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm);
   (* now the composition *)
   val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
   val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
   val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
   (* and also the sequential composition *)
   val birs_rule_STEP_SEQ_thm = MATCH_MP
    birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm
    (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_STEP_SEQ_fun_spec =
    birs_rule_STEP_SEQ_fun (birs_rule_SUBST_thm, birs_rule_STEP_SEQ_thm);
   val _ = print "now reducing it to one sound structure\n";
   val timer = bir_miscLib.timer_start 0;
   val result = exec_until
     (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec)
     single_step_A_thm birs_end_lbls;
   val _ = bir_miscLib.timer_stop
    (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;
 in
   result
 end (* let *)

end (* local *)

end (* structure *)
