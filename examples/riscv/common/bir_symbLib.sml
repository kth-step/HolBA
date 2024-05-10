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

fun bir_symb_analysis bprog_tm
 birs_state_init_lbl birs_stop_lbls
 bprog_envtyl birs_pcond =
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
     single_step_A_thm birs_stop_lbls;
   val _ = bir_miscLib.timer_stop
    (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;
 in
   result
 end (* let *)

end (* local *)

end (* structure *)
