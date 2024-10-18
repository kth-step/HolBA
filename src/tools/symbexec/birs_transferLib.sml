structure birs_transferLib =
struct

local

  open HolKernel Parse boolLib bossLib;

(*
  open birs_stepLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open birs_composeLib;
open birs_auxTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
*)

  (* error handling *)
  val libname = "birs_transferLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

fun prepare_transfer birenvtyl_def pcond_inst bpre symb_analysis_thm =
  let
    val prog_env_thm = birs_driveLib.gen_birs_env_thm birenvtyl_def;
    val prog_pcond_thm = birs_driveLib.gen_birs_pcond_thm birenvtyl_def bpre;
    val pcond_tm = (rhs o concl) prog_pcond_thm;

    (* first remove generic path condition symbol *)
    open birs_instantiationLib;
    open birs_utilsLib;
    val specd_symb_analysis_thm = birs_sound_symb_inst_RULE [(birs_driveLib.pcond_gen_symb, pcond_inst)] symb_analysis_thm;
    val pcond_symb_analysis_thm = birs_sys_pcond_RULE pcond_tm specd_symb_analysis_thm;

    (* then fix the initial state *)
    val fixed_symb_analysis_thm = CONV_RULE (birs_sys_CONV (REWRITE_CONV [GSYM prog_env_thm])) pcond_symb_analysis_thm;
    val _ = print "\n\n";
    val _ = print_thm prog_pcond_thm;
    val _ = print "\n\n";
    val _ = print_thm fixed_symb_analysis_thm;
    val _ = print "\n\n";
  in
    (prog_pcond_thm, fixed_symb_analysis_thm)
  end;



end (* local *)

end (* struct *)
