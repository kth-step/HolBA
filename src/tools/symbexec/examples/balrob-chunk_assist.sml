open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

(*
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_funcLib;
open bir_countw_simplificationLib;

open commonBalrobScriptLib;
*)

open bir_symbexec_driverLib;

(* motor_prep_input *)

val summaries   = [];
val entry_label = "motor_prep_input";
val syst_summary_motor_prep_input =
      create_func_summary n_dict bl_dict_ summaries entry_label;


(* motor_set_l *)

val summaries   = [syst_summary_motor_prep_input];
val entry_label = "motor_set_l";
val syst_summary_motor_set_l =
      create_func_summary n_dict bl_dict_ summaries entry_label;


(* motor_set_r *)

val summaries   = [syst_summary_motor_prep_input];
val entry_label = "motor_set_r";
val syst_summary_motor_set_r =
      create_func_summary n_dict bl_dict_ summaries entry_label;


(* motor_set *)

val summaries   = [syst_summary_motor_set_r, syst_summary_motor_set_l];(*@[syst_summary_motor_prep_input]*)
val entry_label = "motor_set";
val lbl_tm      = find_func_lbl_tm entry_label;
val syst_summary_motor_set_r =
      create_func_summary n_dict bl_dict_ summaries entry_label;
