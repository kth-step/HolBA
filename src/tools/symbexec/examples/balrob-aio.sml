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

(*
(* motor_set_l *)

val entry_label = "motor_set_l";
val (lbl_tm, syst_start) = init_func entry_label;
val systs_start = [syst_start];

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val syst_summary = merge_func lbl_tm systs_after;
*)


(* motor_set *)

val entry_label = "motor_set";
val lbl_tm      = find_func_lbl_tm entry_label;

val syst_start  = init_summary lbl_tm;
val systs_start = [syst_start];

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val syst_summary = merge_func lbl_tm systs_after;

