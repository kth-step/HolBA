open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_sumLib;
open bir_symbexec_driverLib;


(* motor_prep_input *)

val entry_label = "motor_prep_input";
val lbl_tm      = find_func_lbl_tm entry_label;

val syst_start  = init_summary lbl_tm;
val systs_start = [syst_start];

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val syst_summary = merge_func lbl_tm systs_after;



(* motor_set_l *)

val (func_lbl_tm, _, _) = syst_summary;

val entry_label = "motor_set_l";
(*
"c1c" call
"c20" return
*)
val lbl_tm      = find_func_lbl_tm entry_label;

val syst_start  = init_summary lbl_tm;
val systs_start = [syst_start];

val stop_lbl_tms = [func_lbl_tm]; (*``BL_Address (Imm32 0xc1cw)``];*)
val systs_precall = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val systs_callinst = instantiate_summaries [syst_summary] systs_precall;

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val syst_summary_1 = merge_func lbl_tm systs_after;



(* motor_set_r *)

val (func_lbl_tm, _, _) = syst_summary;

val entry_label = "motor_set_r";
val lbl_tm      = find_func_lbl_tm entry_label;

val syst_start  = init_summary lbl_tm;
val systs_start = [syst_start];

val stop_lbl_tms = [func_lbl_tm];
val systs_precall = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val systs_callinst = instantiate_summaries [syst_summary] systs_precall;

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val syst_summary_2 = merge_func lbl_tm systs_after;


(* motor_set *)

val (func_lbl_tm_1, _, _) = syst_summary_1;
val (func_lbl_tm_2, _, _) = syst_summary_2;

val entry_label = "motor_set";
val lbl_tm      = find_func_lbl_tm entry_label;

val syst_start  = init_summary lbl_tm;
val systs_start = [syst_start];

val stop_lbl_tms = [func_lbl_tm_1, func_lbl_tm_2];
val systs_precall = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val systs_callinst = instantiate_summaries [syst_summary_1] systs_precall;
val systs_precall = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val systs_callinst = instantiate_summaries [syst_summary_2] systs_precall;

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val syst_summary_3 = merge_func lbl_tm systs_after;
