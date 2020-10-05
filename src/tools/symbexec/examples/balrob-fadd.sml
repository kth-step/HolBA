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


(* __clzsi2 *)

val entry_label = "__clzsi2";
val (lbl_tm, syst_start) = init_func entry_label;
val systs_start = [syst_start];

val stop_lbl_tms = find_func_ends n_dict entry_label;
val systs_after = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val syst_summary = merge_func lbl_tm systs_after;


(* __aeabi_fadd *)

val (func_lbl_tm, _, _) = syst_summary;

val entry_label = "__aeabi_fadd";
val (lbl_tm, syst_start) = init_func entry_label;
val systs_start = [syst_start];

val stop_lbl_tms = [func_lbl_tm]@(find_func_ends n_dict entry_label);
val systs_precall = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

(*
val systs_callinst = instantiate_func systs_precall syst_summary;

val stop_lbl_tms = find_func_ends n_dict entry_label;
(*
val stop_lbl_tms = [func_lbl_tm]@(find_func_ends n_dict entry_label);
*)
val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val syst_summary_1 = merge_func lbl_tm systs_after;
*)
