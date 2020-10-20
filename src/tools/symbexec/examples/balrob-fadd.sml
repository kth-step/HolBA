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

(*
(* Analysis *)
*)

(*
val i = 1;
val _ = List.map (fn i =>
  if mem i [1,5,9,13,17,22,26] then () else
  let
    val _ = print ("processing " ^ (Int.toString i) ^ "\n");
    val syst_abc = List.nth (systs_precall, i);
    val systs_callinst = instantiate_func [syst_abc] syst_summary;
(*
    val syst = hd systs_callinst;

    val exp = ``BExp_Align Bit32 1 (BExp_Den (BVar "LR" (BType_Imm Bit32)))``;
    bir_countw_simplificationLib.eval_exp_in_syst exp syst_abc2
    expand_bv_in_syst ``BVar "LR" (BType_Imm Bit32)`` syst
*)
    val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;
  in ()
  end) (List.tabulate (length systs_precall, I)); 
*)

(*
val (some_systs, _) = List.partition bir_symbexec_stateLib.state_is_running systs_precall;
*)

*)

val systs_callinst = instantiate_func systs_precall syst_summary;

(*
val stop_lbl_tms = find_func_ends n_dict entry_label;
val stop_lbl_tms = [func_lbl_tm]@(find_func_ends n_dict entry_label);
*)

val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val final_lbl_tms_ = List.map bir_symbexec_stateLib.SYST_get_pc systs_after;
val final_lbl_tms = Redblackset.listItems (Redblackset.fromList Term.compare final_lbl_tms_);

val syst_summary_1 = merge_func lbl_tm systs_after;

(*
progress info
count paths (have a traversal function for what-if-we-try-experiments)
run without function instantiation for comparison (write down numbers to see effects of optimizations)
some approach to "collapse" components?
- cutting/instantiation experiment, based on inspected CFG
- if this works and has positive effect, automatically find cutting points by trying each branch and see if it is possible to find common merge point?
*)
