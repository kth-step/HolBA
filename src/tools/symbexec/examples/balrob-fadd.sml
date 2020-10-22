open HolKernel Parse

open bir_miscLib;

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

val (num_nodetravs, num_pahts, num_paths_wasserts) =
  bir_symbexec_hypoLib.collect_trav_info bl_dict_ n_dict [lbl_tm] stop_lbl_tms;
val _ = print ("number of cfg nodes to traverse: " ^ (Int.toString (num_nodetravs)) ^ "\n");
val _ = print ("number of paths to traverse: " ^ (Int.toString (num_pahts)) ^ "\n");
val _ = print ("number of paths with assert: " ^ (Int.toString (num_paths_wasserts)) ^ "\n");

val systs_after = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;

val syst_summary = merge_func lbl_tm systs_after;

(* __aeabi_fadd *)

val (func_lbl_tm, _, _) = syst_summary;

val entry_label = "__aeabi_fadd";
val (lbl_tm, syst_start) = init_func entry_label;
val systs_start = [syst_start];

val stop_lbl_tms = [func_lbl_tm]@(find_func_ends n_dict entry_label);

val timer_meas = timer_start 1;
val (num_nodetravs, num_pahts, num_paths_wasserts) =
  bir_symbexec_hypoLib.collect_trav_info bl_dict_ n_dict [lbl_tm] stop_lbl_tms;
val _ = print ("number of cfg nodes to traverse: " ^ (Int.toString (num_nodetravs)) ^ "\n");
val _ = print ("number of paths to traverse: " ^ (Int.toString (num_pahts)) ^ "\n");
val _ = print ("number of paths with assert: " ^ (Int.toString (num_paths_wasserts)) ^ "\n");
val _ = timer_stop (fn s => print("time to collect traversal info: " ^ s ^ "\n")) timer_meas;

val timer_meas = timer_start 1;
val systs_precall = drive_to n_dict bl_dict_ systs_start stop_lbl_tms;
val _ = timer_stop (fn s => print("time to drive symbolic execution: " ^ s ^ "\n")) timer_meas;

(* Analysis *)
(* ================================================================ *)
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


(* continue after the call *)
(* ================================================================ *)
(*
val systs_callinst = instantiate_func systs_precall syst_summary;

(*
val stop_lbl_tms = find_func_ends n_dict entry_label;
val stop_lbl_tms = [func_lbl_tm]@(find_func_ends n_dict entry_label);
*)

val systs_after = drive_to n_dict bl_dict_ systs_callinst stop_lbl_tms;

val final_lbl_tms_ = List.map bir_symbexec_stateLib.SYST_get_pc systs_after;
val final_lbl_tms = Redblackset.listItems (Redblackset.fromList Term.compare final_lbl_tms_);

val syst_summary_1 = merge_func lbl_tm systs_after;
*)


(* notes *)
(* ================================================================ *)
(*
TODO:
count paths (have a traversal function for what-if-we-try-experiments)
some approach to "collapse" components?
- cutting/instantiation experiment, based on inspected CFG
- if this works and has positive effect, automatically find cutting points by trying each branch and see if it is possible to find common merge point?

no point to do this with fadd:
- run without function instantiation for comparison (write down numbers to see effects of optimizations)
- expected runtime 4h, but no difference in exectime due to constant execution time of subfunction


*)

(*

results:
(consider cut before the function call, which involves feasibility check, for state counting)

key - a states in total,
    - b are not assert failed/still running/reached the end,
    - c are feasible,
    - x - min_countw,
    - y - max_countw.

- plain running: about 25min, a=21000::48000, b=1129::2781, c=129::297, x=58, y=161.


(* why are these numbers so different?
- ite assignment branching and merging at cjmp complicates this kind of validation
- now hypoLib is fixed to underestimate the branching - does not account for lsls instructions for example that assign ite exp, which is not used for countw and not used for cjmp, not what we actually want
*)
time for fun2 until call (collect travinfo, drive symbexec):
187s
395s

count nodes on all paths (fun1, fun2 until call):
61
9705 (here we probably visit more nodes)

number of paths (fun1, fun2 until call):
8
580 (actually it's 1129?!)

number of paths including assert (fun1, fun2 until call)
69
10857 (actually it's 20937)

*)
