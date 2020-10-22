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

val summaries   = [];
val entry_label = "__clzsi2";
val syst_summary___clzsi2 =
      create_func_summary n_dict bl_dict_ summaries entry_label;


(* __aeabi_fadd *)

val summaries   = [syst_summary___clzsi2];
val entry_label = "__aeabi_fadd";

val syst_summary___aeabi_fadd =
      create_func_summary n_dict bl_dict_ summaries entry_label;
