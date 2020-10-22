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


(* __aeabi_fadd_c1 *)

val summaries   = [];
val lbl_tm      =  ``BL_Address (Imm32 0x257Aw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2598w)``];

val syst_summary___aeabi_fadd_c1 =
      obtain_summary n_dict bl_dict_ summaries lbl_tm end_lbl_tms;


(* __aeabi_fadd_c2 *)

val summaries   = [];
val lbl_tm      =  ``BL_Address (Imm32 0x25A0w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x25AEw)``];
val end_lbl_tms = [``BL_Address (Imm32 0x24C2w)``];

val syst_summary___aeabi_fadd_c2 =
      obtain_summary n_dict bl_dict_ summaries lbl_tm end_lbl_tms;


(* __aeabi_fadd_c3 *)

val summaries   = [];
val lbl_tm      =  ``BL_Address (Imm32 0x25D0w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x24C2w)``];

val syst_summary___aeabi_fadd_c3 =
      obtain_summary n_dict bl_dict_ summaries lbl_tm end_lbl_tms;


(* __aeabi_fadd *)

val summaries   = [syst_summary___clzsi2,
                   syst_summary___aeabi_fadd_c1,
                   syst_summary___aeabi_fadd_c2,
                   syst_summary___aeabi_fadd_c3];
val entry_label = "__aeabi_fadd";

val syst_summary___aeabi_fadd =
      create_func_summary n_dict bl_dict_ summaries entry_label;

(*
now this takes just about 2 minutes and we gain a little bit extra overapproximation on the countw
minmax = (58,168)
hopefully we can find suitable preconditions
*)
