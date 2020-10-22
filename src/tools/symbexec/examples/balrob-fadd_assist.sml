open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_driverLib;


(* __clzsi2 *)

val sums        = [];
val entry_label = "__clzsi2";
val sum___clzsi2 =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* __aeabi_fadd_c1 *)

val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x257Aw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2598w)``];

val sum___aeabi_fadd_c1 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* __aeabi_fadd_c2 *)

val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x25A0w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x25AEw)``];
val end_lbl_tms = [``BL_Address (Imm32 0x24C2w)``];

val sum___aeabi_fadd_c2 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* __aeabi_fadd_c3 *)

val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x25D0w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x24C2w)``];

val sum___aeabi_fadd_c3 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* __aeabi_fadd *)

val sums        = [sum___clzsi2,
                   sum___aeabi_fadd_c1,
                   sum___aeabi_fadd_c2,
                   sum___aeabi_fadd_c3];
val entry_label = "__aeabi_fadd";

val sum___aeabi_fadd =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
now this takes just about 2 minutes and we gain a little bit extra overapproximation on the countw
minmax = (58,168)
hopefully we can find suitable preconditions
*)
