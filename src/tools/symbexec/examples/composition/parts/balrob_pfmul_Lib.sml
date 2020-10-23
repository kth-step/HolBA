structure balrob_pfmul_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;


(* sum___aeabi_fmul_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2C40w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2BB2w)``];

val sum___aeabi_fmul_c1 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* sum___aeabi_fmul_c2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2C7Cw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2C86w)``];

val sum___aeabi_fmul_c2 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;

(*
(* sum___aeabi_fmul_c3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2CA4w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2CAEw)``];

val sum___aeabi_fmul_c3 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;
*)

(* sum___aeabi_fmul_c4 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2CB8w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2CC4w)``];

val sum___aeabi_fmul_c4 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* sum___aeabi_fmul_c5 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2CC6w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2CD0w)``];

val sum___aeabi_fmul_c5 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* sum___aeabi_fmul_c6 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2D40w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2C12w)``];

val sum___aeabi_fmul_c6 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* sum___aeabi_fmul_c7 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2CD2w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2C12w)``];

val sum___aeabi_fmul_c7 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


(* sum___aeabi_fmul_c8 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2D70w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2D7Cw)``];
val end_lbl_tms = [``BL_Address (Imm32 0x2C12w)``];

val sum___aeabi_fmul_c8 =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;






(* __aeabi_fmul *)

val sums        = [sum___clzsi2,
                   sum___aeabi_fmul_c1,
                   sum___aeabi_fmul_c2,
                   (*sum___aeabi_fmul_c3,*)
                   sum___aeabi_fmul_c4,
                   sum___aeabi_fmul_c5,
                   sum___aeabi_fmul_c6,
                   sum___aeabi_fmul_c7,
                   sum___aeabi_fmul_c8];
val entry_label = "__aeabi_fmul";

val sum___aeabi_fmul =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*

- uses jump table encoded in manually extracted cfg!

time to drive symbolic execution: 251.299s

min = 96w
max = 244w

*)


in (* outermost local *)

  val sum___aeabi_fmul = sum___aeabi_fmul;

end (* outermost local *)

end (* struct *)
