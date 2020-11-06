structure balrob_pfsub_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;


(* sum___aeabi_fsub_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2DECw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2DF4w)``];
val usage = (0, 20);

val sum___aeabi_fsub_c1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c1 "sum___aeabi_fsub_c1";


(* sum___aeabi_fsub_c2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2E60w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2E72w)``];
val usage = (0, 20);

val sum___aeabi_fsub_c2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c2 "sum___aeabi_fsub_c2";


(* sum___aeabi_fsub_c3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2EC6w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2EDCw)``];
val usage = (0, 20);

val sum___aeabi_fsub_c3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c3 "sum___aeabi_fsub_c3";


(* sum___aeabi_fsub_c4 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x3082w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x3094w)``];
val usage = (0, 20);

val sum___aeabi_fsub_c4 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c4 "sum___aeabi_fsub_c4";


(* sum___aeabi_fsub_c5 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2F86w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2F9Aw)``];
val usage = (0, 20);

val sum___aeabi_fsub_c5 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c5 "sum___aeabi_fsub_c5";


(* sum___aeabi_fsub_c6 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x30CCw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x30D8w)``];
val usage = (0, 20);

val sum___aeabi_fsub_c6 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c6 "sum___aeabi_fsub_c6";


(* sum___aeabi_fsub_c7 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2E5Aw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2E5Ew)``];
val usage = (0, 20);

val sum___aeabi_fsub_c7 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c7 "sum___aeabi_fsub_c7";


(* sum___aeabi_fsub_c8 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2E2Cw)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2E4Aw)``];
val usage = (0, 20);

val sum___aeabi_fsub_c8 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c8 "sum___aeabi_fsub_c8";

(* __aeabi_fsub *)

val sums        = [sum___clzsi2,
                   sum___aeabi_fsub_c1,
                   sum___aeabi_fsub_c2,
                   sum___aeabi_fsub_c3,
                   sum___aeabi_fsub_c4,
                   sum___aeabi_fsub_c5,
                   sum___aeabi_fsub_c6,
                   sum___aeabi_fsub_c7,
                   sum___aeabi_fsub_c8];
val entry_label = "__aeabi_fsub";

val sum___aeabi_fsub =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
only sum___clzsi2
----------------------

part1
number of paths found: 35766
number of "no assert failed" paths found: 1929
number of feasible paths found: 129


part2
number of paths found: 8520
number of "no assert failed" paths found: 468
number of feasible paths found: 86


altogether
time to drive symbolic execution: 880.591s

min = 69w
max = 172w


with 8 merged chunks
---------------------
time to drive symbolic execution: 88.985s

min = 69w
max = 187w

*)


in (* outermost local *)

  val sum___aeabi_fsub = sum___aeabi_fsub;

end (* outermost local *)

end (* struct *)
