structure balrob_pfsub_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;

val ffun_offset = 0x10000e7c - 0x2DEC (* fadd: 0xFFFDD94 *);
fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);
val _ = print "fsub offset is: 0x";
val _ = print (Arbnum.toHexString (Arbnum.fromInt ffun_offset));
val _ = print "\n";

(*
(n2w ^(int_to_numterm (ffun_offset + 
)))
*)


(* sum___aeabi_fsub_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2DEC))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2DF4))))``];
val usage = (0, 13);

val sum___aeabi_fsub_c1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c1 "sum___aeabi_fsub_c1";


(* sum___aeabi_fsub_c2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E60))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E72))))``];
val usage = (0, 22);

val sum___aeabi_fsub_c2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c2 "sum___aeabi_fsub_c2";


(* sum___aeabi_fsub_c3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2EC6))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2EDC))))``];
val usage = (0, 11);

val sum___aeabi_fsub_c3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c3 "sum___aeabi_fsub_c3";


(* sum___aeabi_fsub_c4 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x3082))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x3094))))``];
val usage = (0, 9);

val sum___aeabi_fsub_c4 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c4 "sum___aeabi_fsub_c4";


(* sum___aeabi_fsub_c5 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2F86))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2F9A))))``];
val usage = (0, 11);

val sum___aeabi_fsub_c5 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c5 "sum___aeabi_fsub_c5";


(* sum___aeabi_fsub_c6 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x30CC))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x30D8))))``];
val usage = (0, 6);

val sum___aeabi_fsub_c6 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c6 "sum___aeabi_fsub_c6";


(* sum___aeabi_fsub_c7 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E5A))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E5E))))``];
val usage = (0, 3);

val sum___aeabi_fsub_c7 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fsub_c7 "sum___aeabi_fsub_c7";


(* sum___aeabi_fsub_c8 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E2C))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2E4A))))``];
val usage = (0, 16);

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
