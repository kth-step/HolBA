structure balrob_pfmul_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;

val ffun_offset = 0x10000c28 - 0x2C40 (* fadd: 0xFFFDD94 *);
fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);
val _ = print "fmul offset is: 0x";
val _ = print (Arbnum.toHexString (Arbnum.fromInt ffun_offset));
val _ = print "\n";

(*
(n2w ^(int_to_numterm (ffun_offset + 
)))
*)


(* sum___aeabi_fmul_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C40))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2BB2))))``];
val usage = (0, 11);

val sum___aeabi_fmul_c1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c1 "sum___aeabi_fmul_c1";


(* sum___aeabi_fmul_c2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C7C))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C86))))``];
val usage = (0, 5);

val sum___aeabi_fmul_c2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c2 "sum___aeabi_fmul_c2";

(*
(* sum___aeabi_fmul_c3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2CA4w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2CAEw)``];
val usage = (0, 20);

val sum___aeabi_fmul_c3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c3 "sum___aeabi_fmul_c3";
*)

(* sum___aeabi_fmul_c4 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2CB8))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2CC4))))``];
val usage = (0, 7);

val sum___aeabi_fmul_c4 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c4 "sum___aeabi_fmul_c4";


(* sum___aeabi_fmul_c5 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2CC6))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2CD0))))``];
val usage = (0, 7);

val sum___aeabi_fmul_c5 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c5 "sum___aeabi_fmul_c5";


(* sum___aeabi_fmul_c6 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2D40))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C12))))``];
val usage = (0, 16);

val sum___aeabi_fmul_c6 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c6 "sum___aeabi_fmul_c6";


(* sum___aeabi_fmul_c7 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2CD2))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C12))))``];
val usage = (0, 8);

val sum___aeabi_fmul_c7 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c7 "sum___aeabi_fmul_c7";


(* sum___aeabi_fmul_c8 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2D70))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2D7C))))``];
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2C12))))``];
val usage = (0, 16);

val sum___aeabi_fmul_c8 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fmul_c8 "sum___aeabi_fmul_c8";






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
