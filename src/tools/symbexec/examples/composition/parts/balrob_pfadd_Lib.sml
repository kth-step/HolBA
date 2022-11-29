structure balrob_pfadd_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;


val fadd_offset = 0x1000030e - 0x257A;
fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);
val _ = print "fadd offset is: 0x";
val _ = print (Arbnum.toHexString (Arbnum.fromInt fadd_offset));
val _ = print "\n";


(* __aeabi_fadd_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x257A))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x2598))))``];
val usage = (0, 15);

val sum___aeabi_fadd_c1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fadd_c1 "sum___aeabi_fadd_c1";


(* __aeabi_fadd_c2 *)

val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x25A0))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x25AE))))``];
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x24C2))))``];
val usage = (0, 29);

val sum___aeabi_fadd_c2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fadd_c2 "sum___aeabi_fadd_c2";


(* __aeabi_fadd_c3 *)

val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x25D0))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (fadd_offset + 0x24C2))))``];
val usage = (0, 10);

val sum___aeabi_fadd_c3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fadd_c3 "sum___aeabi_fadd_c3";


(* __aeabi_fadd *)

val sums        = [sum___clzsi2,
                   sum___aeabi_fadd_c1,
                   sum___aeabi_fadd_c2,
                   sum___aeabi_fadd_c3];
val entry_label = "__aeabi_fadd";

val sum___aeabi_fadd =
      create_func_summary n_dict bl_dict_ sums entry_label;


in (* outermost local *)

val sum___aeabi_fadd = sum___aeabi_fadd;

end (* outermost local *)

end (* struct *)
