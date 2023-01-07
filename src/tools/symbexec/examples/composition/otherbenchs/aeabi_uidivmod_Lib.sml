structure aeabi_uidivmod_Lib =
struct

local
(*
  open HolKernel Parse

  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);


(* __aeabi_uidivmod *)

      val timer_meas = timer_start 1;



val aeabi_uidivmod_end_lbl_tms =
  [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000fc))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000108))))``];


val aeabi_uidivmod_exit_end_lbl_tms =
  [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009e))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000ce))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000f2))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000fe))))``];


(* __aeabi_uidivmod_entry *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000000))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000003c))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000006c))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000020))))``]
                  @aeabi_uidivmod_end_lbl_tms
                  @aeabi_uidivmod_exit_end_lbl_tms;
val usage = (0, 18);

val sum___aeabi_uidivmod_entry =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_entry "sum___aeabi_uidivmod_entry";


(* __aeabi_uidivmod_lp1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000003c))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000006c))))``];
val usage = (0, 24);

val sum___aeabi_uidivmod_lp1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_lp1 "sum___aeabi_uidivmod_lp1";


(* __aeabi_uidivmod_lp2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000006c))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009c))))``];
val usage = (0, 24);

val sum___aeabi_uidivmod_lp2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_lp2 "sum___aeabi_uidivmod_lp2";


(* __aeabi_uidivmod_exit1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009e))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000ce))))``];
val usage = (0, 24);

val sum___aeabi_uidivmod_exit1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_exit1 "sum___aeabi_uidivmod_exit1";


(* __aeabi_uidivmod_exit2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000ce))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000f2))))``];
val usage = (0, 18);

val sum___aeabi_uidivmod_exit2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_exit2 "sum___aeabi_uidivmod_exit2";

(*
(* __aeabi_uidivmod_exit3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000f2))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009c))))``];
val usage = (0, 100);

val sum___aeabi_uidivmod_exit3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_exit3 "sum___aeabi_uidivmod_exit3";
*)


(*

(* __aeabi_uidivmod_loopexp *)
val sums        = [sum___aeabi_uidivmod_lp1,
                   sum___aeabi_uidivmod_lp2];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000003c))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009e))))``];
val usage = (0, 500);

val sum___aeabi_uidivmod_loopexp =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_loopexp "sum___aeabi_uidivmod_loopexp";


*)


(*
(* __aeabi_uidivmod_p1 *)
val sums        = [sum___aeabi_uidivmod_entry,
                   sum___aeabi_uidivmod_lp1,
                   sum___aeabi_uidivmod_lp2,
                   sum___aeabi_uidivmod_exit1,
                   sum___aeabi_uidivmod_exit2];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000000))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009e))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000020))))``]
                  @aeabi_uidivmod_end_lbl_tms
                  @aeabi_uidivmod_exit_end_lbl_tms;
val usage = (0, 18);

val sum___aeabi_uidivmod_p1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_p1 "sum___aeabi_uidivmod_p1";
*)





val sums        = [];
val entry_label = "__aeabi_uidivmod";
(*
val sum___aeabi_uidivmod =
      create_func_summary n_dict bl_dict_ sums entry_label;
*)

      val _ = timer_stop (fn s => print("time for " ^ entry_label ^ ": " ^ s ^ "\n")) timer_meas;
*)

in (* outermost local *)

(*
  val sum___aeabi_uidivmod      = sum___aeabi_uidivmod;
*)

end (* outermost local *)

end (* struct *)
