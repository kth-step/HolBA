open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_driverLib;


(*
(*  *)

val sums        = [];
val entry_label = "";
val sum_ =
      create_func_summary n_dict bl_dict_ sums entry_label;
*)

val sums            = [];
val entry_label     = "imu_handler_pid_entry";

val lbl_tm      = find_func_lbl_tm entry_label;
val end_lbl_tms = [``BL_Address (Imm32 0x3A2w)``];

val sum_experiment =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;

