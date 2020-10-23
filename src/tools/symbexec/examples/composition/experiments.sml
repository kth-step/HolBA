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

open balrob_pends_Lib;
open balrob_pfmisc_Lib;
open balrob_pfadd_Lib;
open balrob_pfsub_Lib;
open balrob_pfmul_Lib;
open balrob_pfdiv_Lib;
open balrob_ptop_Lib;


(* imu_handler_pid_entry *)
val sums        = [sum_timer_read,
                   sum_motor_set_f,
                   sum_atan2f_own,
                   sum___lesf2,
                   sum___aeabi_i2f,
                   sum___aeabi_fadd,
                   sum___aeabi_fsub,
                   sum___aeabi_fmul,
                   sum___aeabi_fdiv];

val entry_label     = "imu_handler_pid_entry";
val entry_label_sub = "pid_msg_write"; (* don't go into pid_msg_write *)

val lbl_tm      = find_func_lbl_tm entry_label;
val end_lbl_tms = (find_func_lbl_tm entry_label_sub)::(find_func_ends n_dict entry_label);

val sum_imu_handler_pid_entry =
      obtain_summary n_dict bl_dict_ sums lbl_tm end_lbl_tms;


