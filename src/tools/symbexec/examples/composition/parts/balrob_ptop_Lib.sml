structure balrob_ptop_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;


open balrob_pends_Lib;

open balrob_pfmisc_Lib;

open balrob_pfadd_Lib;
open balrob_pfsub_Lib;
open balrob_pfmul_Lib;
open balrob_pfdiv_Lib;

open balrob_pmotor_Lib;


(* motor_set_f *)

val sums        = [sum_motor_set, sum___aeabi_f2iz, sum___aeabi_fmul];
val entry_label = "motor_set_f";
val lbl_tm      = find_func_lbl_tm entry_label;
val sum_motor_set_f =
      create_func_summary n_dict bl_dict_ sums entry_label;



(* atan2f_own *)
val sums        = [sum___lesf2,
                   sum_abs_own,
                   sum___aeabi_fadd,
                   sum___aeabi_fsub,
                   sum___aeabi_fmul,
                   sum___aeabi_fdiv];(*sum___aeabi_fcmplt];*)
val entry_label = "atan2f_own";

val sum_atan2f_own =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
time to drive symbolic execution: 10.120s

min = 808w
max = 2038w
*)


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

val usage = commonBalrobScriptLib.get_fun_usage entry_label;

val sum_imu_handler_pid_entry =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_imu_handler_pid_entry entry_label;

in (* outermost local *)

  val sum_motor_set_f = sum_motor_set_f;
  val sum_atan2f_own  = sum_atan2f_own;
  val sum_imu_handler_pid_entry = sum_imu_handler_pid_entry;

end (* outermost local *)

end (* struct *)
