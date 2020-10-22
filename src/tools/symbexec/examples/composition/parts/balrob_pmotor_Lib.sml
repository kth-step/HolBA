structure balrob_pends_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;


(* motor_prep_input *)

val sums        = [];
val entry_label = "motor_prep_input";
val sum_motor_prep_input =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* motor_set_l *)

val sums        = [sum_motor_prep_input];
val entry_label = "motor_set_l";
val sum_motor_set_l =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* motor_set_r *)

val sums        = [sum_motor_prep_input];
val entry_label = "motor_set_r";
val sum_motor_set_r =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* motor_set *)

val sums        = [sum_motor_set_r, sum_motor_set_l];
val entry_label = "motor_set";
val lbl_tm      = find_func_lbl_tm entry_label;
val sum_motor_set =
      create_func_summary n_dict bl_dict_ sums entry_label;


in (* outermost local *)

  val sum_motor_set = sum_motor_set;

end (* outermost local *)

end (* struct *)
