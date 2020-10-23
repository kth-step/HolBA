structure balrob_ptop_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;


open balrob_pends_Lib;
open balrob_pfmul_Lib;
open balrob_pmotor_Lib;


(* motor_set_f *)

val sums        = [sum_motor_set, sum___aeabi_f2iz, sum___aeabi_fmul];
val entry_label = "motor_set_f";
val lbl_tm      = find_func_lbl_tm entry_label;
val sum_motor_set_f =
      create_func_summary n_dict bl_dict_ sums entry_label;


in (* outermost local *)

  val sum_motor_set_f = sum_motor_set_f;

end (* outermost local *)

end (* struct *)
