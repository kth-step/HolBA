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


in (* outermost local *)

  val sum_motor_set_f = sum_motor_set_f;
  val sum_atan2f_own  = sum_atan2f_own;

end (* outermost local *)

end (* struct *)
