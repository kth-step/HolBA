structure aeabi_uidivmod_Lib =
struct

local
  open HolKernel Parse

  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;


(* __aeabi_uidivmod *)

      val timer_meas = timer_start 1;

val sums        = [];
val entry_label = "__aeabi_uidivmod";
val sum___aeabi_uidivmod =
      create_func_summary n_dict bl_dict_ sums entry_label;

      val _ = timer_stop (fn s => print("time for " ^ entry_label ^ ": " ^ s ^ "\n")) timer_meas;


in (* outermost local *)

  val sum___aeabi_uidivmod      = sum___aeabi_uidivmod;

end (* outermost local *)

end (* struct *)
