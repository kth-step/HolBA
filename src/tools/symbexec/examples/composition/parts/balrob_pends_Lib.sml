structure balrob_pends_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;


(*
"motor_prep_input",
"__lesf2",
"__clzsi2",
"__aeabi_f2iz",
(*"pid_msg_write",*)
"timer_read"
*)


(* __lesf2 *)

val sums        = [];
val entry_label = "__lesf2";
val sum___lesf2 =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* __clzsi2 *)

val sums        = [];
val entry_label = "__clzsi2";
val sum___clzsi2 =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* __aeabi_f2iz *)

val sums        = [];
val entry_label = "__aeabi_f2iz";
val sum___aeabi_f2iz =
      create_func_summary n_dict bl_dict_ sums entry_label;


(* timer_read *)

val sums        = [];
val entry_label = "timer_read";
val sum_timer_read =
      create_func_summary n_dict bl_dict_ sums entry_label;


in (* outermost local *)

  val sum___lesf2      = sum___lesf2;
  val sum___clzsi2     = sum___clzsi2;
  val sum___aeabi_f2iz = sum___aeabi_f2iz;
  val sum_timer_read   = sum_timer_read;

end (* outermost local *)

end (* struct *)
