structure balrob_pfmisc_Lib =
struct

local
  open HolKernel Parse

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;


(* __aeabi_i2f *)

val sums        = [sum___clzsi2];
val entry_label = "__aeabi_i2f";

val sum___aeabi_i2f =
      create_func_summary n_dict bl_dict_ sums entry_label;


in (* outermost local *)

  val sum___aeabi_i2f = sum___aeabi_i2f;

end (* outermost local *)

end (* struct *)
