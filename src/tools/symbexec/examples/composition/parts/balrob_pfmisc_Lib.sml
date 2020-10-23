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


(* __aeabi_fcmplt *)

val sums        = [sum___lesf2];
val entry_label = "__aeabi_fcmplt";

val sum___aeabi_fcmplt =
      create_func_summary n_dict bl_dict_ sums entry_label;
(* not usable at the moment, see abs_own *)


(* abs_own *)

val sums        = [sum___lesf2];(*sum___aeabi_fcmplt];*)
val entry_label = "abs_own";

val sum_abs_own =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
if use sum___aeabi_fcmplt:
     {message = "pred prefix must be the equal", origin_function =
      "merge_states_by_intervalvar", origin_structure =
      "bir_symbexec_sumLib"} raised
*)


in (* outermost local *)

  val sum___aeabi_i2f = sum___aeabi_i2f;
  val sum_abs_own     = sum_abs_own;

end (* outermost local *)

end (* struct *)
