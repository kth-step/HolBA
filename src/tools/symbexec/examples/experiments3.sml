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

(* __lesf2 *)

val sums        = [];
val entry_label = "__lesf2";
val sum___lesf2 =
      create_func_summary n_dict bl_dict_ sums entry_label;

(* ========= pfmisc ======== *)

(* __aeabi_fcmplt *)

val sums        = [sum___lesf2];
val entry_label = "__aeabi_fcmplt";

val sum___aeabi_fcmplt =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
 {message = "lbl_tm must be the same", origin_function =
      "merge_states_by_intervalvar", origin_structure =
      "bir_symbexec_sumLib"} raised
*)

(* abs_own *)

val sums        = [sum__aeabi_fcmplt];
val entry_label = "abs_own";

val sum_abs_own =
      create_func_summary n_dict bl_dict_ sums entry_label;

(* atan2f_own *)
(* requires fadd, fdiv, absown, fcmplt, fsub, fmul *)
