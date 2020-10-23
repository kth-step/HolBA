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
