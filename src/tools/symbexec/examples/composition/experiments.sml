open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

(*
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_funcLib;
open bir_countw_simplificationLib;

open commonBalrobScriptLib;
*)

open bir_symbexec_driverLib;


(*
(*  *)

val sums        = [];
val entry_label = "";
val sum_ =
      create_func_summary n_dict bl_dict_ sums entry_label;
*)

open balrob_pends_Lib;


(* __aeabi_fmul *)

val sums        = [sum___clzsi2(*,
                   sum___aeabi_fmul_c1,
                   sum___aeabi_fmul_c2,
                   sum___aeabi_fmul_c3*)];
val entry_label = "__aeabi_fmul";

val sum___aeabi_fmul =
      create_func_summary n_dict bl_dict_ sums entry_label;

(*
Exception-
   HOL_ERR
     {message =
      "couldn't resolve addr_tm: BExp_BinExp BIExp_Plus (BExp_Const (Imm32 13604w))\n  (BExp_Den (BVar \"fr_237957_R3\" (BType_Imm Bit32)))",
      origin_function = "mem_load", origin_structure = "bir_inst_liftingLib"}
   raised
*)
