open HolKernel boolLib Parse bossLib;

open bir_predLib;

val _ = new_theory "storeload_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition storeload_init_addr_def:
 storeload_init_addr : word64 = 0x628w
End

Definition storeload_end_addr_def:
 storeload_end_addr : word64 = 0x690w
End

val sprn = "x2";
val bspec_storeload_pre_tm = bslSyntax.bandl [
  mem_area_disj_reg_bir_tm ("x11", 8) ("x12", 1),
  mem_addrs_stack_disj_reg_bir_tm sprn "x11",
  mem_addrs_stack_disj_reg_bir_tm sprn "x12",
  mem_addrs_aligned_prog_disj_bir_tm sprn,
  mem_addrs_aligned_prog_disj_bir_tm "x11",
  mem_addrs_aligned_prog_disj_bir_tm "x12"
]

val pcond_is_sat = birs_smtLib.bir_check_sat false bspec_storeload_pre_tm;
val _ = if pcond_is_sat then () else
        raise Feedback.mk_HOL_ERR "storeload_specScript" "." "precondition is not satisfiable, seems to contain a contradiction";

Definition bspec_storeload_pre_def:
bspec_storeload_pre (x:word64) : bir_exp_t =
 ^bspec_storeload_pre_tm
End

val _ = export_theory ();
