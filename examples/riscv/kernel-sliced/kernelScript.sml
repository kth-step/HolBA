open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "kernel";

val _ = lift_da_and_store "kernel" "kernel.da" da_riscv
 ((Arbnum.fromInt 0x800000e0), (Arbnum.fromInt 0x80000268));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "-" "bir_kernel_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "kernel" bir_prog_def;

val _ = export_theory ();
