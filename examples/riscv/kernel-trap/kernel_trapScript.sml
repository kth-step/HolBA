open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "kernel_trap";

val _ = lift_da_and_store "kernel_trap" "kernel_trap.da" da_riscv
 ((Arbnum.fromInt 0x800000e0), (Arbnum.fromInt 0x8000026C));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "-" "bir_kernel_trap_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "kernel_trap" bir_prog_def;

val _ = export_theory ();
