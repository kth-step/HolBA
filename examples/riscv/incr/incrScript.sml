open HolKernel Parse;

open bir_lifter_interfaceLib;
open bir_symbLib;

val progname = "incr";

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory progname;

val _ = lift_da_and_store progname (progname ^ ".da") da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10495));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch progname ("bir_"^progname^"_prog_def");
val _ = gen_prog_vars_birenvtyl_defthms progname bir_prog_def;

val _ = export_theory ();
