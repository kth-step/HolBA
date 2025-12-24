open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "isqrt";

val progname = "isqrt";

val _ = lift_da_and_store progname "isqrt.da" da_arm8
 ((Arbnum.fromInt 0x718), (Arbnum.fromInt 0x750));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch progname ("bir_"^progname^"_prog_def");
val _ = gen_prog_vars_birenvtyl_defthms progname bir_prog_def;

val _ = export_theory ();
