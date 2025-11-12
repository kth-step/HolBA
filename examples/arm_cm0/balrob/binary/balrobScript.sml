open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;
open birs_auxLib;

val progname = "balrob";
val dafilename = progname^".elf.da";

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory progname;

val _ = lift_da_and_store progname (dafilename) da_cm0_mod ((Arbnum.fromInt 0x08000000), (Arbnum.fromInt 0x08010000));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch progname ("bir_"^progname^"_prog_def");
val _ = gen_prog_vars_birenvtyl_defthms progname bir_prog_def;

val _ = export_theory ();
