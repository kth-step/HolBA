open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "chacha";

val _ = lift_da_and_store progname "chacha.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x106bc));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "chacha" "bir_chacha_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "chacha" bir_prog_def;

val _ = export_theory ();
