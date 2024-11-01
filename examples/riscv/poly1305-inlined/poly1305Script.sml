open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "poly1305";

val _ = lift_da_and_store "poly1305" "poly1305.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10E10));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "poly1305" "bir_poly1305_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "poly1305" bir_prog_def;

val _ = export_theory ();
