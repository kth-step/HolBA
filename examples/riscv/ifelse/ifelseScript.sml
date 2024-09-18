open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "ifelse";

val _ = lift_da_and_store "ifelse" "ifelse.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x104D0));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "ifelse" "bir_ifelse_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "ifelse" bir_prog_def;

val _ = export_theory ();
