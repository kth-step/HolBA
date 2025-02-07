open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "chacha20";

val _ = lift_da_and_store "chacha20" "chacha20.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x111C4));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "chacha20" "bir_chacha20_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "chacha20" bir_prog_def;

val _ = export_theory ();
