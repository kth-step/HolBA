open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "chachapoly";

val _ = lift_da_and_store "chachapoly" "chachapoly.da" da_riscv ((Arbnum.fromInt 0x105a8), (Arbnum.fromInt 0x120BC));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch "chachapoly" "bir_chachapoly_prog_def";
val _ = gen_prog_vars_birenvtyl_defthms "chachapoly" bir_prog_def;

val _ = export_theory ();
