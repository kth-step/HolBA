open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "isqrt";

val _ = lift_da_and_store "isqrt" "isqrt.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x104c1));

val _ = export_theory ();
