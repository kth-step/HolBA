open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "swap";

val _ = lift_da_and_store "swap" "swapO1.da" ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

val _ = export_theory ();
