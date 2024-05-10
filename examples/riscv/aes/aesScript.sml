open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "aes";

val _ = lift_da_and_store "aes" "aes.da" da_riscv ((Arbnum.fromInt 0), (Arbnum.fromInt 0x500));

val _ = export_theory ();
