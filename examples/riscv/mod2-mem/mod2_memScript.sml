open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "mod2_mem";

val _ = lift_da_and_store "mod2_mem" "mod2_mem.da" da_riscv ((Arbnum.fromInt 0), (Arbnum.fromInt 0x12));

val _ = export_theory ();
