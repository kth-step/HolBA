open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val _ = new_theory "bir_prog_add_reg";

val _ = lift_da_and_store "add_reg"
                          "../1-code/src/add_reg.da"
                          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

val _ = export_theory();
