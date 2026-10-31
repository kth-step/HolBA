Theory bir_prog_add_reg

Libs bir_lifter_interfaceLib

(* lets holbuild stage add_reg.da for the relative read below; no-op otherwise *)
fun holbuild_extra_deps (_ : string list) = ()
val _ = holbuild_extra_deps ["../1-code/src/add_reg.da"]

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = lift_da_and_store "add_reg"
                          "../1-code/src/add_reg.da"
                          da_arm8
                          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
