open HolKernel Parse;

open bir_lifter_interfaceLib;

val _ = new_theory "mod2";

val _ = lift_da_and_store "mod2" "mod2.da" da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10495));

val _ = export_theory ();
