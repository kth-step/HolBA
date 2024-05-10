open HolKernel Parse;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_lifter_interfaceLib;

val _ = new_theory "mod2";

val _ = lift_da_and_store "mod2" "mod2.da" da_riscv ((Arbnum.fromInt 0), (Arbnum.fromInt 0x8));

val _ = export_theory ();
