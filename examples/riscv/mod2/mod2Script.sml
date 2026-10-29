(* lets holbuild stage mod2.da for the relative read below; no-op otherwise *)
fun holbuild_extra_deps (_ : string list) = ()
val _ = holbuild_extra_deps ["mod2.da"]

open HolKernel boolLib Parse bossLib;

open bir_lifter_interfaceLib;
open birs_auxLib;

val progname = "mod2";

val _ = new_theory progname;

val _ = lift_da_and_store progname (progname ^ ".da") da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x10498));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch progname ("bir_"^progname^"_prog_def");
val _ = gen_prog_vars_birenvtyl_defthms progname bir_prog_def;

val _ = export_theory ();
