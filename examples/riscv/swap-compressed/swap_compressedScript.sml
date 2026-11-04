(* lets holbuild stage swap_compressed.da for the relative read below; no-op otherwise *)
fun holbuild_extra_deps (_ : string list) = ()
val _ = holbuild_extra_deps ["swap_compressed.da"]

open HolKernel Parse;

open bir_lifter_interfaceLib;
open birs_auxLib;

(* Same program as examples/riscv/swap, but compiled with -march=rv64gc so
   that the binary mixes 16-bit (compressed) and 32-bit instructions.
   The end address of the code area is the address of the last instruction
   plus its size, which is 2 for a compressed instruction. *)

val progname = "swap_compressed";

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory progname;

val _ = lift_da_and_store progname (progname ^ ".da") da_riscv ((Arbnum.fromInt 0x10488), (Arbnum.fromInt 0x1049a));

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_prog_def = DB.fetch progname ("bir_"^progname^"_prog_def");
val _ = gen_prog_vars_birenvtyl_defthms progname bir_prog_def;

val _ = export_theory ();
