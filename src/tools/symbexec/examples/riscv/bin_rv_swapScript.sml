open HolKernel Parse
open PPBackEnd;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_update_blockTheory;
open bir_inst_liftingTheory;

open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "bin_rv_swap";


val dafilename = "swap.da";
val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x20));

val _ = print_with_style_ [Bold, Underline] ("Lifting "^dafilename^" (riscv)\n");

val (region_map, sections) = read_disassembly_file_regions dafilename;
val (thm, errors) = bmil_riscv.bir_lift_prog_gen prog_range sections;
Theorem bin_rv_swap_thm = thm


val _ = print "\n\n";


val _ = export_theory();
