open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib
open bmil_arm8

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val (region_map, aes_sections) = read_disassembly_file (K true) "aes-aarch64.da"
val (thm, errors) = bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  aes_sections

val _ = print "\n\n";

val _ = new_theory "aes";
val _ = save_thm ("aes_program_THM", thm);
val _ = export_theory();
