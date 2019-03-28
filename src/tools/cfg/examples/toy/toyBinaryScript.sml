open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


val _ = print "\n\n\n";
val _ = print_with_style_ [Bold, Underline] "Lifting m0-toy.da\n";
val (region_map, aes_sections) = read_disassembly_file_regions "m0-toy.da"

val (thm_m0, errors) = bmil_m0_LittleEnd_Process.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x10000))
  aes_sections


val _ = print "\n\n";

val _ = new_theory "toyBinary";
val _ = save_thm ("toy_m0_program_THM", thm_m0);
val _ = export_theory();
