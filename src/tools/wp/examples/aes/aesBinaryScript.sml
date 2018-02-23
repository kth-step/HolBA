open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;



val _ = print_with_style [Bold, Underline] "Lifting aes-aarch64.da\n";

val (region_map, aes_sections) = read_disassembly_file_regions "aes-aarch64.da"

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  aes_sections


val _ = print "\n\n";

val _ = new_theory "aesBinary";
val _ = save_thm ("aes_arm8_program_THM", thm_arm8);
val _ = export_theory();
