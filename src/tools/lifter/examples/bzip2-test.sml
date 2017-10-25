open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting bzip2-aarch64.da\n";

val (region_map, bzip2_sections) = read_disassembly_file (K true) "bzip2-aarch64.da"

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
  bzip2_sections

val _ = print "\n\n\n";
val _ = print_with_style [Bold, Underline] "Lifting bzip2-m0-cortex.da\n";
val (region_map, bzip2_sections) = read_disassembly_file (K true) "bzip2-m0-cortex.da"

val (thm_m0, errors) = bmil_m0_LittleEnd_Process.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x10000))
  bzip2_sections

val _ = print "\n\n";

val _ = new_theory "bzip2";
val _ = save_thm ("bzip2_arm8_program_THM", thm_arm8);
val _ = save_thm ("bzip2_m0_program_THM", thm_m0);
val _ = export_theory();
