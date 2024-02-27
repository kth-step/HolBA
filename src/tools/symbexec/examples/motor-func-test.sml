open HolKernel Parse;
open PPBackEnd;

open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val dafilename = "motor_set.da";
val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000));

val _ = print_with_style_ [Bold, Underline] ("Lifting "^dafilename^" (m0_mod)\n");

val (region_map, sections) = read_disassembly_file_regions dafilename;
val (thm, errors) = bmil_m0_mod_LittleEnd_Process.bir_lift_prog_gen prog_range sections;

val _ = print "\n\n";

(*
val _ = new_theory "aesBinary";
val _ = save_thm ("aes_arm8_program_THM", thm_arm8);
val _ = save_thm ("aes_m0_program_THM", thm_m0);
val _ = FileSys.chDir "./output";
val _ = export_theory();
*)


