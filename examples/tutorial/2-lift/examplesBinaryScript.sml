open HolKernel Parse;

open bir_inst_liftingLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;



val _ = print_with_style_ [Bold, Underline] "Lifting ../1-code/add_reg.da\n";

val (region_map, aes_sections) = read_disassembly_file_regions "../1-code/add_reg.da"

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen
                           ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
                           aes_sections

val (lift_app_1_tm, bir_prog_tm) = (dest_comb o concl) thm_arm8;
val (_, bir_progbin_tm) = dest_comb lift_app_1_tm;


val _ = print "\n\n";

val _ = new_theory "examplesBinary";

val bir_add_reg_prog_def = Define `bir_add_reg_prog = ^bir_prog_tm`;
val bir_add_reg_progbin_def = Define `bir_add_reg_progbin = ^bir_progbin_tm`;

val bir_add_reg_arm8_lift_THM = save_thm ("bir_add_reg_arm8_lift_THM",
       REWRITE_RULE [GSYM bir_add_reg_prog_def,
                     GSYM bir_add_reg_progbin_def] thm_arm8);

val _ = export_theory();
