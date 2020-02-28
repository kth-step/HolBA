open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib;

open binariesBalrobDefsLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "binaries";


val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ da_file_lift ^ " (" ^ arch_str ^ ")\n");

val (region_map, sections) = read_disassembly_file_regions_filter symb_filter_lift da_file_lift;

val (thm, errors) = bmil_m0_mod_LittleEnd_Process.bir_lift_prog_gen prog_range sections;

val _ = save_thm (thm_name, thm);


val _ = export_theory();
