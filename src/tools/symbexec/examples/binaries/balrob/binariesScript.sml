open HolKernel Parse
open PPBackEnd;

open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;

open binariesBalrobDefsLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "binaries";


fun lift_da_file_to_thm (prog_id, (da_file_lift, da_file_mem, mem_file), thm_name, (mem_region_const, mem_region_data, mem_region_stack)) =
  let
    val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ da_file_lift ^ " (" ^ arch_str ^ ")\n");

    val (region_map, sections) = read_disassembly_file_regions_filter symb_filter_lift da_file_lift;

    val (thm, errors) = bmil_m0_mod_LittleEnd_Process.bir_lift_prog_gen prog_range sections;

    val _ = save_thm (thm_name, thm);
  in
    ()
  end;

val _ = List.map lift_da_file_to_thm configs;


val _ = export_theory();
