(* lets holbuild stage ldrstr-aarch64.da for the relative read below; no-op otherwise *)
fun holbuild_extra_deps (_ : string list) = ()
val _ = holbuild_extra_deps ["ldrstr-aarch64.da"]

open HolKernel Parse;
open PPBackEnd;
open bir_update_blockTheory bir_inst_liftingTheory;
open bir_inst_liftingHelpersLib;
open bir_inst_liftingLib;
open gcc_supportLib;

val _ = new_theory "ldrstrBinary";

val _ = Parse.current_backend := PPBackEnd.vt100_terminal
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting ldrstr-aarch64.da\n";

val (region_map, minimal_sections) = read_disassembly_file_regions
        "ldrstr-aarch64.da";

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen 
            ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000)) minimal_sections

Theorem ldrstr_arm8_THM = thm_arm8

val _ = export_theory();
