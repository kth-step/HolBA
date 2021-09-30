
open HolKernel Parse boolLib bossLib;

open bir_inst_liftingLib;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;
open PPBackEnd Parse;

open listSyntax;
open bir_programSyntax;
open bir_symb_masterLib;

open bir_miscLib;


val dafilename = "aes-aarch64.da";
val dafilename = "retonly-aarch64.da";
val dafilename = "aes-2-aarch64.da";
val dafilename = "aes-vs-aarch64.da";

(*
=============================================================================
*)

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ dafilename ^ "\n");

val (region_map, aes_sections) = read_disassembly_file_regions dafilename;

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000)) aes_sections;

val prog = (snd o dest_comb o concl) thm_arm8;


val _ = print "\nLifting done.\n\n";

(*
=============================================================================
*)

val _ = print "\nNow symbexecing.\n\n";

val prog = (snd o dest_eq o concl o EVAL) prog;


val timer = timer_start 1;

val numblocks = (length o fst o dest_list o dest_BirProgram) prog;
val maxdepth = 5 * numblocks (* (~1); *);
val precond = ``bir_exp_true``;
val leafs = symb_exec_process_to_leafs_nosmt maxdepth precond prog;

val _ = timer_stop (fn timestr => print ("hello " ^ dafilename ^", you took " ^ timestr ^ "\n")) timer;

val _ = print ("Number of blocks: " ^ (Int.toString numblocks) ^ "\n");


val _ = print "\nDone symbexecing.\n\n";

