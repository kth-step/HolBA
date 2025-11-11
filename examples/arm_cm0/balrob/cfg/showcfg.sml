open HolKernel Parse boolLib bossLib;

open bir_block_collectionLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

val prog_tm = ((rhs o concl) balrobLib.bir_balrob_prog_def);

(* build the dictionaries using the library under test *)
val _ = print "Building dictionaries.\n";
val bl_dict = gen_block_dict prog_tm;
val lbl_tms = get_block_dict_keys bl_dict;

(* build the cfg and update the basic blocks *)
val _ = print "Building node dict.\n";
open bir_cfgLib;
val n_dict_0 = cfg_build_node_dict bl_dict lbl_tms;

val n_dict_1 = cfg_update_nodes_basic lbl_tms n_dict_0;
val n_dict = n_dict_1;

val entries = [``BL_Address (Imm32 (0x1000020cw))``]; (* __aeabi_fadd *)
val entries = [``BL_Address (Imm32 (0x100013b4w))``]; (* __clzsi2 *)
val entries = [``BL_Address (Imm32 (0x100005a4w))``]; (* __aeabi_fdiv *)
val _ = print "Building cfg.\n";
val g1 = cfg_create "balrob" entries n_dict bl_dict;
(*
val _ = print "Updating cfg.\n";
val n_dict = cfg_update_nodes_basic lbl_tms n_dict;
val g2 = cfg_update g1 n_dict;
*)

(* display the cfg *)
val g_display = g1;
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g_display))) (#CFGG_nodes g_display);
val _ = cfg_display_graph_ns ns;
val _ = cfg_statistics_ns ns;


val _ = print "\n\n\n\n"

val g_some = g_display;
val ns_all = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g_some))) ((map fst o Redblackmap.listItems o #CFGG_node_dict) g_some);
val _ = cfg_statistics_ns ns_all;




(*
val n_dict_2 = cfg_update_nodes_gen "update_node_guess_type_call"
                                    (update_node_guess_type_call bl_dict_ prog_fun_entry_lbl_tms)
                                    prog_lbl_tms_
                                    n_dict_1;
*)

(*
~/data/hol/HolBA_symbexec_old_noproof/src/tools/symbexec/examples$ gedit balrob-show.sml
binaries/binariesCfgLib.sml
*)