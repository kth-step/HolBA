open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

(* prepare test program terms and theorems *)
open toyBinaryTheory;
val lift_thm = toy_m0_program_THM;
val prog_tm = ((snd o dest_comb o concl) lift_thm);

(* build the dictionaries using the library under test *)
val _ = print "Building dictionaries.\n";
open bir_block_collectionLib;
val bl_dict = gen_block_dict prog_tm;
val lbl_tms = get_block_dict_keys bl_dict;

(* build the cfg and update the basic blocks *)
val _ = print "Building node dict.\n";
open bir_cfgLib;
val n_dict = cfg_build_node_dict bl_dict lbl_tms;
val entries = [mk_key_from_address 32 (Arbnum.fromHexString "8104")];
val _ = print "Building cfg.\n";
val g1 = cfg_create "toy" entries n_dict bl_dict;
val _ = print "Updating cfg.\n";
val n_dict = cfg_update_nodes_basic lbl_tms n_dict;
val g2 = cfg_update g1 n_dict;

(* display the cfg *)
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g2))) (#CFGG_nodes g2);
val _ = cfg_display_graph_ns ns;
