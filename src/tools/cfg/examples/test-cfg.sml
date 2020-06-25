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
val n_dict = cfg_update_nodes_basic bl_dict lbl_tms n_dict;
val g2 = cfg_update g1 n_dict;

(* execute the test cases *)
val _ = print "Running simple test cases.\n";
val expected_exits = [mk_key_from_address 32 (Arbnum.fromHexString "817a")];
val _ = if expected_exits = #CFGG_exits g2 then () else
        raise Fail ("Unexpected exit list.");

val expected_jump = mk_key_from_address 32 (Arbnum.fromHexString "817a");
val _ = if CFGNT_Jump = #CFGN_type (valOf (lookup_block_dict (#CFGG_node_dict g2) expected_jump)) then () else
        raise Fail ("Unexpected node type. Should be Jump.");

val expected_condjump = mk_key_from_address 32 (Arbnum.fromHexString "8140");
val _ = if CFGNT_CondJump = #CFGN_type (valOf (lookup_block_dict (#CFGG_node_dict g2) expected_condjump)) then () else
        raise Fail ("Unexpected node type. Should be CondJump.");

val expected_basic = mk_key_from_address 32 (Arbnum.fromHexString "8144");
val _ = if CFGNT_Basic = #CFGN_type (valOf (lookup_block_dict (#CFGG_node_dict g2) expected_basic)) then () else
        raise Fail ("Unexpected node type. Should be Basic.");
