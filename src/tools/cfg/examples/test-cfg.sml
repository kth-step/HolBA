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

(* execute the test cases *)
val _ = print "Running simple test cases.\n";
val expected_exits = [mk_key_from_address 32 (Arbnum.fromHexString "817a")];
val _ = if list_eq identical expected_exits (#CFGG_exits g2) then () else
        raise Fail ("Unexpected exit list.");

val expected_jump = mk_key_from_address 32 (Arbnum.fromHexString "817a");
val _ = if cfg_node_type_eq (CFGNT_Jump, #CFGN_type (lookup_block_dict_value (#CFGG_node_dict g2) expected_jump "" "oh no")) then () else
        raise Fail ("Unexpected node type. Should be Jump.");

val expected_condjump = mk_key_from_address 32 (Arbnum.fromHexString "8140");
val _ = if cfg_node_type_eq (CFGNT_CondJump, #CFGN_type (lookup_block_dict_value (#CFGG_node_dict g2) expected_condjump "" "oh no")) then () else
        raise Fail ("Unexpected node type. Should be CondJump.");

val expected_basic = mk_key_from_address 32 (Arbnum.fromHexString "8144");
val _ = if cfg_node_type_eq (CFGNT_Basic, #CFGN_type (lookup_block_dict_value (#CFGG_node_dict g2) expected_basic "" "oh no")) then () else
        raise Fail ("Unexpected node type. Should be Basic.");

val expected_no_targets = mk_key_from_address 32 (Arbnum.fromHexString "817a");
val _ = if List.null (#CFGN_targets (lookup_block_dict_value (#CFGG_node_dict g2) expected_no_targets "" "oh no")) then () else
        raise Fail ("Unexpected node targets. Should be no targets.");


(* traversal example, single entry recursion, stop at first revisit or exit *)
fun traverse_graph (g:cfg_graph) entry visited acc =
  let
    val n = lookup_block_dict_value (#CFGG_node_dict g) entry "traverse_graph" "n";

    val targets = #CFGN_targets n;
    val descr_o = #CFGN_hc_descr n;
    val n_type  = #CFGN_type n;

    val descr   = case descr_o of
                     SOME x => x
                   | NONE   => raise ERR "traverse_graph" "I expect descriptions on all nodes (becasue of lifting)";
    val _ = if cfg_node_type_eq (n_type, CFGNT_CondJump) then
              print ("cjmp node --- " ^ descr ^ "\n")
            else
              ();

    val acc_new = (if cfg_node_type_eq (n_type, CFGNT_CondJump) then [entry] else [])@acc;

    val targets_to_visit = List.filter (fn x => List.all (fn y => not (identical x y)) visited) targets;

    val result = List.foldr (fn (entry',(visited',acc')) => traverse_graph g entry' visited' acc') (entry::visited, acc_new) targets_to_visit;
  in result end;

val (visited_nodes,cjmp_nodes) = traverse_graph g2 (hd (#CFGG_entries g2)) [] [];

(*
val l1 = (#CFGG_nodes g2);
val l2 = visited_nodes;

List.filter (fn x => (List.all (fn y => x <> y) l2)) l1
List.filter (fn x => (List.all (fn y => x <> y) l1)) l2

Arbnum.toHexString (Arbnum.fromString "33146")
*)
fun compare_list_contents l1 l2 =
  (length l1 = length l2) andalso
  (List.all (fn x => (List.exists (fn y => identical x y) l2)) l1) andalso
  (List.all (fn x => (List.exists (fn y => identical x y) l1)) l2);

val expected_cjmp_nodes =
  List.filter (fn lbl_tm =>
    let
      val n = lookup_block_dict_value (#CFGG_node_dict g2) lbl_tm "expected_cjmp_nodes" "n";
      val n_type  = #CFGN_type n;
    in
      cfg_node_type_eq (n_type, CFGNT_CondJump)
    end
  ) (#CFGG_nodes g2);

val _ = if compare_list_contents expected_cjmp_nodes cjmp_nodes then () else
        raise Fail ("Traversal collection is unexpected.");

val _ = if compare_list_contents (#CFGG_nodes g2) visited_nodes then () else
        raise Fail ("Traversal visitating is unexpected.");
