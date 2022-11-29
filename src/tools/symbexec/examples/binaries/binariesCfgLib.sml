structure binariesCfgLib =
struct
local

  open HolKernel Parse;

  open binariesLib;
  open binariesDefsLib;

  open bir_cfgLib;
  open bir_cfg_m0Lib;

  open bir_block_collectionLib;

  val libname = "binariesCfgLib";
  val ERR = Feedback.mk_HOL_ERR libname;
  val wrap_exn = Feedback.wrap_exn libname;

in (* local *)



(*
=================================================================================================
=================================================================================================
*)
  local


val n_dict_0 = cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val n_dict_1 = cfg_update_nodes_basic prog_lbl_tms_ n_dict_0;

val n_dict_2 = cfg_update_nodes_gen "update_node_guess_type_call"
                                    (update_node_guess_type_call bl_dict_ prog_fun_entry_lbl_tms)
                                    prog_lbl_tms_
                                    n_dict_1;

(* =============================================================================== *)
(* =============================================================================== *)
(* hack maps *)

    (* hack for indirect jumps (a.k.a. oracle) *)
(*
    val hack_map_1
             = [(0x2bc8, "469F (mov pc, r3)", CFGNT_Jump, [
                         "542c0000",
                         "fe2b0000",
                         "fe2b0000",
                         "2c2d0000",
                         "fa2b0000",
                         "fa2b0000",
                         "222d0000",
                         "2c2d0000",
                         "fa2b0000",
                         "222d0000",
                         "fa2b0000",
                         "2c2d0000",
                         "302d0000",
                         "302d0000",
                         "302d0000",
                         "382d0000"
                       ]),
                    (0x2814, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "2a290000",
                         "66280000",
                         "8a280000",
                         "28280000",
                         "8a280000",
                         "06290000",
                         "8a280000",
                         "28280000",
                         "66280000",
                         "66280000",
                         "06290000",
                         "28280000",
                         "5c290000",
                         "5c290000",
                         "5c290000",
                         "12290000"

                       ]),
                    (0x28ba, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "66280000",
                         "66280000",
                         "8a280000",
                         "26280000",
                         "8a280000",
                         "06290000",
                         "8a280000",
                         "26280000",
                         "66280000",
                         "66280000",
                         "06290000",
                         "26280000",
                         "5c290000",
                         "5c290000",
                         "5c290000",
                         "10290000"
                       ])
                   ];
(* -0x428‬ *)
(*
 000033d4
 00003354
 00003394
*)
    val hack_map_2
             = [(0x27a0, "469F (mov pc, r3)", CFGNT_Jump, [
                         "282c0000",
                         "27d60000",
                         "27d60000",
                         "29040000",
                         "27d20000",
                         "27d20000",
                         "28fa0000",
                         "29040000",
                         "27d20000",
                         "28fa0000",
                         "27d20000",
                         "29040000",
                         "29080000",
                         "29080000",
                         "29080000",
                         "29100000"
                       ]),
                    (0x23ec, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "25020000",
                         "243e0000",
                         "24620000",
                         "24000000",
                         "24620000",
                         "24de0000",
                         "24620000",
                         "24000000",
                         "243e0000",
                         "243e0000",
                         "24de0000",
                         "24000000",
                         "25340000",
                         "25340000",
                         "25340000",
                         "24ea0000"
                       ]),
                    (0x2492, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "243e0000",
                         "243e0000",
                         "24620000",
                         "23fe0000",
                         "24620000",
                         "24de0000",
                         "24620000",
                         "23fe0000",
                         "243e0000",
                         "243e0000",
                         "24de0000",
                         "23fe0000",
                         "25340000",
                         "25340000",
                         "25340000",
                         "24e80000"
                       ])
                   ];


*)


    val hack_map_3
             = [(0x10000bb0, "469F (mov pc, r3)", CFGNT_Jump, [
                         "10000c3c",
                         "10000be6",
                         "10000be6",
                         "10000d14",
                         "10000be2",
                         "10000be2",
                         "10000d0a",
                         "10000d14",
                         "10000be2",
                         "10000d0a",
                         "10000be2",
                         "10000d14",
                         "10000d18",
                         "10000d18",
                         "10000d18",
                         "10000d20"
                       ]),
                    (0x1000060c, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "10000722",
                         "1000065e",
                         "10000682",
                         "10000620",
                         "10000682",
                         "100006fe",
                         "10000682",
                         "10000620",
                         "1000065e",
                         "1000065e",
                         "100006fe",
                         "10000620",
                         "10000754",
                         "10000754",
                         "10000754",
                         "1000070a"
                       ]),
                    (0x100006b2, "4697 (mov pc, r2)", CFGNT_Jump, [
                         "1000065e",
                         "1000065e",
                         "10000682",
                         "1000061e",
                         "10000682",
                         "100006fe",
                         "10000682",
                         "1000061e",
                         "1000065e",
                         "1000065e",
                         "100006fe",
                         "1000061e",
                         "10000754",
                         "10000754",
                         "10000754",
                         "10000708"
                       ])
                   ];
    val resolv_map = (*hack_map_1@hack_map_2@*)hack_map_3;
(* =============================================================================== *)
(* =============================================================================== *)

val n_dict_3 = cfg_update_nodes_gen "update_node_manual_indir_jump"
				    (update_node_manual_indir_jump resolv_map)
				    prog_lbl_tms_
				    n_dict_2;

val n_dict_4 = cfg_update_nodes_gen "update_node_guess_type_return"
                                    (update_node_guess_type_return)
                                    prog_lbl_tms_
                                    n_dict_3;



(*

val lbl_tm = mk_key_from_address 32 (Arbnum.fromHexString "c1c");
val lbl_tm = ``BL_Address (Imm32 11098w)``;

val n      = valOf (lookup_block_dict n_dict_1 lbl_tm);
val bl     = valOf (lookup_block_dict bl_dict lbl_tm);

*)

val find_rel_symbol_from_lbl_tm = mem_find_rel_symbol_by_addr_ o dest_lbl_tm;

val ns_ = List.map snd (Redblackmap.listItems n_dict_4);

val ci  = List.foldr (fn (n,l) => let val vo = collect_node_callinfo find_rel_symbol_from_lbl_tm n in
                                 if isSome vo then (valOf vo)::l else l end) [] ns_;


val n_dict_5 = cfg_update_nodes_gen "update_node_fix_return_goto"
                                    (update_node_fix_return_goto find_rel_symbol_from_lbl_tm (lookup_calls_to ci))
                                    prog_lbl_tms_
                                    n_dict_4;

val ns  = List.map snd (Redblackmap.listItems n_dict_5);


(*
=================================================================================================
=================================================================================================
=================================================================================================
=================================================================================================
=================================================================================================
*)
  in (* local *)

val n_dict = n_dict_5;
val ci = ci;

(*
val cfg_targets_to_lbl_tms = cfg_targets_to_lbl_tms;
*)

fun find_node n_dict lbl_tm =
  valOf (lookup_block_dict n_dict lbl_tm)
  handle Option => raise ERR "find_node" ("couldn't find node " ^ (term_to_string lbl_tm));


fun get_fun_cfg_walk_succ (n: cfg_node) =
  let
    val lbl_tm    = #CFGN_lbl_tm n;
    val descr_o   = #CFGN_hc_descr n;
    val n_type    = #CFGN_type n;
    val n_targets = #CFGN_targets n;
    val debug_on = false;

    val descr = case descr_o of
                   SOME x => x
                 | NONE => raise ERR "get_fun_cfg_walk_succ"
                                     ("need node description text from lifter: " ^ (term_to_string lbl_tm));

    val _ = if not debug_on then () else
            print ("node: " ^ (term_to_string lbl_tm) ^ "\n" ^
                   " - " ^ descr ^ "\n");
  in
    case n_type of
        CFGNT_Halt      => []
      | CFGNT_Jump      => n_targets
      | CFGNT_CondJump  => n_targets
      | CFGNT_Basic     => n_targets
      | CFGNT_Call cs   => (* this accounts for a walk that
                              doesn't follow call edges *)
                           cs
      | CFGNT_Return    => [] (* this terminates returns *)
  end;


fun build_fun_cfg_nodes _  acc []                     = acc
  | build_fun_cfg_nodes n_dict acc (lbl_tm::lbl_tm_l) =
      let
        val n         = find_node n_dict lbl_tm;
        val n_type    = #CFGN_type n;
        val n_targets = #CFGN_targets n;

        val _ = if not (cfg_node_type_eq (n_type, CFGNT_Halt)) andalso
                   not (List.null n_targets) then () else
                (print "indirection ::: in ";
                 print (prog_lbl_to_mem_rel_symbol lbl_tm);
                 print "\t"; print (valOf (#CFGN_hc_descr n) handle Option => "NONE");
                 print "\t"; print_term lbl_tm);

        val new_nodes = lbl_tm::acc;

        val next_tm_l      =
              List.filter (fn x => not ((List.exists (fn y => identical x y) (new_nodes@lbl_tm_l))))
                          (get_fun_cfg_walk_succ n);
        val new_lbl_tm_l   = next_tm_l@lbl_tm_l;
      in
        build_fun_cfg_nodes n_dict new_nodes new_lbl_tm_l
      end;


fun lbl_tm_to_rel_symbol lbl_tm =
  (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) lbl_tm;

fun node_to_rel_symbol (n:cfg_node) =
  lbl_tm_to_rel_symbol (#CFGN_lbl_tm n);

fun build_fun_cfg bl_dict n_dict name =
  let
    val entry_lbl_tm = mem_symbol_to_prog_lbl name;
    val cfg_comp_lbls = build_fun_cfg_nodes n_dict [] [entry_lbl_tm];
    val _ = print ("walked " ^ (Int.toString (length cfg_comp_lbls)) ^
                   " nodes (" ^ name ^ ")\n");
    (* validate that all collected nodes belong to the function *)
    val ns_names   = List.map (lbl_tm_to_rel_symbol) cfg_comp_lbls
      handle Option => raise ERR "build_fun_cfg" "cannot find label for node address";
    val allAreName = List.foldr (fn (n,b) => b andalso (
           n = name
      )) true ns_names;
  in
    {
      CFGG_name       = name,
      CFGG_entries    = [entry_lbl_tm],
      CFGG_exits      = [], (* this is not right *)
      CFGG_nodes      = cfg_comp_lbls,
      CFGG_node_dict  = n_dict,
      CFGG_block_dict = bl_dict
    } : cfg_graph
  end;


(*
=================================================================================================
*)

fun count_paths_to_ret_nexts follow_call n_dict lbl_tm =
  let
    val n:cfg_node = find_node n_dict lbl_tm;
    val n_type = #CFGN_type n;
    val nexts = #CFGN_targets n;
  in
    case n_type of
         CFGNT_Halt    => ([], [])
       | CFGNT_Call cs => (if follow_call then nexts else
                           cs
                          ,
                           if follow_call then [] else
                           List.map (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) nexts
                          )
       | CFGNT_Return  => (if follow_call then nexts else [], [])
       | _             => (nexts, [])
  end;

(* following calls doesn't work like this, we would need a call stack of course *)
fun count_paths_to_ret follow_call ns stop_at_l lbl_tm =
  if (List.exists (fn x => identical lbl_tm x) stop_at_l) then (1, []) else
  let
    val (nexts, calls) = count_paths_to_ret_nexts follow_call ns lbl_tm;
    val summary = List.map (count_paths_to_ret follow_call ns stop_at_l) nexts;
  in
    if length nexts = 0 then (1, []) else
    List.foldr (fn ((i, l), (i_s, l_s)) => (i+i_s, l@l_s)) (0, calls) summary
  end;

fun to_histogram_proc (x, [])        = [(x,1)]
  | to_histogram_proc (x, (y, n)::l) =
      if x = y
      then ((y, n+1)::l)
      else (y, n)::(to_histogram_proc (x, l));

fun to_histogram sum_calls =
  List.foldr to_histogram_proc [] sum_calls;

(*
=================================================================================================
=================================================================================================
*)
  end (* local *)


end (* local *)
end (* struct *)
