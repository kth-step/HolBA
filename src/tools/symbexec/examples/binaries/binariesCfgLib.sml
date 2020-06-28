structure binariesCfgLib =
struct
local

open binariesLib;
open binariesDefsLib;

open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open optionSyntax;
open wordsSyntax;
open listSyntax;

open bir_block_collectionLib;
open bir_cfgLib;

(* simple helpers *)
val BVarLR32_tm = ``BVar "LR" (BType_Imm Bit32)``;
fun is_Assign_LR tm =
  if is_BStmt_Assign tm then
    ((fst o dest_BStmt_Assign) tm) = BVarLR32_tm
  else
    false;

in (* local *)

(*
=================================================================================================
=================================================================================================
*)
  local

(*
val bl_dict = bl_dict_;
val n_dict = cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val lbl_tm = mk_key_from_address 32 (Arbnum.fromHexString "c1c");
val n      = valOf (lookup_block_dict n_dict lbl_tm);
val bl     = valOf (lookup_block_dict bl_dict lbl_tm);
*)
fun update_node_guess_type_call bl_dict n =
  if #CFGN_type n <> CFGNT_Jump orelse #CFGN_targets n = [] then n else
  (* take jumps with direct target to filter out the calls *)
  let
    val debug_on = false;

    val lbl_tm = #CFGN_lbl_tm n;
    val targets = #CFGN_targets n;

    val _ = if not debug_on then () else
            print ((term_to_string lbl_tm) ^ "\n");

    val bl =
                  case lookup_block_dict bl_dict lbl_tm of
                     SOME x => x
                   | NONE => raise ERR "update_node_guess_type_call"
                                       ("cannot find label " ^ (term_to_string lbl_tm));

    val (_, bbs, _) = dest_bir_block bl;

    val _ = if length targets = 1 then () else
            raise ERR "update_node_guess_type_call"
                                   "there should be exactly 1 direct jump target"
    val goto_tm = hd targets;

    val isCall_lr       =  List.exists is_Assign_LR ((fst o dest_list) bbs);
    val isCall_to_entry = (List.exists (fn x => x = goto_tm) prog_fun_entry_lbl_tms);

    val _ = if isCall_lr = isCall_to_entry then ()
            else raise ERR "update_node_guess_type_call"
                           "something in call detection is unexpected";
    val isCall = isCall_lr;

    val _ = if not (debug_on andalso isCall) then () else
            (print "call        ::: "; print (Option.getOpt(#CFGN_hc_descr n, "NONE")); print "\t"; print_term lbl_tm);

    val call_targets_guess = [cfg_node_to_succ_lbl_tm n];

    val new_type = if isCall then CFGNT_Call call_targets_guess else #CFGN_type n;

    val new_n =
            { CFGN_lbl_tm   = #CFGN_lbl_tm n,
              CFGN_hc_descr = #CFGN_hc_descr n,
              CFGN_targets  = #CFGN_targets n,
              CFGN_type     = new_type
            } : cfg_node;
  in
    new_n
  end;



(* =============================================================================== *)
(* =============================================================================== *)
(* hack maps *)

    (* hack for indirect jumps (a.k.a. oracle) *)
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
    val resolv_map = hack_map_1@hack_map_2;
(* =============================================================================== *)
(* =============================================================================== *)

fun update_node_manual_indir_jump resolv_map (n:cfg_node) =
  if #CFGN_type n <> CFGNT_Jump orelse #CFGN_targets n <> [] then n else
  (* take jumps with no resolved direct targets to filter out the returns *)
  let
    val debug_on = false;

    val lbl_tm = #CFGN_lbl_tm n;
    val descr_o = #CFGN_hc_descr n;

    val descr = case descr_o of
                   SOME x => x
                 | NONE => raise ERR "update_node_manual_indir_jump"
                                     ("need node description text from lifter: " ^ (term_to_string lbl_tm));

    val hack_map = resolv_map;

    val hackMatch = List.find (fn (loc_, descr_, _, _) =>
                                 descr = descr_ andalso
                                 dest_lbl_tm lbl_tm = Arbnum.fromInt loc_
                              ) hack_map;
    val isIndirJump = isSome hackMatch;
    (*
    val tl = ((fn (_, _, nt, tl) => tl) o hd) hack_map;
    val s = hd tl;
rev_hs_to_num (Arbnum.fromInt 0) s
Arbnum.toHexString (rev_hs_to_num (Arbnum.fromInt 0) s)
    *)
    val indirJumpUpdate = Option.map (fn (_, _, nt, tl) =>
        let
          val tl_unique = List.foldr (fn (x,l) => if List.exists (fn y => x=y) l then l else (x::l)) [] tl;
          fun split_string_byte s =
            let
              val _ = if (String.size s) mod 2 = 0 then () else
                        raise ERR "split_string_byte" "bug: string length is wrong";
              val len = (String.size s) div 2;
            in
              (Arbnum.fromHexString (String.substring(s, (len*2) - 2, 2)),
                                     String.substring(s, 0, (len*2) - 2))
            end;
          fun rev_hs_to_num acc "" = acc
	    | rev_hs_to_num acc s  =
                let
                  val sp = split_string_byte s;
                  val n  = Arbnum.+(Arbnum.*(acc, Arbnum.fromInt 256), fst sp);
                in
                  rev_hs_to_num n (snd sp)
                end;
        in
          (nt, List.map (rev_hs_to_num (Arbnum.fromInt 0)) tl_unique)
        end
      ) hackMatch;
(*
    val isIndirJump = String.isSubstring "(mov pc," descr;
*)
    val _ = if not (debug_on andalso isIndirJump) then () else
            (print "indirect J  ::: "; print descr; print "\t"; print_term lbl_tm);

    val new_type = if isIndirJump then ((fst o valOf) indirJumpUpdate) else #CFGN_type n;

    val new_goto = if isIndirJump then (((List.map (mk_lbl_tm)) o snd o valOf) indirJumpUpdate) else #CFGN_targets n;

    val new_n =
            { CFGN_lbl_tm   = #CFGN_lbl_tm n,
              CFGN_hc_descr = #CFGN_hc_descr n,
              CFGN_targets  = new_targets,
              CFGN_type     = new_type
            } : cfg_node;
  in
    new_n
  end;



(*
length ns

val ns = List.map (update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
val lbl_tm = mk_lbl_tm (Arbnum.fromInt 7936);
val n  = find_node ns lbl_tm;
val _ = List.map (update_node_guess_type_return o update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
*)
fun update_node_guess_type_return (n:cfg_node) =
  if #CFGN_type n <> CFGNT_Jump orelse #CFGN_targets n <> [] then n else
  (* take jumps with no resolved direct targets to filter out the returns *)
  let
    val debug_on = false;

    val lbl_tm = #CFGN_lbl_tm n;
    val descr_o = #CFGN_hc_descr n;

    val descr = case descr_o of
                   SOME x => x
                 | NONE => raise ERR "update_node_guess_type_return"
                                     ("need node description text from lifter: " ^ (term_to_string lbl_tm));

    val isReturn = ((String.isSubstring "pop {" descr) andalso
                    (String.isSubstring "pc}" descr))
                   orelse
                   (String.isSubstring "(bx lr)" descr);

    (* hack for hand inspected instructions *)
    val isReturn = isReturn orelse (
                   (lbl_tm = mk_lbl_tm (Arbnum.fromInt 0x1fc)) andalso
                   (String.isPrefix "4718 (" descr)
        );

    val _ = if not (debug_on andalso isReturn) then () else
            (print "return      ::: "; print descr; print "\t"; print_term lbl_tm);

    (* still unclear type... *)
    val _ = if (isReturn) (* orelse (not debug_on) *) then ()
            else print ("update_node_guess_type_return :: " ^
                           "cannot determine type: " ^ descr ^
                            "\t" ^ (term_to_string lbl_tm) ^ "\n");

    val new_type = CFGNT_Return;

    val new_n =
            { CFGN_lbl_tm   = #CFGN_lbl_tm n,
              CFGN_hc_descr = #CFGN_hc_descr n,
              CFGN_targets  = #CFGN_targets n,
              CFGN_type     = new_type
            } : cfg_node;
  in
    new_n
  end;




(* why need this? / where to put this? *)
(*
fun is_lbl_in_cfg_nodes lbl_tm (ns:cfg_node list) = List.exists (fn n => (#CFGN_lbl_tm n) = lbl_tm) ns;

fun find_node (ns: cfg_node list) lbl_tm =
  valOf (List.find (fn n => (#CFGN_lbl_tm n) = lbl_tm) ns)
  handle Option => raise ERR "find_node" ("couldn't find node: " ^ (term_to_string lbl_tm));
*)

fun collect_node_callinfo (n:cfg_node) =
  let
    val rel_name  = (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm o #CFGN_lbl_tm) n;
    val n_type    = #CFGN_type n;
    val n_targets = #CFGN_targets n;
  in
    if not (cfg_nodetype_is_call n_type) then NONE else SOME (
     rel_name,
     List.map (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) n_targets,
     let
       val call_conts = case n_type of
                           CFGNT_Call c => c
                         | _ => raise ERR "collect_node_callinfo" "this would never happen";
       val _ = if length c = 1 then () else
               raise ERR "collect_node_callinfo" "expecting exactly one call continuation target";
     in
       hd c
     end
    )
  end;


fun lookup_calls_to ci to = List.foldr (fn ((_, tol, returnto), l) =>
    if List.exists (fn x => x = to) tol then
      (returnto)::l
    else
      l
  ) [] ci;

fun update_node_fix_return_goto lookup_calls_to_f n =
  if #CFGN_type n <> CFGNT_Return then n else
  let
    val debug_on = false;

    val rel_name = (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm o #CFGN_lbl_tm) n;

    val new_goto = ((List.map CFGT_DIR) o lookup_calls_to_f) rel_name;

    val new_n =
            { CFGN_lbl_tm = #CFGN_lbl_tm n,
              CFGN_descr  = #CFGN_descr n,
              CFGN_succ   = #CFGN_succ n,
              CFGN_goto   = new_goto,
              CFGN_type   = #CFGN_type n
            } : cfg_node;
  in
    new_n
  end;


fun cfg_targets_to_lbl_tms_exn l et =
    (valOf o cfg_targets_to_lbl_tms) l
    handle Option => raise ERR "cfg_targets_to_lbl_tms_exn" ("unexpected indirection: " ^ et);

fun cfg_targets_to_direct_lbl_tms l = List.foldr (fn
         (CFGT_DIR   tm, ls) => tm::ls
       | (CFGT_INDIR tm , ls) => (print ("unexpected indirection: " ^
                                        (term_to_string tm) ^ "\n"); ls)
  ) [] l;


(*
=================================================================================================
*)

val ns_ = List.map (update_node_guess_type_return o update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
val ci  = List.foldr (fn (n,l) => let val vo = collect_node_callinfo n in
                                 if isSome vo then (valOf vo)::l else l end) [] ns_;

val ns  = List.map (update_node_fix_return_goto (lookup_calls_to ci)) ns_;


(*
=================================================================================================
=================================================================================================
*)
  in (* local *)

val ns = ns;
val ci = ci;

val cfg_targets_to_lbl_tms = cfg_targets_to_lbl_tms;

fun find_node (ns:cfg_node list) lbl_tm =
  (valOf o List.find (fn n => #CFGN_lbl_tm n = lbl_tm)) ns
  handle Option => raise ERR "find_node" ("couldn't find node " ^ (term_to_string lbl_tm));


fun get_fun_cfg_walk_succ (n: cfg_node) =
  let
    val lbl_tm = #CFGN_lbl_tm n;
    val descr  = #CFGN_descr n;
    val n_type = #CFGN_type n;
    val n_goto = #CFGN_goto n;
    val debug_on = false;
    val _ = if not debug_on then () else
            print ("node: " ^ (term_to_string lbl_tm) ^ "\n" ^
                   " - " ^ descr ^ "\n");
  in
    case n_type of
        CFGNT_Unknown   => (if debug_on then print "UNRESOLVED NODE\n" else (); [])
      | CFGNT_Halt      => []
      | CFGNT_Basic     => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_Jump      => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_CondJump  => cfg_targets_to_direct_lbl_tms n_goto
      | CFGNT_Call      => (* this accounts for a walk that
                              doesn't follow call edges *)
                           [(valOf o #CFGN_succ) n]
      | CFGNT_Return    => [] (* this terminates returns *)
  end;


fun build_fun_cfg_nodes _  acc []                 = acc
  | build_fun_cfg_nodes ns acc (lbl_tm::lbl_tm_l) =
      let
        val n = find_node ns lbl_tm;
        val n_type = #CFGN_type n;

        val _ = if n_type <> CFGNT_Unknown then () else
                (print "indirection ::: in ";
                 print (prog_lbl_to_mem_rel_symbol lbl_tm);
                 print "\t"; print (#CFGN_descr n);
                 print "\t"; print_term lbl_tm);

        val new_node  = if n_type = CFGNT_Unknown then [] else [n];
        val new_nodes = new_node@acc;

        val next_tm_l      = List.filter (fn x => not ((is_lbl_in_cfg_nodes x new_nodes) orelse
                                                       (List.exists (fn y => x = y) lbl_tm_l)))
                                         (get_fun_cfg_walk_succ n);
        val new_lbl_tm_l   = next_tm_l@lbl_tm_l;
      in
        build_fun_cfg_nodes ns new_nodes new_lbl_tm_l
      end;

fun node_to_rel_symbol (n:cfg_node) =
  (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) (#CFGN_lbl_tm n);

fun build_fun_cfg ns name =
  let
    val entry_lbl_tm = mem_symbol_to_prog_lbl name;
    val cfg_comp_ns = build_fun_cfg_nodes ns [] [entry_lbl_tm];
    val _ = print ("walked " ^ (Int.toString (length cfg_comp_ns)) ^
                   " nodes (" ^ name ^ ")\n");
    (* validate that all collected nodes belong to the function *)
    val ns_names   = List.map node_to_rel_symbol cfg_comp_ns
      handle Option => raise ERR "build_fun_cfg" "cannot find label for node address";
    val allAreName = List.foldr (fn (n,b) => b andalso (
           n = name
      )) true ns_names;
  in
    {
      CFGG_name  = name,
      CFGG_entry = entry_lbl_tm,
      CFGG_nodes = cfg_comp_ns
    } : cfg_graph
  end;


(*
=================================================================================================
*)

fun count_paths_to_ret_nexts follow_call ns lbl_tm =
  let
    val n = find_node ns lbl_tm;
    val n_type = #CFGN_type n;
    val nexts = (valOf o cfg_targets_to_lbl_tms o #CFGN_goto) n;
  in
    case n_type of
         CFGNT_Unknown => raise ERR "count_paths_to_ret_nexts" " unknown control flow"
       | CFGNT_Halt    => ([], [])
       | CFGNT_Call    => (if follow_call then nexts else
                           [(valOf o #CFGN_succ) n]
                           ,
                           if follow_call then [] else
                           List.map (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) nexts)
       | CFGNT_Return  => (if follow_call then nexts else [], [])
       | _             => (nexts, [])
  end;

(* following calls doesn't work like this, we would need a call stack of course *)
fun count_paths_to_ret follow_call ns stop_at_l lbl_tm =
  if (List.exists (fn x => lbl_tm = x) stop_at_l) then (1, []) else
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
