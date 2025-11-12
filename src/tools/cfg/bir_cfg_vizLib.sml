structure bir_cfg_vizLib =
struct
local

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_programSyntax;

  open wordsSyntax;
  open bir_immSyntax;

  open bir_cfgLib;

  open holba_fileLib;
  open graphVizLib;

  (* error handling *)
  val libname  = "bir_cfg_vizLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  (*
  val i = 0x10000;
  val n = hd (#CFGG_nodes ns_c);
  val t = ``BL_Address (Imm32 990w)``;
   *)

  val dest_lbl_tm = dest_word_literal o snd o gen_dest_Imm o dest_BL_Address;

  fun gen_graph_for_edges_proc idx (t, (gn, ges, i)) =
	(gn, (idx, (Arbnum.toInt o dest_lbl_tm) t)::ges, i);

  fun gen_graph_for_nodes_proc (n:cfg_node, (gns, ges, i)) =
    let
      val idx_num = (dest_lbl_tm o #CFGN_lbl_tm) n;
      val idx     = Arbnum.toInt idx_num;
      val shape   = if cfg_nodetype_is_call (#CFGN_type n) orelse cfg_node_type_eq (#CFGN_type n, CFGNT_Return)
		    then node_shape_doublecircle else node_shape_default;
      val content = [("id", "0x" ^ (Arbnum.toHexString idx_num))];
      val node    = (idx, shape, content);

      val targets = #CFGN_targets n;
      val (gns_, ged_, i_) =
        if not (List.null targets) then
          List.foldr (gen_graph_for_edges_proc idx) ([], [], i) (targets)
        else
          ((i, node_shape_circle, [("indir", "???")])::[], (idx, i)::[], i+1);

      val new_gns = gns_@(node::gns);
      val new_ges = ged_@(ges);
      val new_i   = i_;
    in
      (new_gns, new_ges, new_i)
    end;

  fun gen_statistics_for_nodes_proc (n:cfg_node, (instrs, condjmps, indirjmps)) =
    if cfg_node_type_eq (#CFGN_type n, CFGNT_Basic) orelse
       cfg_nodetype_is_call (#CFGN_type n) orelse
       cfg_node_type_eq (#CFGN_type n, CFGNT_Return) then
      (instrs + 1, condjmps, indirjmps)
    else if cfg_node_type_eq (#CFGN_type n, CFGNT_CondJump) then
    let
      val descr_o = #CFGN_hc_descr n;
      val descr_o_s = if isSome descr_o then valOf descr_o else "NONE";
      val targets = #CFGN_targets n;
      val numtargets = List.length targets;
      val numtargets_s = Int.toString numtargets;

      val s = "----------------- " ^ descr_o_s ^ " :::: " ^ numtargets_s ^ "\n";
      (*val _ = print s;*)
    in
      (instrs + 1, condjmps + 1, indirjmps)
    end
    else if cfg_node_type_eq (#CFGN_type n, CFGNT_Jump) then
    let
      val descr_o = #CFGN_hc_descr n;

      val targets = #CFGN_targets n;
      val numtargets = List.length targets;

      val numtargets_s = Int.toString numtargets;
      (*val _ = if numtargets > 0 then () else raise ERR "gen_statistics_for_nodes_proc" "indirjump error";*)
      val descr_o_s = if isSome descr_o then valOf descr_o else "NONE";
      
      val s = descr_o_s ^ " :::: " ^ numtargets_s ^ "\n";
      val _ = print s;

      val is_indir   = numtargets > 1;
    in
      (instrs + 1, condjmps, if is_indir then indirjmps + 1 else indirjmps)
    end
    else if cfg_node_type_eq (#CFGN_type n, CFGNT_Halt) then
      raise ERR "gen_statistics_for_nodes_proc" "halt not allowed here"
    else
      raise ERR "gen_statistics_for_nodes_proc" "unknown node type";

in

  fun cfg_display_graph_ns ns =
    let
      val (nodes, edges, _) = List.foldr gen_graph_for_nodes_proc ([], [], 0x10000) ns;

      val file = get_tempfile "cfg" "nil";
      val dot_str = gen_graph (nodes, edges);
      val _ = writeToFile dot_str (file ^ ".dot");
      val _ = convertAndView file;
    in () end;

  fun cfg_statistics_ns ns =
    let
      val (instrs, condjmps, indirjmps) = List.foldr gen_statistics_for_nodes_proc (0, 0, 0) ns;

      val s = "instrs: " ^ (Int.toString instrs) ^ "\n" ^
              "condjmps: " ^ (Int.toString condjmps) ^ "\n" ^
              "indirjmps: " ^ (Int.toString indirjmps) ^ "\n";
      val _ = print s;
    in (instrs, condjmps, indirjmps) end;

end (* local *)
end (* struct *)
