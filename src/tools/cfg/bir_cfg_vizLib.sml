structure bir_cfg_vizLib =
struct
local

  open wordsSyntax;
  open bir_immSyntax;

  open bir_cfgLib;

  open bir_fileLib;
  open graphVizLib;

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
      val shape   = if #CFGN_type n = CFGNT_Call orelse #CFGN_type n = CFGNT_Return
		    then node_shape_doublecircle else node_shape_default;
      val content = [("id", "0x" ^ (Arbnum.toHexString idx_num))];
      val node    = (idx, shape, content);

      val targets = #CFGN_goto n;
      val (gns_, ged_, i_) =
        if targets <> [] then
          List.foldr (gen_graph_for_edges_proc idx) ([], [], i) (targets)
        else
          ((i, node_shape_circle, [("indir", "???")])::[], (idx, i)::[], i+1);

      val new_gns = gns_@(node::gns);
      val new_ges = ged_@(ges);
      val new_i   = i_;
    in
      (new_gns, new_ges, new_i)
    end;

in

  fun cfg_display_graph_ns ns =
    let
      val (nodes, edges, _) = List.foldr gen_graph_for_nodes_proc ([], [], 0x10000) ns;

      val file = get_tempfile "cfg";
      val dot_str = gen_graph (nodes, edges);
      val _ = writeToFile dot_str (file ^ ".dot");
      val _ = convertAndView file;
    in () end;

end (* local *)
end (* struct *)
