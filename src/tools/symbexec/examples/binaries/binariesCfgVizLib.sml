structure binariesCfgVizLib =
struct
local

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;

open graphVizLib;

(*
val i = 0x10000;
val n = hd (#CFGG_nodes ns_c);
val t = ``BL_Address (Imm32 990w)``;
 *)
fun to_escaped_string s =
  let
    fun add_escape acc []      = acc
      | add_escape acc (c::cs) =
          let val c_ = if c = #"\"" then [c, #"\\"] else [c] in
            add_escape (c_@acc) cs
          end;
  in
    (implode o List.rev o (add_escape []) o explode) s
  end;

fun gen_graph_for_edges_proc idx (CFGT_DIR   t, (gn, ges, i)) =
      (gn, (idx, (Arbnum.toInt o dest_lbl_tm) t)::ges, i)
  | gen_graph_for_edges_proc idx (CFGT_INDIR t, (gn, ges, i)) =
      ((i, node_shape_circle, [("indir", "???")])::gn, (idx, i)::ges, i+1);

fun gen_graph_for_nodes_proc (n:cfg_node, (gns, ges, i)) =
  let
    val idx     = (Arbnum.toInt o dest_lbl_tm o #CFGN_lbl_tm) n;
    val shape   = if #CFGN_type n = CFGNT_Call orelse #CFGN_type n = CFGNT_Return
                  then node_shape_doublecircle else node_shape_default;
    val content = [("id", "0x" ^ (Arbnum.toHexString o dest_lbl_tm o #CFGN_lbl_tm) n)];
    val node    = (idx, shape, content);

    val (gns_, ged_, i_) = List.foldr (gen_graph_for_edges_proc idx) ([], [], i) (#CFGN_goto n);

    val new_gns = gns_@(node::gns);
    val new_ges = ged_@(ges);
    val new_i   = i_;
  in
    (new_gns, new_ges, new_i)
  end;

(* directory creation helper *)
  fun makedir makepath path =
    let
      val r = OS.Process.system ("mkdir " ^ (if makepath then "-p " else "") ^ path);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "makedir" ("couldn't create the following directory: " ^ path)
              else
                ();
    in
      ()
    end;

fun get_tempfile prefix =
  let
    val tempdir = "tempdir";
    val _ = makedir true tempdir;
    val date = Date.fromTimeLocal (Time.now ());
    val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
  in
    tempdir ^ "/cfg_" ^ datestr
  end;

in (* local *)

fun display_graph_cfg_ns ns =
  let
    val (nodes, edges, _) = List.foldr gen_graph_for_nodes_proc ([], [], 0x10000) ns;

    val file = get_tempfile "cfg_";
    val dot_str = gen_graph (nodes, edges);
    val _ = writeToFile dot_str (file ^ ".dot");
    val _ = convertAndView file;
  in () end;

fun display_call_graph ci symbs_sec_text =
  let
    val node_idxs = List.tabulate (length symbs_sec_text, fn idx =>
                              (idx, List.nth (symbs_sec_text, idx)));
    fun find_node_n s = (fst o valOf o (List.find (fn p => snd p = s))) node_idxs
                        handle Option => raise ERR "displayCallGraph" "bug: this must be something";
    fun find_node_i i = (snd o List.nth) (node_idxs, i);

    val nodes = List.tabulate (length symbs_sec_text, fn idx => (
          idx,
          node_shape_default,
          [(Int.toString idx, find_node_i idx)]
      ));
    val edges = List.concat (List.map (fn (x, ys, _) =>
                  List.map (fn y => (find_node_n x, find_node_n y)) ys) ci);
    val edges_unique = List.foldr (fn (x,l) => if List.exists (fn y => x=y) l then l else (x::l)) [] edges;
    val edges = edges_unique;

    val file = get_tempfile "cfg_";
    val dot_str = gen_graph (nodes, edges);
    val _ = writeToFile dot_str (file ^ ".dot");
    val _ = convertAndView file;
  in () end;

fun show_call_graph () =
  display_call_graph ci symbs_sec_text;

fun show_cfg_fun do_walk ns name =
  let
    val ns_1 = if do_walk then
                 (#CFGG_nodes o (build_fun_cfg ns)) name
               else
                 List.filter ((fn s => s = name) o node_to_rel_symbol) ns;
  in
    display_graph_cfg_ns ns_1
  end;

end (* local *)
end (* struct *)
