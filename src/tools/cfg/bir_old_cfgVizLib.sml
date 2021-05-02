structure bir_old_cfgVizLib =
struct

local

open HolKernel Parse boolLib bossLib;
open bir_programSyntax;
open bir_immSyntax;
open graphVizLib;
open bir_old_cfgLib;
open listSyntax;

val ERR = mk_HOL_ERR "bir_old_cfgVizLib"

in

(*---------------------------------------------------------------------------*)

val eval_label = (snd o dest_eq o concl o EVAL);

fun ziplist [] [] = []
  | ziplist (x::xs) (y::ys) = (x,y)::(ziplist xs ys)
  | ziplist _ _ = raise ERR "ziplist" "list length doesn't match";

fun unziplist [] = ([],[])
  | unziplist ((x,y)::xys) = let val (xs,ys) = unziplist xys; in (x::xs,y::ys) end;

(*---------------------------------------------------------------------------*)

fun convert_inout_to_graphviz idxs_sel (blocks, in_idxs, out_idxs) =
  let
    fun block_to_node (i,block) =
      let
        val (raw_BL_term,_,_,_) = dest_bir_block block;
        val label = eval_label raw_BL_term;
        val label_str =
          if is_BL_Label label then
            dest_BL_Label_string label
          else if is_BL_Address label then
            (term_to_string o snd o gen_dest_Imm o dest_BL_Address) label
          else
            raise ERR "convert_inout_to_graphviz" "label type unknown";
      in
        (i,node_shape_default,[("id",label_str)])
      end;

    fun listcontains l x = List.exists (fn y => y = x) l;

    fun edge_fold_fun ((ins,outs), (nodes_aux,edges,i,i_aux)) =
      if not (listcontains idxs_sel i) then (nodes_aux,edges,i+1,i_aux) else
      let
        val (nodes_aux,edges,i_aux) =
          if ins = [] then
            ((i_aux,node_shape_point,[])::nodes_aux, (i_aux,i)::edges, i_aux+1)
            (* (nodes_aux,edges,i_aux) *)
          else
            (nodes_aux,edges,i_aux);
        val (nodes_aux,edges,i_aux) = List.foldl (fn (in_idx,(nodes_aux,edges,i_aux)) =>
            if in_idx = (~1) then
              ((i_aux,node_shape_circle,[("id", "???")])::nodes_aux,(i_aux,i)::edges,i_aux+1)
            else
              (nodes_aux,edges,i_aux)
          ) (nodes_aux,edges,i_aux) ins;
        val (nodes_aux,edges,i_aux) = List.foldl (fn (out_idx,(nodes_aux,edges,i_aux)) =>
            if out_idx = (~1) then
              ((i_aux,node_shape_circle,[("id", "???")])::nodes_aux,(i,i_aux)::edges,i_aux+1)
            else
              (nodes_aux,(i,out_idx)::edges,i_aux)
          ) (nodes_aux,edges,i_aux) outs;
      in
        (nodes_aux,edges,i+1,i_aux)
      end;

    val blocks_sel = List.foldl (fn (i,l) => (i,List.nth(blocks,i))::l) [] idxs_sel;
    val nodes_base = List.map block_to_node blocks_sel;

    val num_idxs = length blocks;
    val inout_idxs = List.map (fn (i,(ins,outs)) =>
          if not (listcontains idxs_sel i) then
            ([],[])
          else
            (List.map (fn x => if (listcontains ((~1)::idxs_sel) x) then x else (~1)) ins,
             List.map (fn x => if (listcontains ((~1)::idxs_sel) x) then x else (~1)) outs)
      ) (ziplist (List.tabulate(num_idxs, fn x => x)) (ziplist in_idxs out_idxs));

    val (nodes_aux, edges,_,_) = List.foldl edge_fold_fun ([],[],0,num_idxs) inout_idxs;
  in
    (nodes_aux @ nodes_base, edges)
  end;

fun convert_inout_to_graphviz_all (blocks,in_idxs,out_idxs) =
  convert_inout_to_graphviz
    (List.tabulate(length blocks, fn x => x))
    (blocks,in_idxs,out_idxs);

(*---------------------------------------------------------------------------*)

fun bir_export_graph_inout simplified nodes g path =
  let
    val (nodes, edges) = convert_inout_to_graphviz nodes g;
    val (nodes, edges) = if simplified then simplify_graph (nodes, edges) else (nodes, edges);

    val path = if (String.size (OS.Path.dir path)) = 0 then ("./" ^ path) else path;
    val dirname = OS.Path.dir path;
    val _ = OS.FileSys.isDir dirname handle SysErr(_) => (OS.FileSys.mkDir dirname; true);

    val dot_str = gen_graph (nodes, edges);
    val _ = writeToFile dot_str path;
  in
    ()
  end;

fun bir_export_graph_inout_all simplified (blocks, in_idxs, out_idxs) path =
  bir_export_graph_inout
    simplified
    (List.tabulate (length blocks, fn x => x))
    (blocks, in_idxs, out_idxs)
    path;

(*---------------------------------------------------------------------------*)

fun bir_show_graph_inout simplified nodes g =
  let
    val path = "tempdir/temp_file_" ^ (LargeInt.toString (Time.toMilliseconds (Time.now ())));
    val _ = bir_export_graph_inout simplified nodes g (path ^ ".dot");
    val _ = convertAndView path;
  in
    ()
  end;

fun bir_show_graph_inout_all simplified (blocks, in_idxs, out_idxs) =
  bir_show_graph_inout
    simplified
    (List.tabulate (length blocks, fn x => x))
    (blocks, in_idxs, out_idxs);

(*---------------------------------------------------------------------------*)

fun bir_export_graph_from_prog prog path =
  let
    val blocks = (fst o dest_list o dest_BirProgram) prog;
    val (_, in_idxs, out_idxs) = cfg_compute_inoutedges_as_idxs blocks;
    val simplified = false;
  in
    bir_export_graph_inout_all simplified (blocks, in_idxs, out_idxs) path
  end;

fun bir_show_graph_from_prog prog path =
  let
    val blocks = (fst o dest_list o dest_BirProgram) prog;
    val (_, in_idxs, out_idxs) = cfg_compute_inoutedges_as_idxs blocks;
    val simplified = false;
  in
    bir_show_graph_inout_all simplified (blocks, in_idxs, out_idxs)
  end;

end (* local *)

end (* bir_old_cfgVizLib *)
