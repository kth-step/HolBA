open HolKernel Parse;

open aesBinaryTheory;

open listSyntax;
open bir_immSyntax;

open graphVizLib;
open bir_cfgLib;


(*
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 1;
*)

val aes_prog = ((snd o dest_comb o concl) aes_arm8_program_THM);
val aes_blocks = (fst o dest_list o dest_BirProgram) aes_prog;

val blocks = aes_blocks;

(*
length blocks
val block = hd blocks;
*)

val (_,in_idxs,out_idxs) = cfg_compute_inoutedges_as_idxs blocks;

val eval_label = (snd o dest_eq o concl o EVAL);

fun ziplist [] [] = []
  | ziplist (x::xs) (y::ys) = (x,y)::(ziplist xs ys)
  | ziplist _ _ = raise ERR "ziplist" "list length doesn't match";

fun unziplist [] = ([],[])
  | unziplist ((x,y)::xys) = let val (xs,ys) = unziplist xys; in (x::xs,y::ys) end;

fun convert_inout_to_graphviz (blocks,in_idxs,out_idxs) =
  let
    fun node_fold_fun (block, (nodes,i)) =
      let
        val (raw_BL_term, _, _) = dest_bir_block block;
        val label = eval_label raw_BL_term;
        val label_str = if is_BL_Label label then
                      dest_BL_Label_string label
                    else if is_BL_Address label then
                      (term_to_string o snd o gen_dest_Imm o dest_BL_Address) label
                    else
                      raise ERR "convert_inout_tographviz" "label type unknown";
(*        val label_str = (term_to_string o eval_label) raw_BL_term;*)
        val node = (i,node_shape_default,[("id", label_str)]);
      in
        (node::nodes,i+1)
      end;

    fun edge_fold_fun ((ins,outs), (nodes_aux,edges,i,i_aux)) =
      let
        val (nodes_aux,edges,i_aux) =
          if ins = [] then
            ((i_aux,node_shape_point,[])::nodes_aux, (i_aux,i)::edges, i_aux+1)
          else
            (nodes_aux,edges,i_aux);
        val (nodes_aux,edges,i_aux) = List.foldl (fn (out_idx,(nodes_aux,edges,i_aux)) =>
            if out_idx = (~1) then
              ((i_aux,node_shape_circle,[("id", "???")])::nodes_aux,(i,i_aux)::edges,i_aux+1)
            else
              (nodes_aux,(i,out_idx)::edges,i_aux)
          ) (nodes_aux,edges,i_aux) outs;
      in
        (nodes_aux,edges,i+1,i_aux)
      end;

    val (nodes_base,_) = List.foldl node_fold_fun ([],0) blocks;
    val num_idxs = length blocks;
    val (nodes_aux, edges,_,_) = List.foldl edge_fold_fun ([],[],0,num_idxs) (ziplist in_idxs out_idxs);
  in
    (nodes_aux @ nodes_base, edges)
  end;

(*
val (nodes, edges) = convert_inout_to_graphviz (blocks,in_idxs,out_idxs);
val (nodes, edges) = simplify_graph (nodes, edges);
val file = "test";
val dot_str = gen_graph (nodes, edges);
val _ = writeToFile dot_str (file ^ ".dot");
val _ = convertAndView file;
*)


val conn_comps = find_conn_comp (blocks, in_idxs, out_idxs);



val frags = divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps;




