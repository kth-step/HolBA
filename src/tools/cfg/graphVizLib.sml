structure graphVizLib =
struct

local

open HolKernel Parse boolLib bossLib;

val ERR = mk_HOL_ERR "graphVizLib";

in

(*
 ----------------------------------------
        node naming convention
 ----------------------------------------
 *)
fun index_to_node_name idx = "n_" ^ (Int.toString idx);

(*
 ----------------------------------------
        nodes
 ----------------------------------------
 *)
fun gen_node_label_line (id, contents) = id ^ ": " ^ contents ^ "\\l";
fun gen_node_label lines =
  let
    val lines_strs = List.map gen_node_label_line lines;
    val str = List.foldl (fn (x,y) => y ^ x) "" lines_strs;
  in
    str
  end;

val node_shape_default = "";
val node_shape_doublecircle = "doublecircle";
val node_shape_circle = "circle";
val node_shape_point = "point";

fun gen_node (idx, shape, label_lines) =
  let
    val name = index_to_node_name idx;
    val shape_str = if shape = "" then "" else ("shape = " ^ shape ^ ", ");
    val label_str = gen_node_label label_lines;
  in
    "  " ^ name ^ "  " ^
    "[" ^ shape_str ^ "label=\"" ^ label_str ^ 
             "\"]\r\n"
  end;

fun gen_nodes nodes =
  let
    val nodes_strs = List.map gen_node nodes;
    val str = List.foldr (fn (x,y) => y ^ x ^ "\r\n\r\n") "" nodes_strs;
  in
    str
  end;


(*
 ----------------------------------------
        edges
 ----------------------------------------
 *)
fun gen_edge (idx_i, idx_j) =
  let
    val node_name_i = index_to_node_name idx_i;
    val node_name_j = index_to_node_name idx_j;
  in
    node_name_i ^ " -> " ^ node_name_j
  end;

fun gen_edges edges =
  let
    val edges_strs = List.map gen_edge edges;
    val str = List.foldl (fn (x,y) => y ^ x ^ "\r\n") "" edges_strs;
  in
    str
  end;



(*
 ----------------------------------------
        graph
 ----------------------------------------
 *)
fun gen_graph (nodes, edges) =
  let
    val s1 = "digraph L {\r\n\r\n  node [shape=record fontname=Arial];\r\n\r\n";
    val s2 = gen_nodes nodes;
    val s3 = "\r\n";
    val s4 = gen_edges edges;
    val s5 = "\r\n}\r\n";
  in
    s1 ^ s2 ^ s3 ^ s4 ^ s5
  end;



fun simplify_graph (nodes, edges) =
  let
    fun isSpecialNode i =
         let
           val ins = List.foldl (fn ((x,y),l) => if y = i then x::l else l) [] edges;
           val outs = List.foldl (fn ((x,y),l) => if x = i then y::l else l) [] edges;
         in
           (not (length outs = 1 andalso length ins = 1)) orelse
           (let
              val (_,in_shape,_) = case List.find (fn (i,_,_) => i = hd ins) nodes of
				       NONE => raise ERR "simplify_graph" "unexpected error"
				     | SOME x => x;
              val (_,out_shape,_) = case List.find (fn (i,_,_) => i = hd outs) nodes of
				       NONE => raise ERR "simplify_graph" "unexpected error"
				     | SOME x => x;
            in
              in_shape <> node_shape_default orelse out_shape <> node_shape_default
            end)
         end;
    val nodes = List.filter (fn (i,_,_) =>
         let
           val ins = List.foldl (fn ((x,y),l) => if y = i then x::l else l) [] edges;
           val outs = List.foldl (fn ((x,y),l) => if x = i then y::l else l) [] edges;
         in
           isSpecialNode i orelse isSpecialNode (hd ins)
         end
      ) nodes;

    val _ = if nodes <> [] then () else raise ERR "simplify_graph" "the fragment is only one loop, cannot be simplified at the moment";

    fun nodeExists x = (List.exists (fn (i,_,_) => i = x) nodes);
(*
    fun findNexts acc x = if nodeExists x then (x,acc) else
      let
        val SOME (_,y) = List.find (fn (z,_) => x = z) edges;
      in
        findNexts (acc+1) y
      end;
*)
    fun findNexts acc x =
      let
        val (_,y) = case List.find (fn (z,_) => x = z) edges of
		        NONE => raise ERR "simplify_graph" "unexpected error"
		      | SOME x => x;
      in
        if nodeExists y then (y,acc)
        else findNexts (acc+1) y
      end;
    val findNext = fst o (findNexts 0);
    val numMissing = snd o (findNexts 1);

    val nodes = List.map (fn (i,s,ls) => (i,s,
      let
        val outs = List.foldl (fn ((x,y),l) => if x = i then y::l else l) [] edges;
      in
        if length outs = 1 andalso not (nodeExists (hd outs)) then
          ls @ [("CUTOUT", Int.toString (numMissing (hd outs)))]
        else
          ls
      end)) nodes;

    val edges = List.foldl (fn ((x,y),edges) =>
        if nodeExists x then
          if nodeExists y then
            (x,y)::edges
          else
            (x,findNext y)::edges
        else
          edges
      ) [] edges;
  in
    (nodes, edges)
  end;



(*
fun generateDot nodes =
  let
    val s1 = "digraph L {\r\n\r\n  node [shape=record fontname=Arial];\r\n\r\n";
    val s2 = node_to_dot 0 (CFGSIMP_node ((Arbnum.fromInt 0x77), (Arbnum.fromInt 0x100), 6, []))(*"  a_0  [label=\"a \\l abc \\l abc \\l\"]\r\n"*);
    val s3 = "\r\n";
    val s4 = "n_0 -> n_0\r\n";
    val s5 = "\r\n}\r\n";
  in
    s1 ^ s2 ^ s3 ^ s4 ^ s5
  end;
 *)



(*
 ----------------------------------------
        writing to file and conversion
 ----------------------------------------
 *)
fun writeToFile str file_name =
  let
    val outstream = TextIO.openOut file_name;
    val _ = TextIO.output (outstream, str) before TextIO.closeOut outstream;
  in
    () 
  end;

fun convertAndView file =
  let
    val dotfile = (file ^ ".dot");
    val tempfile = (file ^ ".ps");
    val _ = OS.Process.system ("dot " ^ dotfile ^ " -Tps -o " ^ tempfile);
    val _ = OS.Process.system ("xdg-open " ^ tempfile ^ " > /dev/null 2>/dev/null");
  in
    ()
  end;



(*
 ----------------------------------------
        test
 ----------------------------------------
 *)
(*
val nodes = [(0,node_shape_default,[("id","abc"),("len","12")]),
             (1,node_shape_default,[("id","def"),("len","22")]),
             (2,node_shape_point,[]),
             (3,node_shape_circle,[("id","???")]),
             (4,node_shape_default,[("id","aaa")]),
             (5,node_shape_default,[("id","bbb")])];
val edges = [(2,0),
             (0,4),
             (4,5),
             (5,1),
             (1,1),
             (1,3)];


val (nodes, edges) = simplify_graph (nodes, edges);

val file = "test";
val dot_str = gen_graph (nodes, edges);
val _ = writeToFile dot_str (file ^ ".dot");
val _ = convertAndView file;
*)

end (* local *)

end (* graphVizLib *)
