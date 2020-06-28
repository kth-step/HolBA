structure binariesCfgVizLib =
struct
local

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;

open graphVizLib;

open bir_cfg_vizLib;
open bir_fileLib;

in (* local *)

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

    val file = get_tempfile "cfg_" "nil";
    val dot_str = gen_graph (nodes, edges);
    val _ = writeToFile dot_str (file ^ ".dot");
    val _ = convertAndView file;
  in () end;

fun show_call_graph () =
  display_call_graph ci symbs_sec_text;

fun show_cfg_fun do_walk bl_dict n_dict name =
  let
    val lbl_tms = if do_walk then
                    (#CFGG_nodes o (build_fun_cfg bl_dict n_dict)) name
                  else
                     List.filter ((fn s => s = name) o lbl_tm_to_rel_symbol) (List.map fst (Redblackmap.listItems n_dict));
    val ns = List.map (find_node n_dict) lbl_tms;
  in
    cfg_display_graph_ns ns
  end;

fun print_fun_pathstats with_histogram n_dict name =
  let
    val (n_paths, sum_calls) = count_paths_to_ret false n_dict [] (mem_symbol_to_prog_lbl name);
    val n_calls = length sum_calls;
    val histo_calls = to_histogram sum_calls;

    val _ = print ("fun " ^ name ^ " : " ^ (Int.toString n_paths) ^
                                   ", calls " ^ (Int.toString n_calls) ^ "\n");
    val _ = if not with_histogram then () else
            (List.map (fn (s, k) => print (" - " ^ s ^ " =\t" ^ (Int.toString k) ^ "\n")) histo_calls; ());
  in
    ()
  end;

fun print_dead_code bl_dict n_dict name =
  let
    val g  = build_fun_cfg bl_dict n_dict name;
    val lbls_f = List.filter ((fn s => s = name) o lbl_tm_to_rel_symbol)
                           (List.map fst (Redblackmap.listItems n_dict));

    val _ = print ("---------------------\n");
    val dead_code = (List.filter (fn x => not (List.exists (fn y => x = y) (#CFGG_nodes g))) lbls_f);

    val _ = print ("dead code (" ^ name ^ "):\n^^^^^^^^^^^^^^^^^^\n");
    val _ = List.map (fn n => (print_term (#CFGN_lbl_tm n);
                               print ((valOf (#CFGN_hc_descr n) handle Option => "NONE") ^ "\n")))
                     (List.map (find_node n_dict) dead_code);
  in
    ()
  end;

end (* local *)
end (* struct *)
