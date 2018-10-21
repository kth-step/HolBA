
structure bir_cfgLib =
struct

(*
=================================================================
              translate to edge by node list
=================================================================
 *)
val eval_label = (snd o dest_eq o concl o EVAL);

fun find_idxs P xs =
  let
    fun find_idx_acc _ _ [] = []
      | find_idx_acc P a (x::xs) = if P x then a::(find_idx_acc P (a+1) (xs)) else (find_idx_acc P (a+1) (xs))
    ;
  in
    find_idx_acc P 0 xs
  end;

fun find_idx P xs =
  let
    val idxs = find_idxs P xs;
  in
    if idxs = [] then ~1 else hd idxs
  end;

val blocks_to_labels = List.map (fn block =>
    let
      val (raw_BL_term, _, _) = dest_bir_block block;
      val BL_term = eval_label raw_BL_term;
    in
      BL_term
    end
  );

fun block_to_outidxs labels block =
  let
    val (_, _, last_stmt) = dest_bir_block block;
    val raw_targets =
      if is_BStmt_Jmp last_stmt then
        [dest_BStmt_Jmp last_stmt]
      else if is_BStmt_CJmp last_stmt then
        let
          val (_,j1,j2) = dest_BStmt_CJmp last_stmt;
        in
          [j1, j2]
        end
      else if is_BStmt_Halt last_stmt then
        []
      else
        raise ERR "block_to_outidxs" "unknown end statement"
      ;
(*
(print ("\nooops:"^(term_to_string l)^"\n");ls)
*)
    
    fun find_target_idx y = find_idx (fn x => x=y) labels;
    val targets = List.foldl (fn (l,ls) =>
          if is_BLE_Label l then
            ((find_target_idx o eval_label o dest_BLE_Label) l)::ls
          else
            (~1)::ls (* if is is an expression the jump target is unknown *)
      ) [] raw_targets;
    (* we could filter out the entry points from the symbol table *)
    (* here we can only find matches if the targets are in the program *)
    (*val targets = List.map (eval_label) proc_targets;*)
  in
    targets
  end;

fun cfg_compute_outedges_as_idxs blocks =
  let
    val labels = blocks_to_labels blocks;
    val out_idxs = List.map (block_to_outidxs labels) blocks;
  in
    (blocks, out_idxs)
  end;

fun cfg_compute_inedges_as_idxs (blocks, out_idxs) =
  let
    val in_idxs = List.tabulate (length out_idxs, fn i => find_idxs (fn is => List.exists (fn x => x=i) is) out_idxs);
  in
    (blocks, in_idxs, out_idxs)
  end;

val cfg_compute_inoutedges_as_idxs = cfg_compute_inedges_as_idxs o cfg_compute_outedges_as_idxs;



(*

val (_,out_idxs) = cfg_compute_outedges_as_idxs blocks;
val (_,in_idxs,_) = cfg_compute_inedges_as_idxs (blocks, out_idxs);

val (_,in_idxs,out_idxs) = cfg_compute_inoutedges_as_idxs blocks;

*)


(*
    could be visualized already now (graphviz lib)
 *)


(*
=================================================================
            find connected components
=================================================================
 *)

fun find_conn_comp (blocks, in_idxs, out_idxs) =
  let
    val exit_nodes = find_idxs (fn is => List.exists (fn x => x=(~1)) is) out_idxs;
    fun process_conccomp [] acc = acc
      | process_conccomp (n::ns) (nodes, entries, exits) =
           let
             val ins = List.nth(in_idxs,n);
             val outs = List.nth(out_idxs,n);
             val outs_filt = List.filter (fn x => x <> (~1)) outs;

             val new_entries = if ins = [] then (n::entries) else entries;
             val new_exits   = if outs <> outs_filt then (n::exits) else exits;

             val new_ns_0 = (List.filter (fn x => not (List.exists (fn y => y = x) (ns@nodes)))
                               ins) @ ns;
             val new_ns_1 = (List.filter (fn x => not (List.exists (fn y => y = x) (ns@nodes)))
                               outs_filt) @ new_ns_0;
           in
             process_conccomp new_ns_1 (n::nodes, new_entries, new_exits)
           end;
    fun process_conccomps [] acc = acc
      | process_conccomps (n::exit_nodes) acc =
           let
             val conn_comp = process_conccomp [n] ([],[],[]);
             val (_,_,conn_comp_exits) = conn_comp;
             val new_exit_nodes = List.filter (fn x => not (List.exists (fn y => x = y) conn_comp_exits)) exit_nodes;
           in
             process_conccomps (new_exit_nodes) (conn_comp::acc)
           end;
    val conncomp = process_conccomps exit_nodes [];
    (* verify that all nodes are captures in the connected components *)
  in
    conncomp
  end;

(*
val conn_comps = find_conn_comp (blocks, in_idxs, out_idxs);
*)


(*
=================================================================
            divide into linear fragments
=================================================================
 *)

fun divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps =
  let
    fun process_frag n acc =
      let
        val new_acc = n::acc;
        val ins = List.nth(in_idxs,n);
        val is_split = (length ins = 0) orelse
                       (length ins > 1) orelse
                       (length ins = 1 andalso (length (List.nth(out_idxs,hd ins)) > 1))
      in
        if is_split then new_acc else process_frag (hd ins) new_acc
      end;

    fun process_frags [] _ acc = acc
      | process_frags (n::ns) visited acc =
          let
            val new_frag = process_frag n [];
            val new_visited = new_frag @ visited;

            val ins = List.nth(in_idxs,hd new_frag);
            val new_ns = (List.filter (fn x => not (List.exists (fn y => y = x) (ns@new_visited)))
                            ins) @ ns;
          in
            process_frags new_ns new_visited (new_frag::acc)
          end;

    fun process_comp_frags (_, _, exits) =
      process_frags exits [] [];
  in
    List.foldl (fn (c,fs) => (process_comp_frags c)@fs) [] conn_comps
  end;

(*
val frags = divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps;
*)


(*
=================================================================
            divide into loop-free fragments
=================================================================
 *)

fun divide_loopfree_fragments (blocks, in_idxs, out_idxs) conn_comps =
  let
    fun prep_frag_todo_for_compnent c =
      List.map (fn frag =>
        let
          val entries = List.filter (fn z => (List.nth(in_idxs,z)) = [] orelse not (List.all (fn x => List.exists (fn y => x = y) frag) (List.nth(in_idxs,z)))) frag;
          val exits = List.filter (fn z => not (List.all (fn x => (List.exists (fn y => x = y) frag)) (List.nth(out_idxs,z)))) frag;
          val _ = if entries = [hd frag] andalso exits = [List.last frag] then ()
                  else raise ERR "prep_frag_todo_for_compnent" "something is fishy";
        in
          (frag, entries, exits)
        end) (divide_linear_fragments (blocks, in_idxs, out_idxs) [c]);

    fun is_reachable nodes outs n =
      if List.exists (fn x => x = n) outs then true else
      let
        val n_outs = List.filter (fn x => List.exists (fn y => x = y) nodes) (List.nth(out_idxs,n));
      in
        List.exists (fn x => is_reachable nodes outs x) n_outs
      end;

    fun merge_frags (ns_1,en_1,ex_1) (ns_2,en_2,ex_2) =
      let
        val ins_2 = List.foldl (fn (en,l) => List.foldl (fn (x,l) => if List.exists (fn y => x = y) l then l else (x::l)) l (List.nth(in_idxs,en))) [] en_2;
        val outs_2 = List.foldl (fn (ex,l) => List.foldl (fn (x,l) => if List.exists (fn y => x = y) l then l else (x::l)) l (List.nth(out_idxs,ex))) [] ex_2;

        val connects_in = List.exists (fn x => List.exists (fn y => x = y) ins_2) ex_1;
        val connects_out = List.exists (fn x => List.exists (fn y => x = y) outs_2) en_1;

	val createscircle = connects_in andalso
			    connects_out andalso
			    (List.exists (fn x => is_reachable ns_1 ins_2 x)
					 (List.filter (fn x => List.exists (fn y => x = y) ns_1) outs_2)
			    );

        val mergable = (not createscircle) andalso (connects_in orelse connects_out);
      in
        if not mergable then NONE else SOME (
          let
	  val new_nodes = ns_2 @ ns_1;

	  val new_entries = List.filter (fn z => (List.nth(in_idxs,z)) = [] orelse not (List.all (fn x => List.exists (fn y => x = y) new_nodes) (List.nth(in_idxs,z)))) new_nodes;
	  val new_exits = List.filter (fn z => not (List.all (fn x => (List.exists (fn y => x = y) new_nodes)) (List.nth(out_idxs,z)))) new_nodes;
                (*
                val (new_entries,new_exits) = if isgluedin andalso connects_out then ((
                    List.filter (fn x =>
                        let
                          val x_ins = List.nth(in_idxs,x);
                        in
                          (not (List.exists (fn y => ex = y) x_ins)) orelse
                          (List.exists (fn y => not (List.exists (fn z => z = y) new_nodes)) x_ins)
                        end
                      ) (en::entries)
                  ),exits) else (entries,exits);

                val (new_entries,new_exits) = if isgluedin andalso connects_in then (new_entries,(
                    List.filter (fn x =>
                        let
                          val x_outs = List.nth(out_idxs,x);
                        in
                          (not (List.exists (fn y => en = y) x_outs)) orelse
                          (List.exists (fn y => not (List.exists (fn z => z = y) new_nodes)) x_outs)
                        end
                      ) (List.foldl () (ex::new_exits) ins)
                  )) else (new_entries,new_exits);
                *)
          in
            (new_nodes,new_entries,new_exits)
          end
          )
      end;

    fun merge_fragl l _ [] = NONE
      | merge_fragl l frag1 (frag2::fs) =
          case merge_frags frag1 frag2 of
	      NONE          => merge_fragl (frag2::l) frag1 fs
	    | SOME new_frag => SOME (l @ (new_frag::fs));

    fun merge_through l [] = NONE
      | merge_through l (frag::fs) =
          case merge_fragl l frag fs of
	      NONE => merge_through (frag::l) fs
	    | x    => x;

    fun process_comp_frags fs =
          case merge_through [] fs of
	      NONE        => fs
	    | SOME new_fs => process_comp_frags new_fs;

  in
    List.concat (List.map (fn c => process_comp_frags (prep_frag_todo_for_compnent c)) conn_comps)
  end;


(*
val conn_comps = tl conn_comps;
val frags = divide_loopfree_fragments (blocks, in_idxs, out_idxs) conn_comps;

val c = hd conn_comps;
val todo = prep_frag_todo_for_compnent c;
(divide_linear_fragments (blocks, in_idxs, out_idxs) [c])
val frags = process_comp_frags [] [];

val frags =[([0,1,3],[0],[3])]
val ((ns,en,ex)::todo) = [([2],2,2)]
val (nodes,entries,exits) = hd frags
process_comp_frags frags ((ns,en,ex)::todo)

*)


end

