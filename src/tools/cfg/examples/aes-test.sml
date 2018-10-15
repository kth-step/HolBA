open HolKernel Parse;

open aesBinaryTheory;

open listSyntax;



(*
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 1;
*)

val aes_prog = ((snd o dest_comb o concl) aes_arm8_program_THM);
val aes_blocks = (fst o dest_list o dest_BirProgram) aes_prog;

(*
length aes_blocks
val blocks = aes_blocks;
val block = hd blocks;
*)



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


