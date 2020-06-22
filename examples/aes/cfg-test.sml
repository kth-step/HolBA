open HolKernel Parse;

open aesBinaryTheory;

open listSyntax;


open bir_old_cfgLib;
open bir_old_cfgVizLib;


(*
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 1;
*)

(*
toy_m0_program_THM
aes_m0_program_THM
aes_arm8_program_THM
*)
val liftertheorem = aes_m0_program_THM;

val printgraphs = true;
val printsimple = true;

val prog = ((snd o dest_comb o concl) liftertheorem);
val blocks = (fst o dest_list o dest_BirProgram) prog;

(*
val block = hd blocks;
*)

val (_,in_idxs,out_idxs) = cfg_compute_inoutedges_as_idxs blocks;

(*
length blocks
val _ = bir_show_graph_inout_all false (blocks,in_idxs,out_idxs);



val blocks = List.tabulate (9, fn x => ``<|bb_label := BL_Address (Imm32 ^(wordsSyntax.mk_word(Arbnum.fromInt x, Arbnum.fromInt 32)));
   bb_statements :=
     [];
   bb_last_statement :=
     BStmt_Jmp (BLE_Label (BL_Address (Imm32 33030w)))|>``);
val in_idxs  = [[],[0],[0],[1,2,6],[8],[4],[4],[3],[7]];
val out_idxs = [[1,2],[3],[3],[7],[5,6],[~1],[3],[8],[4]];

is_reachable [4,3] [5,4] 2

*)

val _ = if printgraphs then bir_show_graph_inout_all printsimple (blocks,in_idxs,out_idxs) else ();




val conn_comps = find_conn_comp (blocks, in_idxs, out_idxs);
val _ = print ("number of connected components: " ^ (Int.toString (length conn_comps)) ^ "\n");
(*
List.foldl (fn ((x,_,_),l) => l + length x) 0 conn_comps
*)

(*
val _ = List.map (fn (nodes,_,_) => bir_show_graph_inout true nodes (blocks, in_idxs, out_idxs)) conn_comps;
*)


(*
val frags = divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps;
val num_frags = length frags;


(*
List.foldl (fn (x,l) => l + length x) 0 frags
*)

val _ = List.map (fn nodes => bir_show_graph_inout true nodes (blocks, in_idxs, out_idxs)) frags;
*)



val lf_frags = divide_loopfree_fragments (blocks, in_idxs, out_idxs) conn_comps;
val num_lf_frags = length lf_frags;
val _ = print ("number of loop free fragments: " ^ (Int.toString num_lf_frags) ^ "\n");

val _ = if (length blocks) = (List.foldl (fn ((x,_,_),l) => l + length x) 0 lf_frags) then ()
        else raise Fail "Something is fishy: incorrect number of blocks";

(*
List.foldl (fn ((x,_,_),l) => l + length x) 0 lf_frags

List.map (fn (_,x,y) => (blocks_to_labels (List.map (fn x => List.nth(blocks,x)) x), blocks_to_labels (List.map (fn x => List.nth(blocks,x)) y))) lf_frags
*)

val _ = if printgraphs then
          (List.map (fn (nodes,_,_) => bir_show_graph_inout printsimple nodes (blocks, in_idxs, out_idxs)) lf_frags; ())
        else ();
