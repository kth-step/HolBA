open HolKernel Parse;

open aesBinaryTheory;

open listSyntax;


open bir_cfgLib;
open bir_cfgVizLib;


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

val _ = bir_show_graph_inout_all true (blocks,in_idxs,out_idxs);




val conn_comps = find_conn_comp (blocks, in_idxs, out_idxs);

val _ = List.map (fn (nodes,_,_) => bir_show_graph_inout true nodes (blocks, in_idxs, out_idxs)) conn_comps;




val frags = divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps;

val num_frags = length frags;

val _ = List.map (fn nodes => bir_show_graph_inout true nodes (blocks, in_idxs, out_idxs)) frags;



