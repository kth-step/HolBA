open HolKernel Parse;

open aesBinaryTheory;

open listSyntax;

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



val conn_comps = find_conn_comp (blocks, in_idxs, out_idxs);



val frags = divide_linear_fragments (blocks, in_idxs, out_idxs) conn_comps;




