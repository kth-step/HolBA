open HolKernel Parse;

open listSyntax;

open binariesTheory;
open bir_cfgLib;

open bir_wpTheory bir_wpLib;




val prog_thms = [
  ("arm8", "aes"    , aes_arm8_program_THM),
  ("m0"  , "aes"    , aes_m0_program_THM)(*,
  ("arm8", "bignum" , bignum_arm8_program_THM),
  ("m0"  , "bignum" , bignum_m0_program_THM),
  ("arm8", "wolfssl", wolfssl_arm8_program_THM),
  ("m0"  , "wolfssl", wolfssl_m0_program_THM)
*)
];


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 0;





(*

mkdir tempdir
cd tempdir

*)





val (arch_str, example_str, prog_thm) = hd prog_thms;
val prog = ((snd o dest_comb o concl) prog_thm);
val blocks = (fst o dest_list o dest_BirProgram) prog;

val g = cfg_compute_inoutedges_as_idxs blocks;

val conn_comps = find_conn_comp g;

val frags = divide_linear_fragments g conn_comps;
val num_frags = length frags;
val max_frag_size = List.foldl (fn (l,m) => Int.max(length l,m)) 0 frags;

val _ = print ("\n" ^ example_str ^ " - " ^ arch_str ^ ":\n");
val _ = print ((Int.toString num_frags) ^ " fragments\n");
val _ = print ((Int.toString max_frag_size) ^ " max frag size\n\n");
val _ = print "\n";

val frag = (hd o tl o tl) frags;

val theory_name = "abcd" ^ "34454352";

val _ = new_theory theory_name;

(* select only fragment blocks, and last block label *)
fun select_blocks_from_prog frag prog =
  let
    val (blocks,ty) = (dest_list o dest_BirProgram) prog;
    val (_,blocks_sel) = List.foldl (fn (b,(i,l)) => (i+1,if List.exists (fn x => x = i) frag then b::l else l)) (0,[]) blocks;
    val blocks_sel = List.rev blocks_sel;

    val eval_label = (snd o dest_eq o concl o EVAL);
    val last_block = List.last blocks_sel;
    val (raw_BL_term, _, _) = dest_bir_block last_block;
    val BL_term = eval_label raw_BL_term;

    val program = (mk_BirProgram o mk_list) (blocks_sel,ty);
    val last_block_label = BL_term;
  in
    (program,last_block_label)
  end;

val (program,last_block_label) = select_blocks_from_prog frag prog;


val ex_program_def = Define `
      ex_program = ^program
`;
val ex_post_def = Define `
      ex_post = (BExp_Const (Imm1 1w))
`;
val ex_ls_def = Define `
      ex_ls = \x.(x = ^last_block_label)
`;
val ex_wps_def = Define `
      ex_wps = (FEMPTY |+ (^last_block_label, ex_post))
`;



val ex_program = ``ex_program``;
val ex_post = ``ex_post``;
val ex_ls = ``ex_ls``;
val ex_wps = ``ex_wps``;

val defs = [ex_program_def, ex_post_def, ex_ls_def, ex_wps_def];



(* wps_bool_sound_thm for initial wps *)
val prog_term = (snd o dest_comb o concl) ex_program_def;
val wps_term = (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) ex_wps;
val wps_bool_sound_thm = bir_wp_init_wps_bool_sound_thm (ex_program, ex_post, ex_ls) ex_wps defs;
val (wpsdom, blstodo) = bir_wp_init_rec_proc_jobs prog_term wps_term;



(* prepare "problem-static" part of the theorem *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (ex_program, ex_post, ex_ls) defs;


val (wps1, wps1_bool_sound_thm) = bir_wp_comp_wps prog_thm ((ex_wps, wps_bool_sound_thm), (wpsdom, List.rev blstodo)) (ex_program, ex_post, ex_ls) defs;



val aes_wps1_def = Define `
      aes_wps1 = ^wps1
`;

val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;
val _ = save_thm("aes_wps1_bool_sound_thm", wps1_bool_sound_thm_readable);



val _ = export_theory();
