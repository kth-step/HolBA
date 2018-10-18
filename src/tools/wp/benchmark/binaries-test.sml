open HolKernel Parse;

open listSyntax;

open binariesTheory;
open bir_cfgLib;
open bir_cfgVizLib;

open bir_wpTheory bir_wpLib;




val configurations = [
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




(* export the theories to a temporary directory *)
val dirname = "tempdir";
val _ = OS.FileSys.isDir dirname handle SysErr(_) => (OS.FileSys.mkDir dirname; true);
val _ = OS.FileSys.chDir ("./" ^ dirname);




(* iterate over all configurations *)
val _ = List.foldl (fn (config,_) =>
  let
    val (arch_str, example_str, prog_thm) = config;
    (*
    val (arch_str, example_str, prog_thm) = hd configurations;
    val (arch_str, example_str, prog_thm) = ("m0"  , "aes"    , aes_m0_program_THM);
    *)

    val prog = ((snd o dest_comb o concl) prog_thm);
    val blocks = (fst o dest_list o dest_BirProgram) prog;

    val g = cfg_compute_inoutedges_as_idxs blocks;
    (*
    val _ = bir_show_graph_inout_all true g;
    val _ = bir_show_graph_inout_all false g;
    *)

    val conn_comps = find_conn_comp g;
    (*
    val _ = List.map (fn (nodes,_,_) => bir_show_graph_inout true nodes g) conn_comps;
    *)

    val frags = divide_linear_fragments g conn_comps;
    val num_frags = length frags;
    val max_frag_size = List.foldl (fn (l,m) => Int.max(length l,m)) 0 frags;

    val _ = print ("\n" ^ example_str ^ " - " ^ arch_str ^ ":\n");
    val _ = print ((Int.toString num_frags) ^ " fragments\n");
    val _ = print ((Int.toString max_frag_size) ^ " max frag size\n\n");
    val _ = print "\n";


    val theory_name_prefix = example_str ^ "_" ^ arch_str ^ "_";
    (* remove all temporary theories with this prefix *)
    val _ = OS.Process.system ("rm " ^ theory_name_prefix ^ "*");


    (* iterate over all fragments *)
    val _ = List.foldl (fn (frag,frag_i) =>
      let
	(*
	val frag_i = 0;
	val frag = List.nth (frags,0);
	val frag_i = 1;
	val frag = List.nth (frags,1);
	*)

        (*
        val _ = bir_show_graph_inout true frag g;
        val _ = bir_show_graph_inout false frag g;
        *)

	val theory_name = theory_name_prefix ^ (Int.toString frag_i);

	val _ = new_theory theory_name;

	(* select only fragment blocks, and last block label *)
	fun select_blocks_from_prog frag prog =
	  let
	    val (blocks,ty) = (dest_list o dest_BirProgram) prog;
	    val (_,blocks_sel) = List.foldl (fn (b,(i,l)) => (i+1,if List.exists (fn x => x = i) frag then b::l else l)) (0,[]) blocks;
	    val blocks_sel = List.rev blocks_sel;

	    val eval_label = (snd o dest_eq o concl o EVAL);
	    val last_block = List.nth(blocks,(List.last frag));
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
	(*
	val (program, post, ls) = (ex_program, ex_post, ex_ls);
	*)
	val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (ex_program, ex_post, ex_ls) defs;


	val (wps1, wps1_bool_sound_thm) = bir_wp_comp_wps prog_thm ((ex_wps, wps_bool_sound_thm), (wpsdom, List.rev blstodo)) (ex_program, ex_post, ex_ls) defs;



	val aes_wps1_def = Define `
	      aes_wps1 = ^wps1
	`;

	val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;
	val _ = save_thm("aes_wps1_bool_sound_thm", wps1_bool_sound_thm_readable);



	val _ = export_theory();
      in
        frag_i + 1
      end) 0 frags;

  in
    ()
  end) () configurations;
