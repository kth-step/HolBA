open HolKernel Parse;

open listSyntax;
open finite_mapSyntax;

open binariesTheory;
(*open toyBinaryTheory;*)
open bir_cfgLib;
open bir_cfgVizLib;

open bir_wpTheory bir_wpLib;




val configurations = [
  ("m0"  , "toy"    , toy_m0_program_THM),
  ("arm8", "aes"    , aes_arm8_program_THM),
  ("m0"  , "aes"    , aes_m0_program_THM),
  ("arm8", "bignum" , bignum_arm8_program_THM),
  ("m0"  , "bignum" , bignum_m0_program_THM),
  ("arm8", "wolfssl", wolfssl_arm8_program_THM),
  ("m0"  , "wolfssl", wolfssl_m0_program_THM)
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
    val (arch_str, example_str, prog_thm) = ("m0"  , "bignum"    , bignum_m0_program_THM);
    *)

    val theory_name_prefix = example_str ^ "_" ^ arch_str ^ "_";
    val _ = print ("processing program: " ^ theory_name_prefix ^ "\n");

    val prog = ((snd o dest_comb o concl) prog_thm);
    val blocks = (fst o dest_list o dest_BirProgram) prog;


    val timer = (Time.now());


    val g = cfg_compute_inoutedges_as_idxs blocks;
    (*
    val _ = bir_show_graph_inout_all true g;
    val _ = bir_show_graph_inout_all false g;
    *)

    val conn_comps = find_conn_comp g;
    (*
    val _ = List.map (fn (nodes,_,_) => bir_show_graph_inout true nodes g) conn_comps;
    *)

    (*
    val (blocks, in_idxs, out_idxs) = g;
    *)
    val frags = divide_loopfree_fragments g conn_comps;



    val d_time = Time.- (Time.now(), timer);
    val d_s = (Time.toString d_time);
    val _ = print ("time_to_divide_loopfree = " ^ d_s ^ " s\n\n\n");


    (*val frags = List.map (fn x => (x, [hd x], [List.last x])) (divide_linear_fragments g conn_comps);*)
    val num_frags = length frags;
    val (max_frag, max_frag_size, _) = List.foldl (fn ((l,_,_),(mf,m,i)) => let val fl = length l; in
        if fl > m then
          (i,fl,i+1)
        else
          (mf,m,i+1)
      end) (0,0,0) frags;
    (*val max_frag_size = List.foldl (fn (l,m) => Int.max(length l,m)) 0 frags;*)
    val sum_frag_size = List.foldl (fn ((l,_,_),s) => s + (length l)) 0 frags;

    val _ = print ("\n" ^ example_str ^ " - " ^ arch_str ^ ":\n");
    val _ = print ((Int.toString num_frags) ^ " fragments\n");
    val _ = print ((Int.toString max_frag_size) ^ " max frag size in frag " ^ (Int.toString max_frag) ^ "\n");
    val _ = print ((Int.toString (length blocks)) ^ " blocks in the binary\n");
    val _ = print ((Int.toString sum_frag_size) ^ " blocks in all fragments\n");
    val _ = print ((Int.toString (length blocks)) ^ " blocks in the original program\n");
    val _ = print "\n\n";
    val _ = if sum_frag_size = (length blocks) then () else print "sum fragment size: there is something fishy here";




    (* remove all temporary theories with this prefix *)
    val _ = OS.Process.system ("rm " ^ theory_name_prefix ^ "*");



    val skipidx = 0;(* 1531 *)
    val maxlength = 150;

    val (num_frags_to_consider,sum_frag_size_to_consider,max_frag_size_to_consider) = List.foldl (fn (frag,(acc,acc2,acc3)) =>
          let val frag_size = length ((fn (x,_,_) => x) frag); in
          if (maxlength > 0 andalso maxlength < frag_size)
          then (acc,acc2,acc3)
          else (acc + 1,acc2 + frag_size, Int.max(acc3,frag_size))
          end
        ) (0,0,0) frags;

    val _ = print ("... looking only at fragments where block number <= " ^ (Int.toString maxlength) ^ "\n");
    val _ = print ("        i.e., " ^ (Int.toString num_frags_to_consider) ^ " fragments\n");
    val _ = print ("              with in total " ^ (Int.toString sum_frag_size_to_consider) ^ " blocks\n");
    val _ = print ("              with the maximum frag having " ^ (Int.toString max_frag_size_to_consider) ^ " blocks\n");
    val _ = print "\n\n";



    val sum_time_ref = ref (0:int);
    val max_time_ref = ref (0:int);

    (* iterate over all fragments *)
    val _ = List.foldl (fn (frag,frag_i) => if frag_i < skipidx orelse (maxlength > 0 andalso maxlength < length ((fn (x,_,_) => x) frag)) then frag_i + 1 else
      let
	(*
	val frag_i = 0;
	val frag_i = 1;

	val frag_i = skipidx;
	val frag = List.nth (frags,frag_i);
	*)

        (*
        val (frag_ns, _, _) = frag;
        val _ = bir_show_graph_inout true frag_ns g;
        val _ = bir_show_graph_inout false frag_ns g;
        *)

	val theory_name = theory_name_prefix ^ (Int.toString frag_i);

        val (frag_ns, frag_en, frag_ex) = frag;
        val _ = print ("==================================\n");
        val _ = print ("frag " ^ (Int.toString frag_i) ^ " (length: " ^ (Int.toString (length frag_ns)) ^ ")\n");
        val _ = print ("==================================\n");


    val timer = (Time.now());


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

	val (program,_) = select_blocks_from_prog frag_ns prog;

        val block_index_to_label = (fn i =>
          let
            val block = List.nth(blocks,i);

	    val eval_label = (snd o dest_eq o concl o EVAL);
	    val (raw_BL_term, _, _) = dest_bir_block block;
	    val BL_term = eval_label raw_BL_term;
          in
            BL_term
          end);

        val last_block_labels = List.map block_index_to_label frag_ex;
        val first_block_labels = List.map block_index_to_label frag_en;

	val ex_program_def = Define `
	      ex_program = ^program
	`;
	val ex_post_def = Define `
	      ex_post = (BExp_Const (Imm1 1w))
	`;

        val ex_ls_term = List.foldl (fn (lab,tm) => ``(^tm) \/ (x = ^(lab))``) (``x = ^(hd last_block_labels)``) (tl last_block_labels);
	val ex_ls_def = Define `
	      ex_ls = \x.(^ex_ls_term)
	`;

        val ex_wps_term = List.foldl (fn (lab,tm) => ``(^tm) |+ (^lab, ex_post)``) (``FEMPTY:bir_label_t |-> bir_exp_t``) last_block_labels;
	val ex_wps_def = Define `
	      ex_wps = (^ex_wps_term)
	`;



	val ex_program = ``ex_program``;
	val ex_post = ``ex_post``;
	val ex_ls = ``ex_ls``;
	val ex_wps = ``ex_wps``;(*(snd o dest_eq o concl) ex_wps_def;``ex_wps``;*)

	val defs = [ex_program_def, ex_post_def, ex_ls_def, ex_wps_def];

	(*
	val (program, post, ls) = (ex_program, ex_post, ex_ls);
	val wps = ex_wps;
	*)


	(* wps_bool_sound_thm for initial wps *)
	val prog_term = (snd o dest_comb o concl) ex_program_def;
	val wps_term = (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) ex_wps;
	val wps_bool_sound_thm = bir_wp_init_wps_bool_sound_thm (ex_program, ex_post, ex_ls) ex_wps defs;
	val (wpsdom, blstodo) = bir_wp_init_rec_proc_jobs prog_term wps_term [];



	(* prepare "problem-static" part of the theorem *)
	val reusable_thm = bir_wp_exec_of_block_reusable_thm;
	val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (ex_program, ex_post, ex_ls) defs;


	val (wps1, wps1_bool_sound_thm) = bir_wp_comp_wps prog_thm ((ex_wps, wps_bool_sound_thm), (wpsdom, List.rev blstodo)) (ex_program, ex_post, ex_ls) defs;


        val d_time = Time.- (Time.now(), timer);
        val d_ms = Time.toMilliseconds d_time;
    
        val _ = sum_time_ref := (!sum_time_ref) + d_ms;
        val _ = max_time_ref := (Int.max(!max_time_ref,d_ms));


        (* verify that we have wps for each entry *)
        val wps_ = (snd o dest_eq o concl o (REWRITE_CONV [ex_wps_def])) wps1
                   handle UNCHANGED => wps1;
        (*
        val label = hd first_block_labels;
        find_wp_const label wps_
        *)
        fun find_wp_const label wps1 =
          if is_fempty wps1 then NONE else
          if not (is_fupdate wps1) then raise ERR "find_wp_const" "unexpected syntax" else
          let
            val (wps2, mapping) = dest_fupdate wps1;
            val (label2,const) = dest_pair mapping;
          in
            if label2 <> label then find_wp_const label wps2 else
            if is_const const then SOME const else
            raise ERR "find_wp_const" "the resulting term is not const"
          end;

        val _ = List.map (fn label => if find_wp_const label wps_ = NONE then
                                        raise ERR "select_blocks_from_prog" "cannot find one of the preconditions"
                                      else ())
                         (List.filter (fn x => not (List.exists (fn y => x = y) last_block_labels)) first_block_labels);



	val ex_wps1_def = Define `
	      ex_wps1 = ^wps1
	`;

	val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM ex_wps1_def] wps1_bool_sound_thm;
	val _ = save_thm("ex_wps1_bool_sound_thm", wps1_bool_sound_thm_readable);



	val _ = export_theory();
      in
        frag_i + 1
      end) 0 frags;


    fun ms_to_s ms_int =
      ((Int.toString (ms_int div 1000)) ^ "." ^ (Int.toString (ms_int mod 1000)));

    val _ = print ("times for the fragments:\n");
    val _ = print ("     sum time: " ^ (ms_to_s (!sum_time_ref)) ^ " s \n");
    val _ = print ("     max time: " ^ (ms_to_s (!max_time_ref)) ^ " s \n\n\n");

  in
    ()
  end) () configurations;
