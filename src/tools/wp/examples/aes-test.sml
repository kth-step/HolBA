open HolKernel Parse;

open bir_wpTheory bir_wpLib;

open listSyntax;

open aesBinaryTheory;
open bir_expLib;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;





(*
val aes_program_termCutList = (snd o dest_comb o concl o EVAL) ``(REVERSE o (TAKE 5) o REVERSE) (case ^aes_program_term of BirProgram bls => bls)``;
val aes_program_term2 = ``BirProgram ^aes_program_termCutList``;


val first_block_label = (snd o dest_comb o concl o EVAL) ``(\x. x.bb_label) (HD (case ^aes_program_term2 of BirProgram bls => bls))``;
val last_block_label = (snd o dest_comb o concl o EVAL) ``(\x. x.bb_label) (LAST (case ^aes_program_term2 of BirProgram bls => bls))``;
(*
val last_block_label = ``BL_Address (Imm64 0x400574w)``;
*)
*)

fun get_nth_last_label prog_term n =
      let
        val (block_list, block_type) = (dest_list o dest_BirProgram) prog_term;
        val nth_last_block = List.nth (List.rev block_list, n)
      in
        (snd o dest_comb o concl o EVAL) ``(^nth_last_block).bb_label``
      end;

(* create subproblem for debugging and analysis *)
fun get_subprog_with_n_last prog_term n =
      let
        val (block_list, block_type) = (dest_list o dest_BirProgram) prog_term;
        val n_last_blocks = List.drop (block_list, (List.length block_list) - n)
      in
        mk_BirProgram (mk_list (n_last_blocks, block_type))
      end;

fun get_subprog_drop_n_at_end prog_term n =
      let
        val (block_list, block_type) = (dest_list o dest_BirProgram) prog_term;
        val n_last_blocks = List.rev (List.drop (List.rev block_list, n))
      in
        mk_BirProgram (mk_list (n_last_blocks, block_type))
      end;

fun get_prog_length prog_term =
      let
        val (block_list, block_type) = (dest_list o dest_BirProgram) prog_term;
      in
        List.length block_list
      end;


(*
aes round
0x4005dc - 0x40097c

*)

val take_all = false;
val take_n_last = 10;
val dontcalcfirstwp = true;

val aes_program_term_whole = ((snd o dest_comb o concl) aes_arm8_program_THM);
val aes_program_term_round = get_subprog_with_n_last (get_subprog_drop_n_at_end aes_program_term_whole 255) 233;

val aes_program_term = if take_all then
                         aes_program_term_round
                       else
                         get_subprog_with_n_last aes_program_term_round (take_n_last + 1)
                       ;

val last_block_label = get_nth_last_label aes_program_term 0;
val fst_block_label = get_nth_last_label aes_program_term ((get_prog_length aes_program_term) - 1);
val snd_block_label = get_nth_last_label aes_program_term ((get_prog_length aes_program_term) - 2);


val aes_program_def = Define `
      aes_program = ^aes_program_term
`;
val aes_post_def = Define `
      aes_post = (BExp_Const (Imm1 1w))
`;
val aes_ls_def = Define `
      aes_ls = \x.(x = ^last_block_label)
`;
val aes_wps_def = Define `
      aes_wps = (FEMPTY |+ (^last_block_label, aes_post))
`;





val program = ``aes_program``;
val post = ``aes_post``;
val ls = ``aes_ls``;
val wps = ``aes_wps``;

val defs = [aes_program_def, aes_post_def, aes_ls_def, aes_wps_def];



(* wps_bool_sound_thm for initial wps *)
val prog_term = (snd o dest_comb o concl) aes_program_def;
val wps_term = (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps;
val wps_bool_sound_thm = bir_wp_init_wps_bool_sound_thm (program, post, ls) wps defs;
val (wpsdom, blstodo) = bir_wp_init_rec_proc_jobs prog_term wps_term;
val blstodo = if (dontcalcfirstwp) then
                tl blstodo
              else
                blstodo
              ;


(*
fst rec_proc_jobs
snd rec_proc_jobs
*)


(* prepare "problem-static" part of the theorem *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls) defs;

(*
(* step-wise for debugging *)

(* one step label prep *)
val label = ``BL_Address_HC (Imm64 0x40057Cw) "XZY"``;
val prog_l_thm = proc_step1 label prog_thm (program, post, ls) defs;

(* one step wps soundness *)
val (wps1, wps1_bool_sound_thm) = proc_step2 (wps, wps_bool_sound_thm) (prog_l_thm) ((program, post, ls), (label)) defs;
*)



(*
val label = ``BL_Address (Imm64 0x400DA8w)``;(* "9101C3FF (add sp, sp, #0x70)"``;*)
*)
(* time intensive!!! *)
(* and the recursive procedure *)
val (wps1, wps1_bool_sound_thm) = bir_wp_comp_wps prog_thm ((wps, wps_bool_sound_thm), (wpsdom, blstodo)) (program, post, ls) defs;

(*
val (wpsdom, blstodo) = rec_proc_jobs;

val SOME(bl) = block;
    
val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog_conv@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;

val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;

val label_in_prog_conv = [bir_labels_of_program_def, BL_Address_HC_def];
val edges_blocks_in_prog_conv = [bir_edges_blocks_in_prog_exec_def, bir_targets_in_prog_exec_def, bir_get_program_block_info_by_label_def, listTheory.INDEX_FIND_def, BL_Address_HC_def];
val l_not_in_ls_conv = [BL_Address_HC_def];
val label_in_prog_thm = SIMP_CONV (srw_ss()) (label_in_prog_conv@defs) ``MEM ^label (bir_labels_of_program ^program)``;

val all_labels_thm = SIMP_CONV (srw_ss()) (label_in_prog_conv@defs) ``(bir_labels_of_program ^program)``;
val list = (snd o dest_eq o concl)all_labels_thm;

val all_lbs_def = Define `all_lbs = ^list`;
val label_in_prog1_thm = SIMP_CONV (list_ss) (label_in_prog_conv@[all_lbs_def]@defs) ``MEM ^label all_lbs``;

val label_in_prog1_thm = SIMP_CONV (list_ss) (label_in_prog_conv@[all_lbs_def]@defs) ``MEM ^label ^list``;


     bir_edges_blocks_in_prog_exec (BirProgram bls) l1 ⇔
     EVERY (λl2. MEM l2 (BirLabelsOf (BirProgram bls)))
       (bir_targets_in_prog_exec (BirProgram bls) l1):


val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog_conv@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;

val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;
    bir_edges_blocks_in_prog_exec_def
 
*)


(* to make it readable or speedup by incremental buildup *)
val aes_wps1_def = Define `
      aes_wps1 = ^wps1
`;
val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;

(*
val _ = print "===========";
val _ = print "weakest precondition:";
val wp_exp_term = (snd o dest_comb o concl o EVAL) ``(FAPPLY aes_wps1 ^snd_block_label)``;
val _ = bir_exp_pretty_print wp_exp_term;
*)


