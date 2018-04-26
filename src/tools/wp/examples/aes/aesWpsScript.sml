open HolKernel Parse;

open bir_wpTheory bir_wpLib;

open listSyntax;

open aesBinaryTheory;
open bir_expLib;

open bir_wp_expLib;



val _ = new_theory "aesWps";

(*

see "aes/aes-aarch64.da"

0x4005d8: branch to 0x400980

aes round:
0x4005dc - 0x40097c

loop condition check with conditional branch to 0x4005dc:
0x400980 - 0x400988

*)



(* how many blocks of the aes round do we take for the computation? *)
val take_all = true; (* false for a normal run, should override the others *)
val take_n_last = 60; (* we will get one block more at the end as a dummy block *)

val aes_program_term_whole = ((snd o dest_comb o concl) aes_arm8_program_THM);
(* include one after the last as dummy block *)
val aes_program_term_round = get_subprog_with_n_last (get_subprog_drop_n_at_end aes_program_term_whole (255 - 1)) (233 + 1);

val aes_program_term = if take_all then
                         aes_program_term_round
                       else
                         get_subprog_with_n_last aes_program_term_round (take_n_last + 1) (* +1 for the dummy block *)
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



(* prepare "problem-static" part of the theorem *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm = bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls) defs;



val (wps1, wps1_bool_sound_thm) = bir_wp_comp_wps prog_thm ((wps, wps_bool_sound_thm), (wpsdom, List.rev blstodo)) (program, post, ls) defs;
val aes_wps1_def = Define `
      aes_wps1 = ^wps1
`;

val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;
val _ = save_thm("aes_wps1_bool_sound_thm", wps1_bool_sound_thm_readable);


val _ = export_theory();

