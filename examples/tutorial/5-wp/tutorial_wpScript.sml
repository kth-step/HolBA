open HolKernel Parse boolLib bossLib;

open tutorial_liftTheory;
open examplesBinaryLib;
open bir_wpLib;
open bir_wpTheory;
open bir_htTheory;
open bir_wp_expLib;
open bir_program_labelsTheory;

open HolBACoreSimps;

val _ = new_theory "tutorial_wp";

(* Need:
 * 1. Prove theorem to obtain bir_triple from
 *    bir_exec_to_labels_or_assumviol_triple, given a program that
 *    has no Assume statements.
 * 2. Obtain WPs of the code segments below: for loop entry, loop
 *    invariant and loop exit.
 * 3. Prove the contracts using the RoC. *)

(* 11111111111111111111111111111111111111111111111111111111111111 *)
(* TODO: Should be proven with the aid of
 * bir_prog_not_assume_never_assumviol_exec_block_n. Also see
 * bir_never_assumviol_ht for proof inspiration. *)
val bir_never_assumviol_block_n_ht_from_to_labels_ht =
  store_thm("bir_never_assumviol_block_n_ht_from_to_labels_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_triple prog l ls pre post``,

cheat
);

(* 22222222222222222222222222222222222222222222222222222222222222 *)
(****************** bir_sqrt_entry_contract ***********************)
(* TODO: Make everything in section 2 into a function. *)
val last_block_label_tm =
  ``BL_Address_HC (Imm64 0x400288w)
      "54FFFEC9 (b.ls 400260 <sqrt_+0x10>  // b.plast)"``;
val b_sqrt_I_tm = (snd o dest_eq o concl) b_sqrt_I_def;

(* Definitions: *)
val sqrt_prog_def = Define `
  sqrt_prog = ^sqrt_prog_tm`;
val sqrt_post_def = Define `
  sqrt_post = ^b_sqrt_I_tm`;
val sqrt_ls_def = Define `
  sqrt_ls = \x.(x = ^last_block_label_tm)
`;
val sqrt_wps_def = Define `
  sqrt_wps = (FEMPTY |+ (^last_block_label_tm, sqrt_post))
`;

(* Pick out terms: *)
val program = ``sqrt_prog``;
val post = ``sqrt_post``;
val ls = ``sqrt_ls``;
val wps = ``sqrt_wps``;

(* List of definitions: *)
val defs = [sqrt_prog_def,
            sqrt_post_def,
            sqrt_ls_def,
            sqrt_wps_def];

(* wps_bool_sound_thm for initial wps: *)
val prog_term = (snd o dest_comb o concl) sqrt_prog_def;
val wps_term =
  (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps;
val wps_bool_sound_thm =
  bir_wp_init_wps_bool_sound_thm (program, post, ls) wps defs;
val (wpsdom, blstodo) =
  bir_wp_init_rec_proc_jobs prog_term wps_term;

(* Prepare "problem-static" part of the theorem: *)
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val prog_thm =
  bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls)
                                  defs;

(* Main computation: *)
val (wps1, wps1_bool_sound_thm) =
  bir_wp_comp_wps prog_thm ((wps, wps_bool_sound_thm),
                            (wpsdom, List.rev blstodo))
                           (program, post, ls) defs;

(* Pick out the soundness theorems... *)
val thm1 = ((el 2 o CONJUNCTS) wps1_bool_sound_thm);
(* expand bir_sound_wps_map definition... *)
val thm2 = SIMP_RULE std_ss [bir_sound_wps_map_def] thm1;
(* transform the FEVERY into conjunctions for the individual
 * cases... *)
val thm3 =
  CONV_RULE finite_mapLib.fevery_EXPAND_CONV thm2;
(* Simplify set-theoretical operations and address equality *)
val thm4 =
  SIMP_RULE (std_ss++holBACore_ss++wordsLib.WORD_ss++
             wordsLib.WORD_ARITH_EQ_ss++pred_setLib.PRED_SET_ss)
            [sqrt_ls_def, BL_Address_HC_def] thm3;
(* CONJUNCTS now obtains a list with Hoare triples (plus an
 * abbreviation for the postcondition), from which we can pick the
 * theorem we need. *)
val generated_ht = (el 1 o CONJUNCTS) thm4;

(* 33333333333333333333333333333333333333333333333333333333333333 *)
(****************** bir_sqrt_entry_contract ***********************)
(* This theorem would allow us to prove the contractual HT from
 * the generated one. *)
val bir_sqrt_entry_contract_roc =
  store_thm("bir_sqrt_entry_contract_roc",
  ``bir_triple sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      bir_wp_comp_wps_iter_step2_wp_0x400250w
      sqrt_post ==>
    bir_triple sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      (BExp_Const (Imm1 1w))
      b_sqrt_I``,

cheat
);

(******************************************************************)
(*                 Trying to define contracts                     *)
(* TODO: Add that the SP is higher than program code and smaller
 * than max stack. Both to precondition and invariant. *)
(* TODO: WHY DOES NO DEFINITION WORK? *)
(***                     TEST AREA                              ***)
(* The below apparently works... *)
val test = SPECL [``sqrt_prog``,
                  ``(BL_Address (Imm64 2132w))``,
                  ``(\x.(x = (BL_Address (Imm64 2192w))))``,
                  ``(BExp_Const (Imm1 1w))``,
                  ``b_sqrt_I``] bir_triple_def;
(* Check type... *)
val test_ty = type_of ((snd o dest_eq o concl) sqrt_prog_def);
(* The below does not work either... :( *)
(* Nullary definition failed - giving up *)
val bir_sqrt_entry_contract_test_def = Define `
  test_def_triple = bir_exec_to_labels_or_assumviol_triple test_prog
`;
(* Nullary definition failed - giving up *)
val bir_sqrt_entry_contract_def = Define `
  bir_sqrt_entry_contract =
    bir_triple sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      (BExp_Const (Imm1 1w))
      b_sqrt_I
`;
(* Nullary definition failed - giving up *)
val bir_sqrt_loop_inv_contract_def = Define `
  `bir_sqrt_loop_inv_contract =
     bir_triple sqrt_prog (BL_Address (Imm64 0x400288w))
       {BL_Address (Imm64 0x400288w)}
       (BExp_BinExp BIExp_And (b_sqrt_I)
         (BExp_Den (BVar "ProcState_C" BType_Bool))
       )
       b_sqrt_I`;
(* Nullary definition failed - giving up *)
val bir_sqrt_loop_exit_contract_def = Define `
  `bir_sqrt_loop_exit_contract =
     bir_triple sqrt_prog (BL_Address (Imm64 0x400288w))
       {BL_Address (Imm64 0x400294w)}
       (BExp_BinExp BIExp_And (b_sqrt_I)
	 (BExp_UnaryExp BIExp_Not
	   (BExp_Den (BVar "ProcState_C" BType_Bool))
	 )
       )
       (BExp_BinExp BIExp_And (b_sqrt_I)
	 (BExp_UnaryExp BIExp_Not
	   (BExp_Den (BVar "ProcState_C" BType_Bool))
	 )
       )`;
(******************************************************************)

val _ = export_theory();
