open HolKernel Parse boolLib bossLib;

open tutorial_liftTheory;
open examplesBinaryLib;
open bir_wpLib;
open bir_wpTheory;
open bir_htTheory;
open bir_wp_expLib;
open bir_program_labelsTheory;
open bir_program_valid_stateTheory;
open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_multistep_propsTheory;

open bir_expSyntax;
open bir_programSyntax;
open bir_immSyntax;

open pred_setSyntax;

open bir_htLib;

open HolBACoreSimps;

val _ = new_theory "tutorial_wp";

(* Content:
 * 1. Theorem to obtain bir_triple from
 *    bir_exec_to_labels_or_assumviol_triple, given a program that
 *    has no Assume statements.
 * 2. WPs of the example code segments: loop entry, loop
 *    invariant and loop exit of sqrt program.
 * 3. Proof of the contracts using the RoC. *)

(* 11111111111111111111111111111111111111111111111111111111111111 *)
(* TODO: Move this... *)
val bir_exec_to_labels_exists =
  store_thm("bir_exec_to_labels_exists",
  ``!ls prog st.
      ?r.
        bir_exec_to_labels ls prog st = r``,

FULL_SIMP_TAC std_ss [bir_exec_to_labels_def]
);

val bir_never_assumviol_block_n_ht_from_to_labels_ht =
  store_thm("bir_never_assumviol_block_n_ht_from_to_labels_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_triple prog l ls pre post``,

REWRITE_TAC [bir_triple_def,
             bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``ls:bir_label_t -> bool``,
                   ``prog:'a bir_program_t``,
                   ``s:bir_state_t``] bir_exec_to_labels_exists) >>
FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``!s'. _``
            (fn thm => ASSUME_TAC
              (SPEC ``s:bir_state_t`` thm)
            ) >>
REV_FULL_SIMP_TAC std_ss [] >> (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
  IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
  quantHeuristicsLib.QUANT_TAC [("n", `m`, []),
				("l1", `l1`, []),
				("c1", `c1`, []),
				("c2", `c_l'`, []),
				("s'", `s'`, [])] >>
  FULL_SIMP_TAC std_ss []
)
);

(* 22222222222222222222222222222222222222222222222222222222222222 *)

fun find_ht _            []     = NONE
  | find_ht target_label (h::t) =
  let
    val curr_label = (el 2 o snd o strip_comb o concl) h
  in
    if (term_eq curr_label target_label)
    then SOME h
    else find_ht target_label t
  end
;

(* TODO: Need to make sure a mess is not caused by overloading
 * definitions.
 *
 * This can be solved by passing an additional prefix/suffix to
 * bir_wp_comp_wps.
 *)
fun bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                  postcond_tm prefix =
  let
    (* TODO: Make some sort of test to check if computations have
     * already been performed for current prefix. *)
    (* Definitions: *)
    val prog_def = Define `
      ^(mk_var(prefix^"prog", type_of prog_tm)) = ^prog_tm
    `
    (*   For some reason prog requires this approach... *)
    val prog_var = Parse.Term [QUOTE (prefix^"prog")]
    val postcond_def = Define `
      ^(mk_var(prefix^"postcond", bir_exp_t_ty)) = ^postcond_tm
    `
    val postcond_var = (fst o dest_eq o concl) postcond_def
    val ls_def = Define `
      ^(mk_var(prefix^"ls", mk_set_type bir_label_t_ty)) =
        \x.(x = ^last_block_label_tm)
    `
    val ls_var = (fst o dest_eq o concl) ls_def
    val wps_def = Define `
      ^(mk_var(prefix^"wps", ``:bir_label_t |-> bir_exp_t``)) =
        (FEMPTY |+ (^last_block_label_tm,
                    ^((fst o dest_eq o concl) postcond_def)
                   )
        )
    `
    val wps_var = (fst o dest_eq o concl) wps_def

    (* List of definitions: *)
    val defs = [prog_def, postcond_def, ls_def, wps_def]

    (* Initialize queue of blocks to process: *)
    val wps_tm =
      (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps_var
    val wps_bool_sound_thm =
      bir_wp_init_wps_bool_sound_thm
        (prog_var, postcond_var, ls_var) wps_var defs
    val (wpsdom, blstodo) =
      bir_wp_init_rec_proc_jobs prog_tm wps_tm

    (* Prepare "problem-static" part of computation: *)
    val prog_thm =
      bir_wp_comp_wps_iter_step0_init
        bir_wp_exec_of_block_reusable_thm
        (prog_var, postcond_var, ls_var) defs

    (* Main computation: *)
    val (wps1, wps1_bool_sound_thm) =
      bir_wp_comp_wps prog_thm ((wps_var, wps_bool_sound_thm),
				(wpsdom, List.rev blstodo))
			       (prog_var, postcond_var, ls_var) defs

    (* Pick out the soundness theorems, *)
    val sound_thms = ((el 2 o CONJUNCTS) wps1_bool_sound_thm)
    (* expand bir_sound_wps_map definition, *)
    val simp_thm2 =
      SIMP_RULE std_ss [bir_sound_wps_map_def] sound_thms
    (* transform the FEVERY into conjunctions for the individual
     * cases, *)
    val simp_thm3 =
      CONV_RULE finite_mapLib.fevery_EXPAND_CONV simp_thm2
    (* then simplify set-theoretical operations and address
     * equality. *)
    val simp_thm4 =
      SIMP_RULE (std_ss++holBACore_ss++wordsLib.WORD_ss++
		 wordsLib.WORD_ARITH_EQ_ss++pred_setLib.PRED_SET_ss)
		[ls_def, BL_Address_HC_def] simp_thm3
    (* CONJUNCTS now obtains a list with Hoare triples (plus an
     * abbreviation for the postcondition), from which we can pick
     * the theorem we need. *)
    val hts_list = CONJUNCTS simp_thm4
    val hts_list_trim = List.take (hts_list, (length hts_list) - 1)
    val target_ht =
      valOf (find_ht first_block_label_tm hts_list_trim)
    (* Transform HT to bir_triple *)
    (* TODO: Make bir_htSyntax *)
    val no_assumes_thm =
      REWRITE_RULE [GSYM prog_def]
        (bir_prog_has_no_assumes_pp
           ``bir_prog_has_no_assumes ^prog_tm``
        )
    val target_bir_triple =
      HO_MATCH_MP
        (HO_MATCH_MP bir_never_assumviol_block_n_ht_from_to_labels_ht
                     no_assumes_thm
        ) target_ht
    (* Obtain definition of WP expression *)
    val wp_name =
      "bir_wp_comp_wps_iter_step2_wp_"^
      ((term_to_string o snd o gen_dest_Imm o dest_BL_Address)
        first_block_label_tm)
    val final_wp_def =
      EVAL (Parse.Term [QUOTE wp_name])
  in
    (target_bir_triple, [prog_def, postcond_def, final_wp_def])
  end handle Option => raise ERR "extract_subprogram"
	("No Hoare triple was found for the addresses "^
	 (term_to_string first_block_label_tm)^" and "^
	 (term_to_string last_block_label_tm)^
	 ". Please double-check these addresses in the BIR "^
         "program.")
;

(******************************************************************)
val prog_tm = sqrt_prog_tm;
(****************** bir_sqrt_entry_contract ***********************)
val prefix = "sqrt_entry_"
val first_block_label_tm = ``BL_Address (Imm64 0x400250w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =
  ``BL_Address_HC (Imm64 0x400288w)
      "54FFFEC9 (b.ls 400260 <sqrt_+0x10>  // b.plast)"``;
val postcond_tm = (snd o dest_eq o concl) b_sqrt_I_def;
val bir_sqrt_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm;

(****************** bir_sqrt_loop_inv_contract ********************)
val first_block_label_tm = ``BL_Address (Imm64 0x400288w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =
  ``BL_Address_HC (Imm64 0x400288w)
      "54FFFEC9 (b.ls 400260 <sqrt_+0x10>  // b.plast)"``;
val postcond_tm = (snd o dest_eq o concl) b_sqrt_I_def;
val bir_sqrt_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm;

(***************** bir_sqrt_loop_exit_contract ********************)
val first_block_label_tm = ``BL_Address (Imm64 0x400288w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =
  ``BL_Address (Imm64 0x400294w)``;
val postcond_tm =
  ``(BExp_BinExp BIExp_And (b_sqrt_I)
      (BExp_UnaryExp BIExp_Not
        (BExp_Den (BVar "ProcState_C" BType_Bool))
      )
    )``;
val bir_sqrt_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm;


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
