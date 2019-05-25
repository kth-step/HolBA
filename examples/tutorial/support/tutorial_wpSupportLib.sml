structure tutorial_wpSupportLib =
struct

local
(* TODO: Clean up in includes... *)
open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib bir_htLib;
open easy_noproof_wpLib;

open bir_wpTheory bir_htTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples: *)
open examplesBinaryTheory;
open tutorial_bir_to_armSupportTheory;
open tutorial_bir_to_armTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

(* Local *)
open tutorial_wpSupportTheory;

in

val eot = (rhs o concl o EVAL)
val get_wp_from_ht =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl)

local

  (* This finds exactly one HT whose execution starts from
   * target_label. *)
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

  (* This helper function takes a list of BIR program labels and
   * makes a finite map mapping these onto BIR False. *)
  fun make_false_label_fmap false_label_l =
    List.foldl (fn (label, map) =>
		  mk_fupdate (map,
                              mk_pair (label, bir_exp_false_tm)
                             )
	       )
	       (mk_fempty (bir_label_t_ty, bir_exp_t_ty))
	       false_label_l
  ;

in

(* This is a wrapper function for generating and proving WPs. *)
fun bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                  postcond_tm prefix false_label_l defs =
  let
    (* Some terms which will be used: *)
    (*   The terminating label set *)
    val ls_tm = ``\x.(x = ^last_block_label_tm)``
    (*   A finite map of dummy labels to False *)
    val false_fmap_tm = make_false_label_fmap false_label_l
    (*   A finite map of all the labels and all the preconditions,
     *   which will be used throughout the computation to store
     *   the WPs *)
    val wps_tm = ``
        ((^false_fmap_tm) |+ (^last_block_label_tm,
                    ^(postcond_tm)
                   )
        )
    ``;

    (* Initialize queue of blocks to process: *)
    val wps_expand_tm =
      (rhs o concl o (SIMP_CONV std_ss defs)) wps_tm
    (* For debugging bir_wp_init_wps_bool_sound_thm: 
    val (program, post, ls) = (prog_tm, postcond_tm, ls_tm)
    val wps = wps_tm
    *)
    val wps_bool_sound_thm =
      bir_wp_init_wps_bool_sound_thm
        (prog_tm, postcond_tm, ls_tm) wps_tm defs
    val (wpsdom, blstodo) =
      bir_wp_init_rec_proc_jobs (eot prog_tm) wps_expand_tm
                                false_label_l

    (* Prepare "problem-static" part of computation: *)
    (* For debugging bir_wp_comp_wps_iter_step0_init:
    val reusable_thm = bir_wp_exec_of_block_reusable_thm;
    val (program, post, ls) = (prog_tm, postcond_tm, ls_tm)
    *)
    val prog_thm =
      bir_wp_comp_wps_iter_step0_init
        bir_wp_exec_of_block_reusable_thm
        (prog_tm, postcond_tm, ls_tm) defs

    (* Main computation: *)
    (* For debugging bir_wp_comp_wps:
      val wps = wps_tm
      val blsotodo = List.rev blstodo
      val program = prog_tm
      val post = postcond_tm
      val ls = ls_tm
    *)
    val (wps1, wps1_bool_sound_thm) =
      bir_wp_comp_wps prog_thm ((wps_tm, wps_bool_sound_thm),
				(wpsdom, List.rev blstodo))
			       (prog_tm, postcond_tm, ls_tm) defs

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
		[BL_Address_HC_def] simp_thm3
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
        (bir_prog_has_no_assumes_rewr_pp
            defs
            ``bir_prog_has_no_assumes ^(prog_tm)``)
    val target_bir_triple =
      HO_MATCH_MP
        (HO_MATCH_MP
           bir_never_assumviol_block_n_ht_from_to_labels_ht
           no_assumes_thm
        ) target_ht
    (* Obtain WP of target_bir_triple *)
    val target_wp_tm = get_wp_from_ht target_bir_triple
  in
    (target_bir_triple, target_wp_tm)
  end handle Option => raise ERR "extract_subprogram"
	("No Hoare triple was found for the addresses "^
	 (term_to_string first_block_label_tm)^" and "^
	 (term_to_string last_block_label_tm)^
	 ". Please double-check these addresses in the BIR "^
         "program.")
;

end

(*
(* This function proves implications between BIR expressions using
 * the SMT solver Z3. *)
fun prove_imp_w_smt ante conseq =
  let
    val bir_impl = bor (bnot ante, conseq)
    val w_tm = bir2bool bir_impl
  in
    HolSmtLib.Z3_ORACLE_PROVE w_tm

    handle HOL_ERR e =>
      let
        val neg_tm = mk_neg w_tm
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL neg_tm
        val _ = print "Failed to prove the implication. Anyways, have a SAT model: ";
        val _ = PolyML.print model;
      in
        raise HOL_ERR e
      end
  end
;
*)

end

end
