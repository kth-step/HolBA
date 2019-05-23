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
(* TODO: Need to make sure a mess is not caused by overloading
 * definitions.
 *
 * This can be solved by passing an additional prefix/suffix to
 * bir_wp_comp_wps.
 *)
fun bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                  postcond_tm prefix false_label_l defs =
  let
    (* TODO: Make some sort of test to check if computations have
     * already been performed for current prefix. *)
    (* Definitions: *)
(*
    val prog_def = Define `
      ^(mk_var(prefix^"prog", type_of prog_tm)) = ^prog_tm
    `
*)
    (*   For some reason prog requires this approach... *)
    val prog_var = prog_tm
(*
    val postcond_def = Define `
      ^(mk_var(prefix^"postcond", bir_exp_t_ty)) = ^postcond_tm
    `
*)
    val postcond_var = postcond_tm
    val ls_var = ``\x.(x = ^last_block_label_tm)``
    val false_fmap_tm = make_false_label_fmap false_label_l
    val wps_def = Define `
      ^(mk_var(prefix^"wps", ``:bir_label_t |-> bir_exp_t``)) =
        ((^false_fmap_tm) |+ (^last_block_label_tm,
                    ^(postcond_tm)
                   )
        )
    `
    val wps_var = (fst o dest_eq o concl) wps_def

    (* List of definitions: *)

    val defs = [wps_def]@defs


    (* Initialize queue of blocks to process: *)
    val wps_tm =
      (rhs o concl o (SIMP_CONV std_ss defs)) wps_var
(* For experimentation: 
val (program, post, ls) = (prog_var, postcond_var, ls_var)
val wps = wps_var
*)
    val wps_bool_sound_thm =
      bir_wp_init_wps_bool_sound_thm
        (prog_var, postcond_var, ls_var) wps_var defs
    val (wpsdom, blstodo) =
      bir_wp_init_rec_proc_jobs (eot prog_tm) wps_tm false_label_l

    (* Prepare "problem-static" part of computation: *)
(*
val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val (program, post, ls) = (prog_var, postcond_var, ls_var)
*)
    val prog_thm =
      bir_wp_comp_wps_iter_step0_init
        bir_wp_exec_of_block_reusable_thm
        (prog_var, postcond_var, ls_var) defs

    (* Main computation: *)
(*
  val wps = wps_var
  val blsotodo = List.rev blstodo
  val program = prog_var
  val post = postcond_var
  val ls = ls_var
*)
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
        (bir_prog_has_no_assumes_pp
            defs
            ``bir_prog_has_no_assumes ^(prog_tm)``)
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
    (target_bir_triple, [final_wp_def])
  end handle Option => raise ERR "extract_subprogram"
	("No Hoare triple was found for the addresses "^
	 (term_to_string first_block_label_tm)^" and "^
	 (term_to_string last_block_label_tm)^
	 ". Please double-check these addresses in the BIR "^
         "program.")
;

end

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

end

end
