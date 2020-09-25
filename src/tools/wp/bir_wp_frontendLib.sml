structure bir_wp_frontendLib =
struct

local
(* TODO: Clean up in includes... *)
open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open bir_program_no_assumeLib;

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

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

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
  fun make_blacklist_fmap blacklist =
    List.foldl (fn (label, map) =>
		  mk_fupdate (map,
                              mk_pair (label, bir_exp_false_tm)
                             )
	       )
	       (mk_fempty (bir_label_t_ty, bir_exp_t_ty))
	       blacklist
  ;

in

(* TODO: Is there any smarter way to do this? *)
fun dest_lambda tm = (Absyn.dest_AQ o snd o Absyn.dest_lam o Absyn.mk_AQ) tm;
fun ending_lam_disj_to_sml_list ls =
  if pred_setSyntax.is_empty ls
  then []
  else map (snd o dest_eq) (strip_disj (dest_lambda ls));

(*
val tm =   ``(BL_Address x) INSERT abc``
*)
fun dest_until_var tm =
  if not (pred_setSyntax.is_insert tm) then
    if is_var tm then [] else raise ERR "dest_until_var" ("is no variable: " ^ (term_to_string tm))
  else
    let val (x, tm') = pred_setSyntax.dest_insert tm in
      x::(dest_until_var tm')
    end;

fun ending_set_to_sml_list tm =
  pred_setSyntax.strip_set tm
  handle HOL_ERR _ => (
    print ("\nnotice that the variable set has to be a blacklist: " ^
           (term_to_string tm) ^ "\n");
    dest_until_var tm
  );

fun postcond_exp_from_label postcond label =
  (snd o dest_eq o concl)
    (SIMP_CONV
      (bool_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss) []
      (mk_comb (postcond, label)
    )
  )
;


fun init_wps_fmap label_list postcond postcond_exp_from_label = 
  let
    val empty_fmap = finite_mapSyntax.mk_fempty (bir_label_t_ty, bir_exp_t_ty)
    val postconds_list = map (fn tm => pairSyntax.mk_pair (tm, postcond_exp_from_label postcond tm)) label_list
  in
    finite_mapSyntax.list_mk_fupdate (empty_fmap, postconds_list)
  end
;

(*
val ending_lam_disj = ending_set;
val ending_lam_disj_to_sml_list = ending_set_to_sml_list;
*)
(* This is a wrapper function for generating and proving WPs. *)
(* TODO: Rename arguments to more generic ones *)
fun bir_obtain_ht prog_tm first_block_label_tm
                  ending_lam_disj
                    (ending_lam_disj_to_sml_list)
                  postcond_tm
                    (postcond_exp_from_label)
                  prefix defs =
  let
    (* Some terms which will be used: *)
    (* TODO: Should ending_lam_disj_to_sml_list be an argument
     * or be used in preprocessing before bir_obtain_ht? *)
    val wps_tm =
      finite_mapSyntax.mk_fempty (bir_label_t_ty, bir_exp_t_ty)

    val ending_label_list =
      ending_lam_disj_to_sml_list ending_lam_disj

    (* TODO: For all of the below, check that you are not using the huge program in a dumb way. *)
    (* For debugging bir_wp_init_wps_bool_sound_thm: 
      val (program, post, ls) = (prog_tm, postcond_tm, ending_lam_disj)
      val wps = wps_tm
    *)
    (* Prove theorem stating booleanity and soundness of wp map for starting wps *)
    val wps_bool_sound_thm =
      bir_wp_init_wps_bool_sound_thm
        (prog_tm, postcond_tm, ending_lam_disj) wps_tm defs
    val blstodo =
      bir_wp_init_rec_proc_jobs prog_tm first_block_label_tm ending_label_list

    (* Prepare "problem-static" part of computation: *)
    (* For debugging bir_wp_comp_wps_iter_step0_init:
      val (program, post, ls) = (prog_tm, postcond_tm, ending_lam_disj)
    *)
    val prog_thm =
      bir_wp_comp_wps_iter_step0_init
        (prog_tm, postcond_tm, ending_lam_disj) defs

    (* Main computation: *)
    (* For debugging bir_wp_comp_wps:
      val wps = wps_tm
      val wpsdom = ([]:term list)
      val blstodo = List.rev blstodo
      val program = prog_tm
      val post = postcond_tm
      val ls = ending_lam_disj
    *)
    val (wps1, wps1_bool_sound_thm) =
      bir_wp_comp_wps prog_thm ((wps_tm, wps_bool_sound_thm),
				(([]:term list), List.rev blstodo))
			       (prog_tm, postcond_tm, ending_lam_disj)
                               ending_label_list defs

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
    val hts_list_trim =
          if List.length hts_list <> 1 then
            List.take (hts_list, (length hts_list) - 1)
          else
            hts_list
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
           bir_never_assumviol_ht
           no_assumes_thm
        ) target_ht
    (* Obtain WP of target_bir_triple *)
    val target_wp_tm = get_wp_from_ht target_bir_triple
  in
    (target_bir_triple, target_wp_tm)
  end handle Option => raise ERR "bir_obtain_ht"
	("No Hoare triple was found for the start label "^
	 (term_to_string first_block_label_tm)^" and "^
         (* TODO: Ending labels here... *)
	 "the provided Ending addresses"(*(term_to_string last_block_label_tm)*)^
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
