structure tutorial_compositionLib =
struct
  local
    open bslSyntax;
    open tutorial_bir_to_armSupportTheory;
    open tutorial_wpSupportLib;
    open bir_auxiliaryLib;
  in
    fun get_contract_prog contract_thm = ((el 1) o snd o strip_comb o concl) contract_thm;
    fun get_contract_l contract_thm = ((el 2) o snd o strip_comb o concl) contract_thm;
    fun get_contract_ls contract_thm = ((el 3) o snd o strip_comb o concl) contract_thm;
    fun get_contract_pre contract_thm = ((el 4) o snd o strip_comb o concl) contract_thm;
    fun get_contract_post contract_thm = ((el 5) o snd o strip_comb o concl) contract_thm;

    fun bir_triple_tm_get_sort_ls_thm ht_tm =
      let
	val ls = ((el 3) o snd o strip_comb) ht_tm
	val sorted_ls = pred_setSyntax.mk_set (ins_sort_tm (pred_setSyntax.strip_set ls))
      in 
	EQT_ELIM (computeLib.EVAL_CONV (mk_eq (ls, sorted_ls)))
      end
    ;

    fun get_bir_map_triple_prog map_triple = ((el 1) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_invariant map_triple = ((el 2) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_start_label map_triple = ((el 3) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_wlist map_triple = ((el 4) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_blist map_triple = ((el 5) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_pre map_triple = ((el 6) o snd o strip_comb o concl) map_triple;
    fun get_bir_map_triple_post map_triple = ((el 7) o snd o strip_comb o concl) map_triple;

    (* TODO: Is there any smarter way to do this? *)
    fun mk_lambda_lset_from_llist label_list =
      ``\x. ^(list_mk_disj (map (curry mk_eq (mk_var ("x", bir_label_t_ty))) label_list))``

    val string_ss = rewrites (type_rws ``:string``);
    val char_ss = rewrites (type_rws ``:char``);

    val vars_ss = std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss;

    fun use_pre_str_rule contract_thm pre_impl_wp =
      let
        fun remove_foralls t = (remove_foralls o snd o dest_forall) t
                               handle HOL_ERR _ => t;

	val contract_thm = SIMP_RULE std_ss [bir_bool_expTheory.bir_exp_and_def] contract_thm;
        val pre_wo = (remove_foralls o concl) pre_impl_wp;
	val pre = ((el 2) o snd o strip_comb o (el 2) o snd o strip_comb o hd o snd o strip_comb) pre_wo;

	val prog = get_contract_prog contract_thm;
	val entry = get_contract_l contract_thm;
	val exit = get_contract_ls contract_thm;
	val post = get_contract_post contract_thm;
	val wp = get_contract_pre contract_thm;
	val taut_thm = computeLib.RESTR_EVAL_RULE [(fst o strip_comb) pre, ``bir_exp_is_taut``] pre_impl_wp;
        (* TODO: This is slow. Replace it with something faster later. *)
	val pre_var_thm = prove (``
	   ((bir_vars_of_exp ^pre) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
        (* TODO: This is slow. Replace it with something faster later. *)
	val wp_var_thm = prove (``
	   ((bir_vars_of_exp ^wp) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val new_contract_thm = ((SIMP_RULE std_ss [contract_thm, taut_thm, wp_var_thm, pre_var_thm]) 
	  ((ISPECL [wp, pre, prog, entry, exit, post])
	      bir_wm_instTheory.bir_taut_pre_str_rule_thm)
	      );
      in
        new_contract_thm
      end;

    fun use_pre_str_rule_map map_ht_thm pre_impl_wp =
      let
	val map_ht_thm = SIMP_RULE std_ss [bir_bool_expTheory.bir_exp_and_def] map_ht_thm;
	val pre = ((el 2) o snd o strip_comb o (el 2) o snd o strip_comb o hd o snd o strip_comb o concl) pre_impl_wp;
	val prog = get_bir_map_triple_prog map_ht_thm;
        val invar = get_bir_map_triple_invariant map_ht_thm;
	val entry = get_bir_map_triple_start_label map_ht_thm;
	val wlist = get_bir_map_triple_wlist map_ht_thm;
	val blist = get_bir_map_triple_blist map_ht_thm;
	val post = get_bir_map_triple_post map_ht_thm;
	val wp = get_bir_map_triple_pre map_ht_thm;
	val taut_thm = computeLib.RESTR_EVAL_RULE [(fst o strip_comb) pre, ``bir_exp_is_taut``] pre_impl_wp;
        (* TODO: This is slow. Replace it with something faster later. *)
	val pre_var_thm = prove (``
	   ((bir_vars_of_exp ^pre) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
        (* TODO: This is slow. Replace it with something faster later. *)
	val wp_var_thm = prove (``
	   ((bir_vars_of_exp ^wp) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val new_contract_thm = ((SIMP_RULE std_ss [map_ht_thm, taut_thm, wp_var_thm, pre_var_thm]) 
	  ((ISPECL [prog, invar, entry, wlist, blist, wp, pre, post])
	      bir_wm_instTheory.bir_taut_map_pre_str_rule_thm)
	      );
      in
        new_contract_thm
      end;

    fun bir_map_triple_from_bir_triple tr =
      let
	val prog = get_contract_prog tr
	val l = get_contract_l tr
	val ls = get_contract_ls tr
	val pre = get_contract_pre tr
	val post = get_contract_post tr

	val map_equiv = ISPECL [prog, bir_bool_expSyntax.bir_exp_true_tm,
			     l, ls, pred_setSyntax.mk_empty ``:bir_label_t``,
			     pre, post] bir_wm_instTheory.bir_triple_equiv_map_triple_alt
        (* TODO: Review and describe what these steps are supposed to do *)
        (* Simplify union in ending label set *)
	val map_equiv2 =
	  SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] map_equiv
        (* Simplify eventual conjunctions with bir_exp_true in precondition. Expanding bir_triple
         * definition is needed for this. *)
        val map_equiv3 =
          SIMP_RULE std_ss
	    [bir_wm_instTheory.bir_triple_def,
             bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
	     bir_exp_equivTheory.bir_and_op2,
             bir_bool_expTheory.bir_is_bool_exp_env_REWRS] map_equiv2
        (* Fold precondition definition *)
	val map_equiv4 =
	  SIMP_RULE std_ss [GSYM bir_wm_instTheory.bir_exec_to_labels_triple_precond_def] map_equiv3
        (* Do the same for the postcondition *)
	val map_equiv5 =
	  SIMP_RULE std_ss
	    [bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def,
             bir_exp_equivTheory.bir_and_op2,
             bir_bool_expTheory.bir_is_bool_exp_env_REWRS] map_equiv4
        (* TODO: The below theorem might be needed for some HTs... *)
(*
        val spec_eta = ISPEC post boolTheory.ETA_THM
*)
        (* Fold postcondition and bir_triple definitions *)
	val map_equiv6 =
	  SIMP_RULE std_ss [GSYM bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def,
                            GSYM bir_wm_instTheory.bir_triple_def] map_equiv5
      in
	REWRITE_RULE [GSYM map_equiv6] tr
      end
    ;


    fun bir_remove_labels_from_ending_set ht new_ending_label_set =
      let
      val prog = get_contract_prog ht
      val start_label = get_contract_l ht
      val to_remove_label_set =
	pred_setSyntax.mk_set (
	  filter (fn tm => not (exists (term_eq tm) (pred_setSyntax.strip_set new_ending_label_set)))
		 (pred_setSyntax.strip_set (get_contract_ls ht))
	)
      val precondition = get_contract_pre ht
      val postcondition = get_contract_post ht

      val bir_spec_subset_rule_thm =
	ISPECL [prog,
		start_label,
		new_ending_label_set,
		to_remove_label_set,
		precondition,
		postcondition] bir_wm_instTheory.bir_subset_rule_thm
      val removal_ante_thm =
	prove ((fst o dest_imp o concl) bir_spec_subset_rule_thm,

	computeLib.RESTR_EVAL_TAC [``bir_val_true``, ``bir_exp_false``] >>
	GEN_TAC >>
	CASE_TAC >| [
	  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++
				 wordsLib.WORD_ss) [],

	  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_eval_exp_TF,
				bir_bool_expTheory.bir_val_TF_dist]
	]
	)

	val bir_spec_subset_rule_thm2 =
	  (fn thm => ONCE_REWRITE_RULE [bir_triple_tm_get_sort_ls_thm
                                          ((fst o dest_imp o concl) thm)] thm
          )
	  (SIMP_RULE (std_ss++HolBACoreSimps.bir_union_var_set_ss) []
	    (HO_MATCH_MP bir_spec_subset_rule_thm removal_ante_thm)
	  )

	val bir_spec_subset_rule_thm3 =
	  HO_MATCH_MP bir_spec_subset_rule_thm2
	   ((fn thm => ONCE_REWRITE_RULE [bir_triple_tm_get_sort_ls_thm (concl thm)] thm)
	      ht
	   )
      in
	bir_spec_subset_rule_thm3
      end
    ;


    local
    fun remove_label list label = filter (fn el => not (term_eq el label)) list

    fun bir_populate_blacklist' _ _ [] map_triple=
      map_triple
      | bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                 simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                (h::t) map_triple =
	  let
	    val elabel_post_is_false_tm = mk_comb ((get_bir_map_triple_post map_triple), h)
	    val elabel_post_is_false_thm =
	      SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
                [] elabel_post_is_false_tm
	    val elabel_post_is_false =
	      term_eq ((snd o dest_eq o concl) elabel_post_is_false_thm)
		bir_bool_expSyntax.bir_exp_false_tm
	  in
	    if elabel_post_is_false
	    then let
		   val new_map_triple1 =
		     HO_MATCH_MP bir_wm_instTheory.bir_map_triple_move_to_blacklist map_triple
		   val elabel_in_wlist = el_in_set_repr h (get_bir_map_triple_wlist map_triple)
		   val new_map_triple2 =
		     HO_MATCH_MP new_map_triple1 elabel_in_wlist
		   val new_map_triple3 =
		     HO_MATCH_MP new_map_triple2 (SIMP_RULE std_ss [] elabel_post_is_false_thm)
		   val new_map_triple4 =
		     simp_delete_set_repr_rule new_map_triple3
		   val new_map_triple5 =
		     simp_insert_set_repr_rule new_map_triple4
		 in
		   bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                            simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                           t new_map_triple5 
                     
		 end
	    else bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                          simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                         t map_triple  
	  end
    in
      fun bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule) map_triple =
	bir_populate_blacklist'
	  (get_labels_from_set_repr, el_in_set_repr, mk_set_repr, simp_delete_set_repr_rule,
	   simp_insert_set_repr_rule)
	  (get_bir_map_triple_post map_triple)
	  (get_labels_from_set_repr (get_bir_map_triple_wlist map_triple))
	  map_triple
    end
    ;

    (* This function composes a loop from a looping bir_map_triple and a loop exit bir_triple *)
    fun bir_compose_loop (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) loop_map_ht
          loop_exit_ht loop_invariant loop_condition loop_variant def_list = 
      let
	(* 1. Specialise bir_while_rule_thm *)
	val prog = get_contract_prog loop_exit_ht
	val start_label = get_bir_map_triple_start_label loop_map_ht
	val ending_label_set = get_contract_ls loop_exit_ht

	val bir_add_comp_while_rule_thm =
	  ISPECL [prog,
		  start_label,
		  ending_label_set,
		  loop_invariant,
		  loop_condition,
		  loop_variant,
		  get_contract_post loop_exit_ht] bir_wm_instTheory.bir_signed_while_rule_thm

	(* 2. Knock out antecedents:  *)
	(* Note: This structure enforces the property that each step only touches the
	 * relevant antecedent. This makes it clearer what is needed to do for each
	 * separate step, especially in failure states. *)
	(* type_of_bir_exp of variant should be 64-bit Imm *)
        (* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm1 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm,
				       SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
				     )] bir_add_comp_while_rule_thm

	(* Variables in variant should be subset of vars_of_prog *)
        (* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm2 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm1,
				       SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
					 def_list (* bir_add_reg_prog_def needed *)
				     )] bir_add_comp_while_rule_thm1

	(* Loop condition should be a Boolean expression *)
        (* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm3 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm2,
				       SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss)
					 def_list (* bir_add_reg_loop_condition_def needed *)
				     )] bir_add_comp_while_rule_thm2

	(* Variables in loop condition should be a subset of vars_of_prog *)
	(* TODO: Construct this antecedent explicitly in place (need maker for bir_vars_of_program) *)
	val bir_add_comp_while_rule_thm4 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm3,
				       SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
					 def_list (* bir_add_reg_loop_condition_def and
						     bir_add_reg_prog_def needed *)
				     )] bir_add_comp_while_rule_thm3

	(* Obtain the bir_signed_loop_contract from loop_ht and loop_continuation_ht and knock
         * out the corresponding antecedent *)
	(*   TODO: Make syntax functions for bir_signed_loop_contract *)
	(*   TODO: Make separate composition function for bir_signed_loop_contract *)
	val temp_cheat_thm =
	  prove(``bir_signed_loop_contract (^prog) (^start_label) (^ending_label_set)
                    (^loop_invariant) (^loop_condition) (^loop_variant)``,

	    SIMP_TAC std_ss [bir_wm_instTheory.bir_signed_loop_contract_def] >>
	    CONJ_TAC >| [
              simp_in_set_repr_tac,

              GEN_TAC >>
              ASSUME_TAC (Q.SPEC `x` (GEN_ALL loop_map_ht)) >>
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_triple_equiv_map_triple] >>
              FULL_SIMP_TAC (std_ss++inter_set_repr_ss++union_set_repr_ss) [] >>
              FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_triple_def,
                                    bin_hoare_logicTheory.weak_triple_def,
                                    bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
                                    bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def] >>
              REPEAT STRIP_TAC >>
              QSPECL_X_ASSUM ``!s. _`` [`s`] >>
              REV_FULL_SIMP_TAC std_ss [] >>
              FULL_SIMP_TAC std_ss (def_list@[bir_exp_equivTheory.bir_and_op2,
                                             bir_bool_expTheory.bir_is_bool_exp_env_REWRS]) >>
(* For debugging:
                  FULL_SIMP_TAC std_ss [GSYM bir_add_reg_prog_def] >>
*)
              REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
                [bir_valuesTheory.BType_Bool_def] >>
              Q.EXISTS_TAC `s'` >>
              FULL_SIMP_TAC std_ss [] >>
              REPEAT STRIP_TAC >| [
                (* Expression evaluation *)
                REPEAT CASE_TAC >> (
                  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
                    [bir_exp_equivTheory.bir_and_op2,
                     bir_bool_expTheory.bir_eval_exp_TF,
                     bir_bool_expTheory.bir_val_TF_dist]
                ),

                (* bool_exp_env *)
                REPEAT CASE_TAC >> (
                  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
                    [bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
                     bir_bool_expTheory.bir_exp_false_def]
                )
              ]
	    ]
	  )
	val bir_add_comp_while_rule_thm5 =
	  HO_MATCH_MP bir_add_comp_while_rule_thm4 temp_cheat_thm

	(* Finally, obtain conclusion through MP with loop_exit_ht and some piecing
         * together of precondition of loop_exit_ht and loop condition *)
	val bir_add_comp_while_rule_thm6 =
	  prove((snd o dest_imp o concl) bir_add_comp_while_rule_thm5,

	    irule bir_add_comp_while_rule_thm5 >>
	    ASSUME_TAC loop_exit_ht >>
	    FULL_SIMP_TAC std_ss def_list
	  )

      in
	bir_add_comp_while_rule_thm6
      end
    ;


    (* This function composes two bir_map_triples sequentially using bir_map_std_seq_comp_thm *)
    (* TODO: Fix the mess with def_list unfolding too much back and forth,
     *       see if RESTR_EVAL_RULE can be helpful *)
    fun bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
          map_ht1 map_ht2 def_list =
      let
	(* 1. Specialise bir_map_std_seq_comp_thm *)
	val prog = get_bir_map_triple_prog map_ht1
        val invariant = get_bir_map_triple_invariant map_ht1
	val white_ending_label_set1 = get_bir_map_triple_wlist map_ht1
	val white_ending_label_set2 = get_bir_map_triple_wlist map_ht2
	val black_ending_label_set1 = get_bir_map_triple_blist map_ht1
	val black_ending_label_set2 = get_bir_map_triple_blist map_ht2
	val start_label = get_bir_map_triple_start_label map_ht1
	val pre1 = get_bir_map_triple_pre map_ht1
	val post1 = get_bir_map_triple_post map_ht1
	val post2 = get_bir_map_triple_post map_ht2

        (* TODO: HO_MATCH_MP is not general enough to immediately knock out the bir_map_triple
         * antecedent before specialisation *)
	val bir_add_comp_seq_rule_thm =
	  ISPECL [prog, white_ending_label_set1, white_ending_label_set2,
		  black_ending_label_set1, black_ending_label_set2,
		  invariant, start_label, pre1, post1, post2]
	    bir_wm_instTheory.bir_map_std_seq_comp_thm

	(* 2. Knock out antecedents: *)
	(* Whitelist of HT2 should be subset of blacklist of HT1 *)
	val bir_add_comp_seq_rule_thm1 =
	  SIMP_RULE std_ss [prove (pred_setSyntax.mk_subset
                                     (white_ending_label_set2,
                                      black_ending_label_set1),

				       SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
                                         [pred_setTheory.SUBSET_DEF]
                            )] bir_add_comp_seq_rule_thm

	(* The intersection between whitelist of HT1 and whitelist of HT2 should be empty *)
        (* TODO: Does this work for larger than singleton sets? *)
	val spec_noteq_trans_impl1 =
	  ISPECL [el 1 (get_labels_from_set_repr white_ending_label_set1),
		  el 1 (get_labels_from_set_repr white_ending_label_set2)]
            bir_auxiliaryTheory.noteq_trans_impl
	val bir_add_comp_seq_rule_thm2 =
	  SIMP_RULE std_ss [prove (mk_eq
                                     (pred_setSyntax.mk_inter
                                        (white_ending_label_set1,
                                         white_ending_label_set2),
                                     pred_setSyntax.mk_empty bir_label_t_ty),
                            (* TODO: srw_ss()... *)
                            SIMP_TAC (srw_ss()) [pred_setTheory.INTER_DEF, pred_setTheory.IN_ABS,
                                                 spec_noteq_trans_impl1]
                            )] bir_add_comp_seq_rule_thm1

	(* The intersection between whitelist of HT2 and blacklist of HT2 should be empty *)
        (* TODO: Does this work for larger than singleton sets? *)
	val bir_add_comp_seq_rule_thm3 =
	  if not (pred_setSyntax.is_empty black_ending_label_set2)
	  then
            let
	      val spec_noteq_trans_impl2 =
		ISPECL [el 1 (get_labels_from_set_repr white_ending_label_set2),
			el 1 (get_labels_from_set_repr black_ending_label_set2)]
		  bir_auxiliaryTheory.noteq_trans_impl
            in
	      SIMP_RULE std_ss [prove(mk_eq
					(pred_setSyntax.mk_inter
					   (white_ending_label_set2,
					    black_ending_label_set2),
					 pred_setSyntax.mk_empty bir_label_t_ty),
				(* TODO: srw_ss()... *)
				SIMP_TAC (srw_ss()) [pred_setTheory.INTER_DEF,
						     pred_setTheory.IN_ABS,
						     spec_noteq_trans_impl2]
				)] bir_add_comp_seq_rule_thm2
            end
	  else
            HO_MATCH_MP
              bir_add_comp_seq_rule_thm2
              (ISPEC white_ending_label_set2 (CONJUNCT2 pred_setTheory.INTER_EMPTY))

	(* Knock out the bir_map_triple-antecedent *)
	val bir_add_comp_seq_rule_thm4 =
	  HO_MATCH_MP bir_add_comp_seq_rule_thm3 map_ht1

	(* Starting label of HT2 is the single label in whitelist of HT1
	 * Note: The theorem used for composition actually allows for multiple connection points *)
	val bir_add_comp_seq_rule_thm5 =
          simp_in_sing_set_repr_rule bir_add_comp_seq_rule_thm4
	(* Knock out the final antecedent with bir_loop_map_triple *)
	val bir_add_comp_seq_rule_thm6 =
          HO_MATCH_MP (SIMP_RULE std_ss def_list bir_add_comp_seq_rule_thm5)
            (SIMP_RULE std_ss def_list map_ht2)
        (* Clean-up the expanded definitions *)
	val bir_add_comp_seq_rule_thm7 =
          simp_inter_set_repr_rule (SIMP_RULE std_ss (map GSYM def_list) bir_add_comp_seq_rule_thm6)

      in
	bir_add_comp_seq_rule_thm7
      end
    ;

    (* This function composes two bir_triples sequentially using bir_map_std_seq_comp_thm *)
    fun bir_compose_nonmap_seq ht1 ht2 def_list (get_labels_from_set_repr, el_in_set_repr,
                                                 mk_set_repr, simp_delete_set_repr_rule,
	                                         simp_insert_set_repr_rule,
                                                 simp_in_sing_set_repr_rule,
                                                 simp_inter_set_repr_rule) =
      let
        val map_ht1 =
          bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                 (bir_map_triple_from_bir_triple ht1)
        val map_ht2 =
          bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                 (bir_map_triple_from_bir_triple ht2)
      in
        bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
          map_ht1 map_ht2 def_list
      end
    ;

  end
end
