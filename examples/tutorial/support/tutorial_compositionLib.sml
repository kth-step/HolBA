structure tutorial_compositionLib =
struct
  local
    open bslSyntax;
    open tutorial_bir_to_armSupportTheory;
    open tutorial_wpSupportLib;
  in
    fun get_contract_prog contract_thm = ((el 1) o snd o strip_comb o concl) contract_thm;
    fun get_contract_l contract_thm = ((el 2) o snd o strip_comb o concl) contract_thm;
    fun get_contract_ls contract_thm = ((el 3) o snd o strip_comb o concl) contract_thm;
    fun get_contract_pre contract_thm = ((el 4) o snd o strip_comb o concl) contract_thm;
    fun get_contract_post contract_thm = ((el 5) o snd o strip_comb o concl) contract_thm;

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

    fun use_impl_rule contract_thm pre_impl_wp =
      let
	val contract_thm = SIMP_RULE std_ss [bir_bool_expTheory.bir_exp_and_def] contract_thm;
	val pre = ((el 2) o snd o strip_comb o (el 2) o snd o strip_comb o hd o snd o strip_comb o concl) pre_impl_wp;
	val prog = get_contract_prog contract_thm;
	val entry = get_contract_l contract_thm;
	val exit = get_contract_ls contract_thm;
	val post = get_contract_post contract_thm;
	val wp = get_contract_pre contract_thm;
	val taut_thm = computeLib.RESTR_EVAL_RULE [(fst o strip_comb) pre, ``bir_exp_is_taut``] pre_impl_wp;
	val pre_var_thm = prove (``
	   ((bir_vars_of_exp ^pre) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val wp_var_thm = prove (``
	   ((bir_vars_of_exp ^wp) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val new_contract_thm = ((SIMP_RULE std_ss [contract_thm, taut_thm, wp_var_thm, pre_var_thm]) 
	  ((ISPECL [wp, pre, prog, entry, exit, post])
	      bir_triple_weak_rule_thm)
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
			     pre, post] bir_wm_instTheory.bir_triple_from_map_triple
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

    local
    fun remove_label list label = filter (fn el => not (term_eq el label)) list

    fun bir_populate_blacklist' [] map_triple post =
      map_triple
      | bir_populate_blacklist' (h::t) map_triple post =
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
		   val elabel_in_wlist =
		     prove (pred_setSyntax.mk_in (h, get_bir_map_triple_wlist map_triple),

		     SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
		     )
		   val new_map_triple2 =
		     HO_MATCH_MP new_map_triple1 elabel_in_wlist
		   val new_map_triple3 =
		     HO_MATCH_MP new_map_triple2 (SIMP_RULE std_ss [] elabel_post_is_false_thm)
		   (* TODO: Simplify DELETE and INSERT operations... 

		   val new_map_triple4 =
		     SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss)
		       [pred_setTheory.DELETE_DEF, pred_setTheory.DIFF_DEF]
		       new_map_triple3

		    *       Until these proof procedures have been created, we cheat... *)
		   val new_wl =
		     mk_lambda_lset_from_llist
		       (remove_label
                          (get_labels_from_lam_disj (get_bir_map_triple_wlist map_triple))
			  h)
		   val new_bl =
		     mk_lambda_lset_from_llist
		       ((get_labels_from_lam_disj (get_bir_map_triple_blist map_triple))@[h])
		   val new_map_triple4 =
		     bir_wm_instSyntax.mk_bir_map_triple (get_bir_map_triple_prog new_map_triple3,
							  get_bir_map_triple_invariant
                                                            new_map_triple3,
							  get_bir_map_triple_start_label
                                                            new_map_triple3,
							  new_wl,
							  new_bl,
							  get_bir_map_triple_pre new_map_triple3,
							  get_bir_map_triple_post new_map_triple3)
		 in
		   bir_populate_blacklist' t (prove (new_map_triple4, cheat)) post
		 end
	    else bir_populate_blacklist' t map_triple post
	  end
    in
      fun bir_populate_blacklist map_triple =
	bir_populate_blacklist'
	  (get_labels_from_lam_disj (get_bir_map_triple_wlist map_triple))
	  map_triple
	  (get_bir_map_triple_post map_triple)
    end
    ;

    (* This function composes a loop from a looping bir_map_triple and a loop exit bir_triple *)
    fun bir_compose_loop loop_map_ht loop_exit_ht loop_invariant loop_condition
          loop_variant def_list = 
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
		  get_contract_post loop_exit_ht] bir_wm_instTheory.bir_while_rule_thm

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

	(* Obtain the bir_loop_contract from loop_ht and loop_continuation_ht and knock
         * out the corresponding antecedent *)
	(*   TODO: Ending label set must be union of loop end (64) and post-loop (68 or 72?). *)
	(*   TODO: Postcondition must be a map which maps 64 to postcond and all else to false. *)
	(*   TODO: Should signed or unsigned comparisons be used? *)
	(*   TODO: Make syntax functions for bir_loop_contract *)
	(*   TODO: Make separate composition function for bir_loop_contract *)
	val temp_cheat_thm =
	  prove(``bir_loop_contract (^prog) (^start_label) (^ending_label_set) (^loop_invariant)
		    (^loop_condition) (^loop_variant)``,

	    SIMP_TAC std_ss [bir_wm_instTheory.bir_loop_contract_def] >>
	    CONJ_TAC >| [
	      SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
                [pred_setTheory.IN_ABS],

              GEN_TAC >>
              ASSUME_TAC (Q.SPEC `x` (GEN_ALL loop_map_ht)) >>
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_triple_from_map_triple_alt] >>
              (* TODO: Cheating on these set-theoretical operations for now *)
              Q.SUBGOAL_THEN `((\l. l = BL_Address (Imm64 64w)) UNION
                              (\l. (l = BL_Address (Imm64 64w)) \/
                                (l = BL_Address (Imm64 72w))
                              ) INTER
                              (\l. l = BL_Address (Imm64 72w))) =
                                ({BL_Address (Imm64 64w)} UNION (\x. x = BL_Address (Imm64 72w)))`
                (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
                  cheat
                ) >>
              (* TODO: Use def_list here... *)
              FULL_SIMP_TAC std_ss def_list >> (*[bir_add_reg_contract_3_pre_variant_def,
                                    GSYM bir_add_reg_loop_condition_def]*) 
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_triple_def,
                                    bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
                                    bir_exp_equivTheory.bir_and_op2,
                                    (* TODO: Make theorem similar to bir_and_op2 for
                                     *       bir_is_bool_exp_env so you can unfold definitions *)
                                    bir_bool_expTheory.bir_is_bool_exp_env_REWRS] >>
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def,
                                    bir_exp_equivTheory.bir_and_op2] >>
              (* Note: this also includes a conjunction with BIR True *)
              Q.SUBGOAL_THEN `!ex.
                              (\l. if l IN (\l. l = BL_Address (Imm64 64w)) then
                                      BExp_BinExp BIExp_And
				       (if l = BL_Address (Imm64 64w) then
					  ex
					else bir_exp_false) bir_exp_true
				   else bir_exp_false) =
                              (\l'. if l' = BL_Address (Imm64 64w) then
				      ex
				    else bir_exp_false)`
                (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
                cheat
              ) >>
              FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def
                                    (*bir_add_reg_contract_2_post_variant_def*)] >>
              (* TODO: At this point everything is done, apart from differing Signed vs. Unsigned
               *       comparisons *)
	      cheat
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
    fun bir_compose_seq map_ht1 map_ht2 def_list =
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
        (* TODO: This does not work for sets of more than one... *)
	val spec_noteq_trans_impl1 =
	  ISPECL [el 1 (get_labels_from_lam_disj white_ending_label_set1),
		  el 1 (get_labels_from_lam_disj white_ending_label_set2)]
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
        (* TODO: This does not work for sets of more than one... Make proof procedure for
         * intersections *)
	val bir_add_comp_seq_rule_thm3 =
	  if not (pred_setSyntax.is_empty black_ending_label_set2)
	  then
            let
	      val spec_noteq_trans_impl2 =
		ISPECL [el 1 (get_labels_from_lam_disj white_ending_label_set2),
			el 1 (get_labels_from_lam_disj black_ending_label_set2)]
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
          (* HT1 postcondition definition needed *)
	  SIMP_RULE std_ss [pred_setTheory.IN_ABS]
	    bir_add_comp_seq_rule_thm4
	(* Knock out the final antecedent with bir_loop_map_triple *)
	val bir_add_comp_seq_rule_thm6 =
          HO_MATCH_MP (SIMP_RULE std_ss def_list bir_add_comp_seq_rule_thm5)
            (SIMP_RULE std_ss def_list map_ht2)
        (* Clean-up the expanded definitions *)
        (* TODO: Simplify a stupid UNION in the blacklist of the result... *)
	val bir_add_comp_seq_rule_thm7 =
          (SIMP_RULE std_ss (map GSYM def_list) bir_add_comp_seq_rule_thm6)

      in
	bir_add_comp_seq_rule_thm7
      end
    ;

    (* This function composes two bir_triples sequentially using bir_map_std_seq_comp_thm *)
    fun bir_compose_nonmap_seq ht1 ht2 def_list =
      let
        val map_ht1 = bir_populate_blacklist (bir_map_triple_from_bir_triple ht1)
        val map_ht2 = bir_populate_blacklist (bir_map_triple_from_bir_triple ht2)
      in
        bir_compose_seq map_ht1 map_ht2 def_list
      end
    ;

  end
end
