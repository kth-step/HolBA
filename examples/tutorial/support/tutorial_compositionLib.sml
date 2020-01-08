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
    (* TODO: Is there any smarter way to do this? *)
    fun get_label_from_ls ls =
      (snd o dest_eq o Absyn.dest_AQ o snd o Absyn.dest_lam o Absyn.mk_AQ) ls;

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
	   ((bir_vars_of_exp ^pre) ⊆ (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val wp_var_thm = prove (``
	   ((bir_vars_of_exp ^wp) ⊆ (bir_vars_of_program ^prog))
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
	val map_equiv2 =
	  SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss)
	    [pred_setTheory.INTER_EMPTY, bir_wm_instTheory.bir_triple_def,
             bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
	     bir_exp_equivTheory.bir_and_op2,
             bir_bool_expTheory.bir_is_bool_exp_env_REWRS] map_equiv
	val map_equiv3 =
	  SIMP_RULE std_ss [GSYM bir_wm_instTheory.bir_exec_to_labels_triple_precond_def] map_equiv2
	val map_equiv4 =
	  SIMP_RULE std_ss
	    [bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def,
             bir_exp_equivTheory.bir_and_op2,
             bir_bool_expTheory.bir_is_bool_exp_env_REWRS] map_equiv3
	val map_equiv5 =
	  SIMP_RULE std_ss [GSYM bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def,
                            GSYM bir_wm_instTheory.bir_triple_def] map_equiv4
      in
	REWRITE_RULE [GSYM map_equiv5] tr
      end
    ;

    fun bir_compose_loop loop_ht loop_continuation_ht loop_exit_ht loop_invariant loop_condition
          loop_variant def_list = 
      let
	(* 1. Specialise bir_while_rule_thm *)
	val prog = get_contract_prog loop_ht
	val start_label = get_contract_l loop_continuation_ht
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
	val bir_add_comp_while_rule_thm1 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm,
				       SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
				     )] bir_add_comp_while_rule_thm

	(* Variables in variant should be subset of vars_of_prog *)
	val bir_add_comp_while_rule_thm2 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm1,
				       SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
					 def_list (* bir_add_reg_prog_def needed *)
				     )] bir_add_comp_while_rule_thm1

	(* Loop condition should be a Boolean expression *)
	val bir_add_comp_while_rule_thm3 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm2,
				       SIMP_TAC (std_ss++bir_expSimps.bir_is_bool_ss)
					 def_list (* bir_add_reg_loop_condition_def needed *)
				     )] bir_add_comp_while_rule_thm2

	(* Variables in loop condition should be a subset of vars_of_prog *)
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
	(*   TODO: Make composition function only for bir_loop_contract *)
	val temp_cheat_thm =
	  prove(``bir_loop_contract (^prog) (^start_label) (^ending_label_set) (^loop_invariant)
		    (^loop_condition) (^loop_variant)``,

	    SIMP_TAC std_ss [bir_wm_instTheory.bir_loop_contract_def] >>
	    CONJ_TAC >| [
	      SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
                [pred_setTheory.IN_ABS],

	      (* TODO: Use loop_ht and loop_continuation_ht here? *)
	      cheat
	    ]
	  )
	val bir_add_comp_while_rule_thm5 =
	  HO_MATCH_MP bir_add_comp_while_rule_thm4 temp_cheat_thm

	(* Finally, obtain conclusion through MP with loop_exit_ht and some piecing
         * together of precondition of loop_exit_ht and loop condition *)
	val bir_add_comp_while_rule_thm6 =
	  prove(((snd o dest_imp o concl) bir_add_comp_while_rule_thm5),

	    irule bir_add_comp_while_rule_thm5 >>
	    ASSUME_TAC loop_exit_ht >>
	    FULL_SIMP_TAC std_ss def_list
	  )

      in
	bir_add_comp_while_rule_thm6
      end
    ;

    fun bir_compose_seq ht1 ht2 def_list =
      let
	(* 1. Specialise bir_map_std_seq_comp_thm *)
	val prog = get_contract_prog ht1
	val white_ending_label_set1 = get_contract_ls ht1
	val white_ending_label_set2 = get_contract_ls ht2
	val black_ending_label_set1 = get_contract_ls ht2
	val black_ending_label_set2 = pred_setSyntax.mk_empty bir_label_t_ty
	val invariant = bir_bool_expSyntax.bir_exp_true_tm
	val start_label = get_contract_l ht1
	val pre1 = get_contract_pre ht1
	val post1 = get_contract_post ht1
	val post2 = get_contract_post ht2

	val bir_add_comp_seq_rule_thm =
	  ISPECL [prog, white_ending_label_set1, white_ending_label_set2,
		  black_ending_label_set1, black_ending_label_set2,
		  invariant, start_label, pre1, post1, post2]
	    bir_wm_instTheory.bir_map_std_seq_comp_thm

	(* 2. Knock out antecedents: *)
	(* Whitelist of HT2 should be subset of blacklist of HT1 *)
	val bir_add_comp_seq_rule_thm1 =
	  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) bir_add_comp_seq_rule_thm)``,
				       SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
				     )] bir_add_comp_seq_rule_thm

	(* The intersection between whitelist of HT1 and whitelist of HT2 should be empty *)
	val spec_noteq_trans_impl =
	  ISPECL [get_label_from_ls white_ending_label_set1,
		  get_label_from_ls black_ending_label_set1] bir_auxiliaryTheory.noteq_trans_impl
	val bir_add_comp_seq_rule_thm2 =
	  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) bir_add_comp_seq_rule_thm1)``,
				       SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++pred_setLib.PRED_SET_ss)
					 [pred_setTheory.INTER_DEF, pred_setTheory.IN_ABS] >>
				       (* TODO: srw_ss() here... *)
				       FULL_SIMP_TAC (srw_ss()) [spec_noteq_trans_impl]
				     )] bir_add_comp_seq_rule_thm1

	(* The intersection between whitelist of HT2 and blacklist of HT2 should be empty *)
	val bir_add_comp_seq_rule_thm3 =
	  SIMP_RULE std_ss [prove(``^((fst o dest_imp o concl) bir_add_comp_seq_rule_thm2)``,
				       SIMP_TAC std_ss [pred_setTheory.INTER_EMPTY]
				     )] bir_add_comp_seq_rule_thm2

	(* Obtain the bir_map_triple from ht1 and knock out the corresponding antecedent *)
	(* Translate first HT to map_triple *)
	val bir_intro_map_triple = bir_map_triple_from_bir_triple ht1

	(* TODO: bir_add_contract_1 must have address 72 in blacklist (ensure this during generation).
	 *       Do modus ponens with the correct contract as "bir_intro_map_triple"
	 *       here when you have it... *)
	val bir_add_comp_seq_rule_thm4 =
	  prove(``^((snd o dest_imp o concl) bir_add_comp_seq_rule_thm3)``,
	    cheat
	  );

	(* Obtain the bir_map_triple from ht1 and knock out the corresponding antecedent *)
	val bir_loop_map_triple = bir_map_triple_from_bir_triple ht2;
	(* Starting label of HT2 is the single label in whitelist of HT1
	 * Note: The theorem used for composition actually allows for multiple connection points *)
	val bir_add_comp_seq_rule_thm5 =
          (* HT1 postcondition definition needed *)
	  SIMP_RULE std_ss ([pred_setTheory.IN_ABS]@def_list)
	    bir_add_comp_seq_rule_thm4;
	(* Knock out the final antecedent with bir_loop_map_triple *)
	val bir_add_comp_seq_rule_thm6 = HO_MATCH_MP bir_add_comp_seq_rule_thm5 bir_loop_map_triple;
      in
	bir_add_comp_seq_rule_thm6
      end
    ;

  end
end
