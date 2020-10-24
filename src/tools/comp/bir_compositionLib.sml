structure bir_compositionLib =
struct
  local

(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

    open bslSyntax;
    open bir_wp_interfaceLib;
    open bir_auxiliaryLib;
    open HolBACoreSimps;
  in

    (* These functions obtains the parameters of a
     * bir_exec_to_labels_triple *)
    fun get_contract_prog contract_thm = ((el 1) o snd o strip_comb o concl) contract_thm;
    fun get_contract_l contract_thm = ((el 2) o snd o strip_comb o concl) contract_thm;
    fun get_contract_ls contract_thm = ((el 3) o snd o strip_comb o concl) contract_thm;
    fun get_contract_pre contract_thm = ((el 4) o snd o strip_comb o concl) contract_thm;
    fun get_contract_post contract_thm = ((el 5) o snd o strip_comb o concl) contract_thm;

    (* These functions obtains the parameters of a
     * bir_simp_jgmt *)
    fun get_bir_simp_jgmt_prog map_triple = ((el 1) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_invariant map_triple = ((el 2) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_start_label map_triple = ((el 3) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_wlist map_triple = ((el 4) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_blist map_triple = ((el 5) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_pre map_triple = ((el 6) o snd o strip_comb o concl) map_triple;
    fun get_bir_simp_jgmt_post map_triple = ((el 7) o snd o strip_comb o concl) map_triple;

    fun bir_simp_jgmt_tm_get_sort_ls_thm ct_tm =
      let
	val ls = ((el 4) o snd o strip_comb) ct_tm
	val sorted_ls =
          pred_setSyntax.mk_set (ins_sort_tm (pred_setSyntax.strip_set ls))
      in 
	EQT_ELIM (computeLib.EVAL_CONV (mk_eq (ls, sorted_ls)))
      end
    ;

    (* TODO: Is there any smarter way to do this? *)
    fun mk_lambda_lset_from_llist label_list =
      ``\x. ^(list_mk_disj (map (curry mk_eq (mk_var ("x", bir_label_t_ty))) label_list))``

    val string_ss = rewrites (type_rws ``:string``);
    val char_ss = rewrites (type_rws ``:char``);

    val vars_ss = std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss;

    fun remove_foralls t = (remove_foralls o snd o dest_forall) t
                           handle HOL_ERR _ => t;

    fun use_pre_str_rule_simp simp_ct_thm pre_impl_wp =
      let
	val simp_ct_thm = SIMP_RULE std_ss [bir_bool_expTheory.bir_exp_and_def] simp_ct_thm;
        val pre_wo = (remove_foralls o concl) pre_impl_wp;
	val pre = ((el 2) o snd o strip_comb o (el 2) o snd o strip_comb o hd o snd o strip_comb) pre_wo;
	val prog = get_bir_simp_jgmt_prog simp_ct_thm;
        val invar = get_bir_simp_jgmt_invariant simp_ct_thm;
	val entry = get_bir_simp_jgmt_start_label simp_ct_thm;
	val wlist = get_bir_simp_jgmt_wlist simp_ct_thm;
	val blist = get_bir_simp_jgmt_blist simp_ct_thm;
	val post = get_bir_simp_jgmt_post simp_ct_thm;
	val wp = get_bir_simp_jgmt_pre simp_ct_thm;
        val taut_eq_thm = computeLib.RESTR_EVAL_CONV [(fst o strip_comb) pre, ``bir_exp_is_taut``] (concl pre_impl_wp);
	val taut_thm = EQ_MP taut_eq_thm pre_impl_wp;
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
	val new_contract_thm = ((SIMP_RULE std_ss [simp_ct_thm, taut_thm, taut_eq_thm,
                                                   pre_impl_wp, wp_var_thm, pre_var_thm]) 
	  ((ISPECL [prog, invar, entry, wlist, blist, wp, pre, post])
	      bir_wm_instTheory.bir_simp_taut_pre_str_rule_thm)
	      );
      in
        new_contract_thm
      end;

    fun use_post_weak_rule_simp simp_ct_thm l2 post1_impl_post2 =
      let
	val simp_ct_thm = SIMP_RULE std_ss [bir_bool_expTheory.bir_exp_and_def] simp_ct_thm;
        val post2e_wo = (remove_foralls o concl) post1_impl_post2;
	val post2e = ((el 3) o snd o strip_comb o hd o snd o strip_comb) post2e_wo;
	val prog = get_bir_simp_jgmt_prog simp_ct_thm;
        val invar = get_bir_simp_jgmt_invariant simp_ct_thm;
	val entry = get_bir_simp_jgmt_start_label simp_ct_thm;
	val wlist = get_bir_simp_jgmt_wlist simp_ct_thm;
	val blist = get_bir_simp_jgmt_blist simp_ct_thm;
	val post1 = get_bir_simp_jgmt_post simp_ct_thm;
        val post2 = ``\l. if l = ^l2 then ^post2e else ^post1 l``;
	val pre = get_bir_simp_jgmt_pre simp_ct_thm;
        val taut_eq_thm = computeLib.RESTR_EVAL_CONV [(fst o strip_comb) post2e, ``bir_exp_is_taut``] (concl post1_impl_post2);
	val taut_thm = EQ_MP taut_eq_thm post1_impl_post2;
        (* TODO: This is slow. Replace it with something faster later. *)
	val post2_var_thm = prove (``
	   ((bir_vars_of_exp (^post2 ^l2)) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
        (* TODO: This is slow. Replace it with something faster later. *)
	val post1_var_thm = prove (``
	   ((bir_vars_of_exp (^post1 ^l2)) SUBSET (bir_vars_of_program ^prog))
	   ``,
	   computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
	   (SIMP_TAC vars_ss
	   ) [bir_valuesTheory.BType_Bool_def]
	);
	val new_contract_thm = ((SIMP_RULE (std_ss++HolBACoreSimps.bir_TYPES_ss++wordsLib.WORD_ss)
                                           [simp_ct_thm, taut_thm, taut_eq_thm,
                                            post1_impl_post2, post1_var_thm, post2_var_thm]) 
	  ((ISPECL [prog, invar, entry, wlist, l2, blist, pre, post1, post2])
	      bir_wm_instTheory.bir_simp_taut_post_weak_rule_thm)
	      );
      in
        new_contract_thm
      end;

    fun bir_remove_labels_from_wlist
      not_empty_set_repr ct new_wlist =
      let
	val prog = get_bir_simp_jgmt_prog ct
	val start_label = get_bir_simp_jgmt_start_label ct
	val label_set = get_bir_simp_jgmt_wlist ct
	val to_remove_label_set = 
	  pred_setSyntax.mk_set (
	    filter (fn tm => not (exists (term_eq tm) (pred_setSyntax.strip_set new_wlist)))
		   (pred_setSyntax.strip_set label_set)
	  )
	val precondition = get_bir_simp_jgmt_pre ct
	val postcondition = get_bir_simp_jgmt_post ct

	val bir_spec_subset_rule_thm =
	  ISPECL [prog,
		  start_label,
		  new_wlist,
		  to_remove_label_set,
		  precondition,
		  postcondition] bir_wm_instTheory.bir_simp_wl_subset_rule_thm

	val bir_spec_subset_rule_thm1 =
	  (HO_MATCH_MP bir_spec_subset_rule_thm (not_empty_set_repr new_wlist))

	val removal_ante_thm =
	  prove ((fst o dest_imp o concl) bir_spec_subset_rule_thm1,

	  computeLib.RESTR_EVAL_TAC [``bir_val_true``, ``bir_exp_false``] >>
	  GEN_TAC >>
	  CASE_TAC >| [
	    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++
				   wordsLib.WORD_ss) [],

	    FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_eval_exp_TF,
				  bir_bool_expTheory.bir_val_TF_dist] >>
	    REWRITE_TAC [Once (prove(``A ==> ~B <=> B ==> ~A``, METIS_TAC [boolTheory.MONO_NOT_EQ]))] >>
	    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++pred_setLib.PRED_SET_ss++wordsLib.WORD_ss)
		    [bir_bool_expTheory.bir_eval_exp_TF,
				  bir_bool_expTheory.bir_val_TF_dist]
	  ]
	  )

	  val bir_spec_subset_rule_thm2 =
	    (fn thm => ONCE_REWRITE_RULE [bir_simp_jgmt_tm_get_sort_ls_thm
					    ((fst o dest_imp o concl) thm)] thm
	    )
	    (SIMP_RULE (std_ss++HolBACoreSimps.bir_union_var_set_ss) []
	      (HO_MATCH_MP bir_spec_subset_rule_thm1 removal_ante_thm)
	    )

	  val bir_spec_subset_rule_thm3 =
	    HO_MATCH_MP bir_spec_subset_rule_thm2
	     ((fn thm => ONCE_REWRITE_RULE [bir_simp_jgmt_tm_get_sort_ls_thm (concl thm)] thm)
		ct
	     )
      in
	bir_spec_subset_rule_thm3
      end
    ;

    (* This function applies bir_simp_bl_subset_rule_thm
     * to a contract, given a set of labels to remove from the
     * blacklist *)
    fun bir_remove_labels_from_blist (simp_in_set_repr_tac) map_ct to_remove_from_blist =
      let
	val prog = get_bir_simp_jgmt_prog map_ct
        val invariant = get_bir_simp_jgmt_invariant map_ct
	val start_label = get_bir_simp_jgmt_start_label map_ct
        val wlist = get_bir_simp_jgmt_wlist map_ct
        val blist = get_bir_simp_jgmt_blist map_ct
        (* TODO: Parametrize this over different set representations *)
        val new_blist_sml =
          filter (fn tm => not (exists (term_eq tm) (pred_setSyntax.strip_set to_remove_from_blist)))
		 (pred_setSyntax.strip_set blist)
	val new_blist =
          if null new_blist_sml
          then pred_setSyntax.mk_empty bir_label_t_ty
	  else pred_setSyntax.mk_set new_blist_sml
	val precondition = get_bir_simp_jgmt_pre map_ct
	val postcondition = get_bir_simp_jgmt_post map_ct

      val bir_spec_subset_rule_thm =
	ISPECL [prog,
                invariant,
                start_label,
                wlist,
		blist,
		new_blist,
		precondition,
		postcondition] bir_wm_instTheory.bir_simp_bl_subset_rule_thm

      val bir_spec_subset_rule_thm2 =
	SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_spec_subset_rule_thm,
				     simp_in_set_repr_tac
				   )] bir_spec_subset_rule_thm

	val bir_spec_subset_rule_thm3 =
	  HO_MATCH_MP bir_spec_subset_rule_thm2
	   map_ct
      in
	bir_spec_subset_rule_thm3
      end
    ;

    local
    fun remove_label list label = filter (fn el => not (term_eq el label)) list

    fun bir_populate_blacklist' _ _ [] map_triple assmpt=
      map_triple
      | bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr,
                                 mk_set_repr, simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                (h::t) map_triple assmpt =
	  let
            (* First, check if postcondition holds for the current label h in the list of
             * exit labels *)
	    val elabel_post_is_false_tm = mk_comb ((get_bir_simp_jgmt_post map_triple), h)
	    val elabel_post_is_false_thm =
	      SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
                [ASSUME assmpt] elabel_post_is_false_tm
	    val elabel_post_is_false =
	      term_eq ((snd o dest_eq o concl) elabel_post_is_false_thm)
		bir_bool_expSyntax.bir_exp_false_tm
	  in
	    if elabel_post_is_false
	    then let
                   (* Apply bir_simp_wl_to_bl_rule_thm and compute antecedents *)
		   val new_map_triple1 =
		     HO_MATCH_MP bir_wm_instTheory.bir_simp_wl_to_bl_rule_thm map_triple
                   (* elabel IN wlist *)
		   val elabel_in_wlist = el_in_set_repr h (get_bir_simp_jgmt_wlist map_triple)
		   val new_map_triple2 =
		     HO_MATCH_MP new_map_triple1 elabel_in_wlist
                   (* wlist DELETE elabel <> {} *)
                   val delete_elabel_notempty =
                     delete_not_empty_set_repr h (get_bir_simp_jgmt_wlist map_triple)
		   val new_map_triple3 =
		     HO_MATCH_MP new_map_triple2 delete_elabel_notempty
                   (* post elabel = bir_exp_false *)
		   val new_map_triple4 =
		     HO_MATCH_MP new_map_triple3 (SIMP_RULE std_ss [] elabel_post_is_false_thm)
                   (* Finalize with assumption and INSERT and DELETE simplification *)
		   val new_map_triple5 =
                     SIMP_RULE std_ss [ASSUME assmpt]
		     (simp_delete_set_repr_rule new_map_triple4)
		   val new_map_triple6 =
		     simp_insert_set_repr_rule new_map_triple5
		 in
		   bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr,
                                            delete_not_empty_set_repr, mk_set_repr,
                                            simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                           t new_map_triple5 assmpt
		 end
	    else bir_populate_blacklist' (get_labels_from_set_repr, el_in_set_repr,
                                          delete_not_empty_set_repr, mk_set_repr,
                                          simp_delete_set_repr_rule, simp_insert_set_repr_rule) post
                                         t map_triple assmpt
	  end
    in
      fun bir_populate_blacklist_assmpt (get_labels_from_set_repr, el_in_set_repr,
                                         delete_not_empty_set_repr, mk_set_repr,
                                         simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                        map_triple assmpt =
	bir_populate_blacklist'
	  (get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr, mk_set_repr,
           simp_delete_set_repr_rule, simp_insert_set_repr_rule)
	  (get_bir_simp_jgmt_post map_triple)
	  (get_labels_from_set_repr (get_bir_simp_jgmt_wlist map_triple))
	  map_triple assmpt

      fun bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr,
                                  delete_not_empty_set_repr, mk_set_repr,
                                  simp_delete_set_repr_rule, simp_insert_set_repr_rule) map_triple =
	bir_populate_blacklist'
	  (get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr, mk_set_repr,
           simp_delete_set_repr_rule, simp_insert_set_repr_rule)
	  (get_bir_simp_jgmt_post map_triple)
	  (get_labels_from_set_repr (get_bir_simp_jgmt_wlist map_triple))
	  map_triple T
    end
    ;

    (* This function translates a bir_exec_to_labels_triple to bir_simp_jgmt,
     * and abbreviates the precondition according to a given tautology *)
    fun label_ct_to_simp_ct (not_empty_set_repr, get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr,
                            mk_set_repr, simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                           label_ct taut_thm =
      bir_populate_blacklist (get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr,
                              mk_set_repr, simp_delete_set_repr_rule, simp_insert_set_repr_rule)
	(use_pre_str_rule_simp
	  (HO_MATCH_MP
	    (HO_MATCH_MP bir_wm_instTheory.bir_label_jgmt_impl_weak_jgmt (not_empty_set_repr (get_contract_ls label_ct))) label_ct
	  )
	  taut_thm
	)
      ;

    fun label_ct_to_simp_ct_assmpt (not_empty_set_repr, get_labels_from_set_repr, el_in_set_repr, delete_not_empty_set_repr,
                                   mk_set_repr, simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                  label_ct taut_thm assmpt =
      bir_populate_blacklist_assmpt (get_labels_from_set_repr, el_in_set_repr,
                                     delete_not_empty_set_repr, mk_set_repr,
			             simp_delete_set_repr_rule, simp_insert_set_repr_rule)
	(use_pre_str_rule_simp
	  (HO_MATCH_MP
            (HO_MATCH_MP bir_wm_instTheory.bir_label_jgmt_impl_weak_jgmt (not_empty_set_repr (get_contract_ls label_ct))
            ) (UNDISCH_ALL (SPEC_ALL label_ct))
	  )
	  taut_thm
	) assmpt;

    fun label_ct_to_simp_ct_no_taut_assmpt (not_empty_set_repr, get_labels_from_set_repr, el_in_set_repr,
                                           delete_not_empty_set_repr, mk_set_repr,
			                   simp_delete_set_repr_rule, simp_insert_set_repr_rule)
                                          label_ct assmpt =
      bir_populate_blacklist_assmpt (get_labels_from_set_repr, el_in_set_repr,
                                     delete_not_empty_set_repr, mk_set_repr,
			             simp_delete_set_repr_rule, simp_insert_set_repr_rule)
	  (HO_MATCH_MP
            (HO_MATCH_MP bir_wm_instTheory.bir_label_jgmt_impl_weak_jgmt (not_empty_set_repr (get_contract_ls label_ct))
            ) (UNDISCH_ALL (SPEC_ALL label_ct))
	  ) assmpt;

    (* This function composes a loop from a looping contract and a loop exit contract *)
    fun bir_compose_simp_loop (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) loop_map_ct
          loop_exit_map_ct loop_invariant loop_condition loop_variant prog_def def_list = 
      let
	(* 1. Specialise bir_simp_signed_loop_rule_thm *)
	val prog = get_bir_simp_jgmt_prog loop_exit_map_ct
	val start_label = get_bir_simp_jgmt_start_label loop_map_ct
	val wlist = get_bir_simp_jgmt_wlist loop_exit_map_ct
	val blist = get_bir_simp_jgmt_blist loop_exit_map_ct

	val bir_add_comp_while_rule_thm =
	  ISPECL [prog,
		  start_label,
		  wlist,
		  blist,
		  loop_invariant,
		  loop_condition,
		  loop_variant,
		  get_bir_simp_jgmt_post loop_exit_map_ct]
                 bir_wm_instTheory.bir_simp_signed_loop_rule_thm

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
					 [prog_def]
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
					 (def_list@[prog_def]) (* bir_add_reg_loop_condition_def and
						                  bir_add_reg_prog_def needed *)
				     )] bir_add_comp_while_rule_thm3

	(* Start label should not be in whitelist *)
	(* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm5 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm4,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm4

	(* Start label should not be in blacklist *)
	(* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm6 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm5,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm5

	(* Intersection of whitelist and blacklist should be empty set *)
	(* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm7 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm6,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm6

	(* Obtain the loop contract in required format and knock out the
         * corresponding antecedent *)
	(*   TODO: Make separate function for this *)
	val new_loop_map_ct =
	  prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm7,
	    GEN_TAC >>
	    ASSUME_TAC (Q.SPEC `x` (GEN_ALL loop_map_ct)) >>
(*
	    FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_triple_equiv_simp_jgmt] >>
*)
	    FULL_SIMP_TAC (std_ss++inter_set_repr_ss++union_set_repr_ss) [] >>
	    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
	    FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_simp_jgmt_def,
				  abstract_simp_hoare_logicTheory.abstract_simp_jgmt_def,
				  abstract_hoare_logicTheory.abstract_jgmt_def,
				  bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
				  bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def] >>
	    REPEAT STRIP_TAC >> (
              FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
            ) >>
	    QSPECL_X_ASSUM ``!s. _`` [`s`] >>
	    REV_FULL_SIMP_TAC std_ss [] >>
	    FULL_SIMP_TAC std_ss (def_list@[bir_exp_equivTheory.bir_and_op2,
					   bir_bool_expTheory.bir_is_bool_exp_env_REWRS]) >>
	    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
	      [bir_valuesTheory.BType_Bool_def, (GSYM bir_exp_equivTheory.bir_and_equiv), bir_bool_expTheory.bir_eval_exp_TF] >>
	    Q.EXISTS_TAC `s''` >>
	    FULL_SIMP_TAC std_ss [] >>
	    REPEAT STRIP_TAC >| [
              (* Union in ending label set of weak transition  *)
              FULL_SIMP_TAC (std_ss++union_set_repr_ss) [],

	      (* Expression evaluation *)
	      REPEAT CASE_TAC >> (
		FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
		  [bir_exp_equivTheory.bir_and_op2,
		   bir_bool_expTheory.bir_eval_exp_TF,
		   bir_bool_expTheory.bir_val_TF_dist, GSYM bir_exp_equivTheory.bir_and_equiv]
	      ),

	      (* bool_exp_env *)
	      REPEAT CASE_TAC >> (
		FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
		  [bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
                   bir_bool_expTheory.bir_eval_exp_TF,
                   bir_bool_expTheory.bir_val_TF_dist,
		   bir_bool_expTheory.bir_exp_false_def]
	      ),

              (* Evaluation of invariant *)
              Cases_on `s''.bst_pc.bpc_label = (^start_label)` >> (
                FULL_SIMP_TAC std_ss
		  [GSYM bir_exp_equivTheory.bir_and_equiv,
                   bir_bool_expTheory.bir_eval_exp_TF,
                   bir_bool_expTheory.bir_val_TF_dist]
              ),

              (* bool_exp_env of invariant *)
	      FULL_SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS)
		[bir_bool_expTheory.bir_is_bool_exp_env_def, bir_wm_instTheory.bir_etl_wm_def, bir_wm_instTheory.bir_weak_trs_def] >>
              Cases_on `bir_exec_to_labels
              (^(pred_setSyntax.mk_set [start_label]) UNION (^wlist))
              (bir_add_reg_prog:'observation_type bir_program_t) s` >> (
                FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_programTheory.bir_exec_to_labels_def]
              ) >>
              IMP_RES_TAC bir_program_env_orderTheory.bir_exec_to_labels_n_ENV_ORDER >>
              METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_ORDER]
	    ]
	  )
	val bir_add_comp_while_rule_thm8 =
	  HO_MATCH_MP bir_add_comp_while_rule_thm7 new_loop_map_ct

	(* Finally, obtain conclusion through MP with loop exit contract and some piecing
         * together of precondition of loop exit and loop condition *)
	val bir_add_comp_while_rule_thm9 =
	  prove((snd o dest_imp o concl) bir_add_comp_while_rule_thm8,

	    irule bir_add_comp_while_rule_thm8 >>
	    ASSUME_TAC loop_exit_map_ct >>
	    FULL_SIMP_TAC std_ss def_list
	  )

      in
	bir_add_comp_while_rule_thm9
      end
    ;

    (* This function composes a loop from a looping bir_simp_jgmt
     * and a loop exit bir_simp_jgmt *)
    fun bir_compose_simp_loop_unsigned (simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) loop_map_ct
          loop_exit_map_ct loop_invariant loop_condition loop_variant prog_def def_list = 
      let
	(* 1. Specialise bir_simp_unsigned_loop_rule_thm *)
	val prog = get_bir_simp_jgmt_prog loop_exit_map_ct
	val start_label = get_bir_simp_jgmt_start_label loop_map_ct
	val wlist = get_bir_simp_jgmt_wlist loop_exit_map_ct
	val blist = get_bir_simp_jgmt_blist loop_exit_map_ct

	val bir_add_comp_while_rule_thm =
	  ISPECL [prog,
		  start_label,
		  wlist,
		  blist,
		  loop_invariant,
		  loop_condition,
		  loop_variant,
		  get_bir_simp_jgmt_post loop_exit_map_ct]
                 bir_wm_instTheory.bir_simp_unsigned_loop_rule_thm

	(* 2. Knock out antecedents:  *)
	(* Note: This structure enforces the property that each step only touches the
	 * relevant antecedent. This makes it clearer what is needed to do for each
	 * separate step, especially in failure states. *)
	(* type_of_bir_exp of variant should be 64-bit Imm *)
        (* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm1 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm,
				       SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) def_list
				     )] bir_add_comp_while_rule_thm

	(* Variables in variant should be subset of vars_of_prog *)
        (* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm2 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm1,
				       SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
					 (prog_def::def_list)
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
					 (prog_def::def_list) (* bir_add_reg_loop_condition_def and
						     bir_add_reg_prog_def needed *)
				     )] bir_add_comp_while_rule_thm3

	(* Start label should not be in whitelist *)
	val bir_add_comp_while_rule_thm5 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm4,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm4

	(* Start label should not be in blacklist *)
	(* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm6 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm5,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm5

	(* Intersection of whitelist and blacklist should be empty set *)
	(* TODO: Construct this antecedent explicitly in place *)
	val bir_add_comp_while_rule_thm7 =
	  SIMP_RULE std_ss [prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm6,
				       simp_in_set_repr_tac
				     )] bir_add_comp_while_rule_thm6

	val new_loop_map_ct =
	  prove((fst o dest_imp o concl) bir_add_comp_while_rule_thm7,
	    GEN_TAC >>
	    ASSUME_TAC (Q.SPEC `x` (GENL [``v:word64``] loop_map_ct)) >>
	    FULL_SIMP_TAC (std_ss++inter_set_repr_ss++union_set_repr_ss) [] >>
	    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] >>
	    FULL_SIMP_TAC std_ss [bir_wm_instTheory.bir_simp_jgmt_def,
				  abstract_simp_hoare_logicTheory.abstract_simp_jgmt_def,
				  abstract_hoare_logicTheory.abstract_jgmt_def,
				  bir_wm_instTheory.bir_exec_to_labels_triple_precond_def,
				  bir_wm_instTheory.bir_exec_to_labels_triple_postcond_def] >>
	    REPEAT STRIP_TAC >> (
              FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
            ) >>
	    QSPECL_X_ASSUM ``!s. _`` [`s`] >>
	    REV_FULL_SIMP_TAC std_ss [] >>
	    FULL_SIMP_TAC std_ss (def_list@[bir_exp_equivTheory.bir_and_op2,
					   bir_bool_expTheory.bir_is_bool_exp_env_REWRS]) >>
	    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
	      [bir_valuesTheory.BType_Bool_def, (GSYM bir_exp_equivTheory.bir_and_equiv), bir_bool_expTheory.bir_eval_exp_TF] >>
	    Q.EXISTS_TAC `s''` >>
	    FULL_SIMP_TAC std_ss [] >>
	    REPEAT STRIP_TAC >> (
              FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
                [bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY]
            ) >| [
              (* 1. Union in ending label set of weak transition  *)
              FULL_SIMP_TAC (std_ss++union_set_repr_ss) [],

	      (* 2. Expression evaluation *)
	      REPEAT CASE_TAC >> (
		FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
		  [bir_exp_equivTheory.bir_and_op2,
		   bir_bool_expTheory.bir_eval_exp_TF,
		   bir_bool_expTheory.bir_val_TF_dist, GSYM bir_exp_equivTheory.bir_and_equiv]
	      ),

	      (* 3. bool_exp_env *)
	      REPEAT CASE_TAC >> (
		FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss)
		  [bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
                   bir_bool_expTheory.bir_eval_exp_TF,
                   bir_bool_expTheory.bir_val_TF_dist,
		   bir_bool_expTheory.bir_exp_false_def]
	      ),

              (* 4. Evaluation of invariant *)
              Cases_on `s''.bst_pc.bpc_label = (^start_label)` >> (
                FULL_SIMP_TAC std_ss
		  [GSYM bir_exp_equivTheory.bir_and_equiv,
                   bir_bool_expTheory.bir_eval_exp_TF,
                   bir_bool_expTheory.bir_val_TF_dist] >>
                FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
              ),

              (* bool_exp_env of invariant *)
	      FULL_SIMP_TAC (std_ss++abstract_hoare_logicSimps.bir_wm_SS)
		[bir_bool_expTheory.bir_is_bool_exp_env_def, bir_wm_instTheory.bir_etl_wm_def, bir_wm_instTheory.bir_weak_trs_def] >>
              Cases_on `bir_exec_to_labels
              (^(pred_setSyntax.mk_set [start_label]) UNION (^wlist))
              (bprog_is_even_odd:'a bir_program_t) s` >> (
                FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_programTheory.bir_exec_to_labels_def]
              ) >>
              IMP_RES_TAC bir_program_env_orderTheory.bir_exec_to_labels_n_ENV_ORDER >>
              METIS_TAC [bir_env_oldTheory.bir_env_vars_are_initialised_ORDER]
	    ]
	  )

	val bir_add_comp_while_rule_thm8 =
	  HO_MATCH_MP bir_add_comp_while_rule_thm7 new_loop_map_ct

	(* Finally, obtain conclusion through MP with loop_exit_map_ct and some piecing
         * together of precondition of loop_exit_map_ct and loop condition *)
	val bir_add_comp_while_rule_thm9 =
	  prove((snd o dest_imp o concl) bir_add_comp_while_rule_thm8,

	    irule bir_add_comp_while_rule_thm8 >>
	    ASSUME_TAC loop_exit_map_ct >>
	    FULL_SIMP_TAC std_ss def_list
	  )

      in
	bir_add_comp_while_rule_thm9
      end
    ;

    (* This function composes two bir_simp_jgmts sequentially using bir_simp_std_seq_rule_thm *)
    (* TODO: Fix the mess with def_list unfolding too much back and forth,
     *       see if RESTR_EVAL_RULE can be helpful *)
    fun bir_compose_seq_assmpt (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                                simp_inter_set_repr_rule)
          simp_ct1 simp_ct2 def_list assmpt =
      let
	(* 1. Specialise bir_simp_std_seq_rule_thm *)
	val prog = get_bir_simp_jgmt_prog simp_ct1
        val invariant = get_bir_simp_jgmt_invariant simp_ct1
	val white_ending_label_set1 = get_bir_simp_jgmt_wlist simp_ct1
	val white_ending_label_set2 = get_bir_simp_jgmt_wlist simp_ct2
	val black_ending_label_set1 = get_bir_simp_jgmt_blist simp_ct1
	val black_ending_label_set2 = get_bir_simp_jgmt_blist simp_ct2
	val start_label = get_bir_simp_jgmt_start_label simp_ct1
	val pre1 = get_bir_simp_jgmt_pre simp_ct1
	val post1 = get_bir_simp_jgmt_post simp_ct1
	val post2 = get_bir_simp_jgmt_post simp_ct2

        (* TODO: HO_MATCH_MP is not general enough to immediately knock out the bir_simp_jgmt
         * antecedent before specialisation *)
	val bir_add_comp_seq_rule_thm =
	  ISPECL [prog, white_ending_label_set1, white_ending_label_set2,
		  black_ending_label_set1, black_ending_label_set2,
		  invariant, start_label, pre1, post1, post2]
	    bir_wm_instTheory.bir_simp_std_seq_rule_thm

	(* 2. Knock out antecedents: *)
	(* Whitelist of contract 2 should be subset of blacklist of contract 1 *)
	val bir_add_comp_seq_rule_thm1 =
	  SIMP_RULE std_ss [prove (pred_setSyntax.mk_subset
                                     (white_ending_label_set2,
                                      black_ending_label_set1),

				       SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
                                         [pred_setTheory.SUBSET_DEF]
                            )] bir_add_comp_seq_rule_thm

	(* The intersection between whitelist of contract 1 and whitelist of contract 2 should be empty *)
        (* TODO: Does this work for larger than singleton sets? *)
	val spec_noteq_trans_impl1 =
	  ISPECL [el 1 (get_labels_from_set_repr white_ending_label_set1),
		  el 1 (get_labels_from_set_repr white_ending_label_set2)]
            bir_auxiliaryTheory.noteq_trans_impl
        val white_inter_lbls = (get_labels_from_set_repr white_ending_label_set1)@
                               (get_labels_from_set_repr white_ending_label_set2)
        val cases_on_x_lbls_tac = List.foldr (fn (lbl, st) => Cases_on `x = ^lbl` >> st) ALL_TAC white_inter_lbls
	val bir_add_comp_seq_rule_thm2 =
	  SIMP_RULE std_ss [UNDISCH_ALL (prove (mk_imp (assmpt,
                                    mk_eq
                                     (pred_setSyntax.mk_inter
                                        (white_ending_label_set1,
                                         white_ending_label_set2),
                                     pred_setSyntax.mk_empty bir_label_t_ty)),
                            (* TODO: srw_ss()... *)
                            STRIP_TAC >>
                            SIMP_TAC (srw_ss()) [ASSUME assmpt, pred_setTheory.INTER_DEF, pred_setTheory.IN_ABS,
                                                 spec_noteq_trans_impl1] >>
                            FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT] >>
                            REPEAT STRIP_TAC >>
                            cases_on_x_lbls_tac >> (
                                FULL_SIMP_TAC (std_ss++HolBACoreSimps.bir_TYPES_ss++wordsLib.WORD_ss) []
                              )
                            ))] bir_add_comp_seq_rule_thm1

	(* Knock out the bir_simp_jgmt-antecedent *)
	val bir_add_comp_seq_rule_thm3 =
	  HO_MATCH_MP bir_add_comp_seq_rule_thm2 simp_ct1

	(* Starting label of contract 2 is the single label in whitelist of contract 1
	 * Note: The theorem used for composition actually allows for multiple connection points *)
	val bir_add_comp_seq_rule_thm4 =
          simp_in_sing_set_repr_rule bir_add_comp_seq_rule_thm3
	(* Knock out the final antecedent with bir_simp_loop_jgmt *)
	val bir_add_comp_seq_rule_thm5 =
          HO_MATCH_MP (SIMP_RULE std_ss def_list bir_add_comp_seq_rule_thm4)
            (SIMP_RULE std_ss def_list simp_ct2)
        (* Clean-up the expanded definitions *)
	val bir_add_comp_seq_rule_thm6 =
          simp_inter_set_repr_rule (SIMP_RULE std_ss (map GSYM def_list) bir_add_comp_seq_rule_thm5)
        val bir_add_comp_seq_rule_thm7 =
          SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.bir_TYPES_ss) [ASSUME assmpt] bir_add_comp_seq_rule_thm6

      in
	bir_add_comp_seq_rule_thm7
      end
    ;

    fun bir_compose_seq (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                         simp_inter_set_repr_rule)
          simp_ct1 simp_ct2 def_list
       =
        ((REWRITE_RULE []) o DISCH_ALL) (
          bir_compose_seq_assmpt (get_labels_from_set_repr, simp_in_sing_set_repr_rule,
                                  simp_inter_set_repr_rule)
            simp_ct1 simp_ct2 def_list T
        )
       ;

    local
      fun try_disch_all_assmpt_w_EVAL ct =
	let
	  val ct_d      = DISCH_ALL ct;
	  val assmpt_tm = (fst o dest_imp o concl) ct_d;
	  val ct_as     = EVAL assmpt_tm;
	  val ct2       = REWRITE_RULE [ct_as] (DISCH assmpt_tm ct)
	in
	  try_disch_all_assmpt_w_EVAL ct2
	end
	handle HOL_ERR _ => ct;
    in
    fun inst_vars ct []     = try_disch_all_assmpt_w_EVAL ct
      | inst_vars ct ((h1, h2)::t) =
	let
	  val ct1 = INST [h1 |-> h2] ct
	in
	  inst_vars ct1 t
	end
    end;

    (**********************************************************************************)
    (* These are the various functions and rules to facilitate treatment of pred_sets *)
    (* TODO: Where to place the below? *)
    fun el_in_set elem set =
      EQT_ELIM (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) [] (pred_setSyntax.mk_in (elem, set)));

    fun not_empty_set set =
      EQT_ELIM (SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) []
        (mk_neg (mk_eq (set, pred_setSyntax.mk_empty bir_label_t_ty))))
    ;

    fun delete_not_empty_set elem set =
      let
        val delete_tm = pred_setSyntax.mk_delete (set, elem)

        val delete_thm =
          SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
	    [pred_setTheory.DELETE_DEF]
            delete_tm

        val notempty_thm =
          not_empty_set ((snd o dest_eq o concl) delete_thm)

      in
        EQT_ELIM (SIMP_CONV std_ss [delete_thm, notempty_thm] 
          (mk_neg (mk_eq (delete_tm, pred_setSyntax.mk_empty bir_label_t_ty)))
        )
      end
    ;

    val mk_set = pred_setSyntax.mk_set;

    val simp_delete_set_rule =
      SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
	[pred_setTheory.DELETE_DEF]

    val simp_insert_set_rule =
      SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss)
	[(* ??? *)]

    val simp_in_sing_set_rule =
      SIMP_RULE std_ss [pred_setTheory.IN_SING]

    fun simp_inter_set_rule ct =
      ONCE_REWRITE_RULE [EVAL (get_bir_simp_jgmt_blist ct)] ct

    val simp_in_set_tac =
      SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++wordsLib.WORD_ss++pred_setLib.PRED_SET_ss) []

    (*
    (* For debugging: *)
    val (not_empty_set_repr, delete_not_empty_set_repr, get_labels_from_set_repr, el_in_set_repr,
	 mk_set_repr, simp_delete_set_repr_rule,
	 simp_insert_set_repr_rule, simp_in_sing_set_repr_rule, simp_inter_set_repr_rule, simp_in_set_repr_tac, inter_set_repr_ss, union_set_repr_ss) =
           (not_empty_set, delete_not_empty_set, ending_set_to_sml_list, el_in_set, mk_set, simp_delete_set_rule,
	    simp_insert_set_rule, simp_in_sing_set_rule, simp_inter_set_rule, simp_in_set_tac, bir_inter_var_set_ss, bir_union_var_set_ss);
    *)

   (* These are instantiations of composition rules for pred_sets *)
   val label_ct_to_simp_ct_predset =
     label_ct_to_simp_ct (not_empty_set, ending_set_to_sml_list, el_in_set, delete_not_empty_set, mk_set,
			 simp_delete_set_rule, simp_insert_set_rule);

   val label_ct_to_simp_ct_assmpt_predset =
     label_ct_to_simp_ct_assmpt (not_empty_set, ending_set_to_sml_list, el_in_set, delete_not_empty_set, mk_set,
			        simp_delete_set_rule, simp_insert_set_rule);

   val label_ct_to_simp_ct_no_taut_assmpt_predset =
     label_ct_to_simp_ct_no_taut_assmpt (not_empty_set, ending_set_to_sml_list, el_in_set, delete_not_empty_set,
                                        mk_set, simp_delete_set_rule, simp_insert_set_rule);

   val bir_compose_seq_predset =
     bir_compose_seq (ending_set_to_sml_list,
		      simp_in_sing_set_rule,
		      simp_inter_set_rule);

   val bir_compose_seq_assmpt_predset =
     bir_compose_seq_assmpt (ending_set_to_sml_list, simp_in_sing_set_rule,
                             simp_inter_set_rule);

   val bir_remove_labels_from_wlist_predset = bir_remove_labels_from_wlist (not_empty_set);

   val bir_remove_labels_from_blist_predset = bir_remove_labels_from_blist (simp_in_set_tac);

   val bir_compose_simp_loop_predset =
     bir_compose_simp_loop (simp_in_set_tac, bir_inter_var_set_ss, bir_union_var_set_ss);

   val bir_compose_simp_loop_unsigned_predset =
     bir_compose_simp_loop_unsigned (simp_in_set_tac, bir_inter_var_set_ss, bir_union_var_set_ss);

   val bir_populate_blacklist_predset =
     bir_populate_blacklist (ending_set_to_sml_list, el_in_set,
                                   delete_not_empty_set, mk_set,
                                   simp_delete_set_rule, simp_insert_set_rule);

  end
end
