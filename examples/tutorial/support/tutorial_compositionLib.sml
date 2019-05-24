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

     val string_ss = rewrites (type_rws ``:string``);
     val char_ss = rewrites (type_rws ``:char``);

     val vars_ss = std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss;

     fun use_impl_rule contract_thm pre_impl_wp =
     let
       val contract_thm = SIMP_RULE (std_ss) [bir_bool_expTheory.bir_exp_and_def] contract_thm;
       val pre = ((el 2) o snd o strip_comb o (el 2) o snd o strip_comb o hd o snd o strip_comb o concl) pre_impl_wp;
       val prog = ((el 1) o snd o strip_comb o concl) contract_thm;
       val entry = ((el 2) o snd o strip_comb o concl) contract_thm;
       val exit = ((el 3) o snd o strip_comb o concl) contract_thm;
       val post = ((el 5) o snd o strip_comb o concl) contract_thm;
       val wp = ((el 4) o snd o strip_comb o concl) contract_thm;
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
       val new_contract_thm = ((SIMP_RULE (std_ss) [contract_thm, taut_thm, wp_var_thm, pre_var_thm]) 
         ((ISPECL [wp, pre, prog, entry, exit, post])
             bir_triple_weak_rule_thm)
             );
       in   new_contract_thm end;

   end
end
