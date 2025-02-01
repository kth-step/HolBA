structure bir_convLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open holba_convLib;
  open holba_cacheLib;

  open HolBACoreSimps;

  open bir_typing_expSyntax;

  (* error handling *)
  val libname = "bir_convLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname


in (* local *)

(* ---------------------------------------------------------------------------------- *)
(*  label set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  
  val bir_imm_EQ_CONV =
    let
      (* this assumes 32 or 63 bit addresses only, also doesn't take care of the case where Imms don't match (mixed Imms in Addresses) *)
      (*(fn tm => (print "\n"; print_term tm; print "\n"; REFL tm)) THENC*)
      val Imm32_EQ_CONV =
        REWR_CONV ((GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) bir_immTheory.bir_imm_t_11) THENC
        word_EQ_CONV;
      val Imm64_EQ_CONV =
        REWR_CONV ((GEN_ALL o (fn x => List.nth(x,4)) o CONJUNCTS o SPEC_ALL) bir_immTheory.bir_imm_t_11) THENC
        word_EQ_CONV;
      val distinct_thms = [bir_immTheory.bir_imm_t_distinct, GSYM bir_immTheory.bir_imm_t_distinct];
    in
      IFC
        (fn tm =>
          if (bir_immSyntax.is_Imm32 o lhs) tm then
            Imm32_EQ_CONV tm
          else
            Imm64_EQ_CONV tm)
        (ALL_CONV)
        (REWRITE_CONV distinct_thms THENC EVAL)
    end;

  val bir_label_EQ_CONV =
    let
      fun BL_Address_HC_CONV tm =
        if bir_program_labelsSyntax.is_BL_Address_HC tm then
          REWR_CONV bir_program_labelsTheory.BL_Address_HC_def tm
        else
          raise UNCHANGED;
      val BL_Label_EQ_CONV =
        REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) bir_programTheory.bir_label_t_11) THENC
        stringLib.string_EQ_CONV;
      val BL_Address_EQ_CONV =
        REWR_CONV ((GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) bir_programTheory.bir_label_t_11) THENC
        bir_imm_EQ_CONV;
      val distinct_thms = [bir_programTheory.bir_label_t_distinct, GSYM bir_programTheory.bir_label_t_distinct];
    in
      (LHS_CONV BL_Address_HC_CONV) THENC
      (RHS_CONV BL_Address_HC_CONV) THENC
      IFC
        (fn tm =>
          if (bir_programSyntax.is_BL_Address o lhs) tm then
            BL_Address_EQ_CONV tm
          else
            BL_Label_EQ_CONV tm)
        (ALL_CONV)
        (REWRITE_CONV distinct_thms)
    end;
  (*val bir_label_EQ_CONV = wrap_cache_result_EQ_BEQ Term.compare bir_label_EQ_CONV;*)

  val bir_pc_EQ_CONV =
    (REWR_CONV bir_programTheory.bir_programcounter_t_literal_11) THENC
    (CONJR_CONV
      bir_label_EQ_CONV
      num_EQ_CONV);
  (*val bir_pc_EQ_CONV = wrap_cache_result_EQ_BEQ Term.compare bir_pc_EQ_CONV;*)
  val bir_pc_EQ_CONV = Profile.profile "auxset_bir_pc_EQ_CONV" bir_pc_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(*  bir var set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  val bir_varname_EQ_CONV =
    stringLib.string_EQ_CONV;
  val bir_varname_EQ_CONV = wrap_cache_result_EQ_BEQ_string stringLib.fromHOLstring bir_varname_EQ_CONV;
  val bir_varname_EQ_CONV = Profile.profile "auxset_bir_varname_EQ_CONV" bir_varname_EQ_CONV;

  val bir_var_EQ_thm = prove(``
    !a0 a1 a0' a1'.
      BVar a0 a1 = BVar a0' a1' <=>
      a1 = a1' /\ a0 = a0'
  ``,
    METIS_TAC [bir_envTheory.bir_var_t_11]
  );

  val bir_immtype_EQ_CONV =
    REWRITE_CONV [bir_immTheory.bir_immtype_t_distinct, GSYM bir_immTheory.bir_immtype_t_distinct];

  val bir_type_EQ_LImm_thm = CONJUNCT1 bir_valuesTheory.bir_type_t_11;
  val bir_type_EQ_LMem_thm = CONJUNCT2 bir_valuesTheory.bir_type_t_11;
  val bir_type_EQ_CONV =
    REWRITE_CONV [bir_valuesTheory.bir_type_t_distinct,  GSYM bir_valuesTheory.bir_type_t_distinct] THENC
    (fn tm =>
      (if identical T tm orelse identical F tm then ALL_CONV else
       if (bir_valuesSyntax.is_BType_Imm o fst o dest_eq) tm then
         REWR_CONV bir_type_EQ_LImm_thm THENC
         bir_immtype_EQ_CONV
       else
         REWR_CONV bir_type_EQ_LMem_thm THENC
         CONJL_CONV bir_immtype_EQ_CONV bir_immtype_EQ_CONV
      ) tm);
  (* this seems to be well optimized now, maybe need to turn off caching if there are much more variables around so that the dictionary lookups are more expensive *)
  val bir_var_EQ_CONV =
    (REWR_CONV bir_var_EQ_thm) THENC
    (CONJL_CONV
      bir_type_EQ_CONV (*type*)
      bir_varname_EQ_CONV (*name*));
  val bir_var_EQ_CONV = wrap_cache_result_EQ_BEQ Term.compare bir_var_EQ_CONV;
  val bir_var_EQ_CONV = Profile.profile "auxset_bir_var_EQ_CONV" bir_var_EQ_CONV;
  val bir_status_EQ_CONV =
    (* this seems to be well optimized now *)
    EVAL;


  val bir_status_EQ_CONV = Profile.profile "auxset_bir_status_EQ_CONV" bir_status_EQ_CONV;

  (* could speed this up, maybe take inspiration from string or word EQ_CONV functions *)
  val bir_exp_EQ_CONV =
    let
      val rewrite_thms = (((List.concat o List.map (fn t => [t,GSYM t]) o CONJUNCTS) bir_expTheory.bir_exp_t_distinct)@(CONJUNCTS bir_expTheory.bir_exp_t_11))@[bir_extra_expsTheory.BExp_IntervalPred_def];
    in
      REWRITE_CONV rewrite_thms THENC
      EVAL (*SIMP_CONV (std_ss++holBACore_ss++birs_state_ss) [] THENC EVAL*)
    end;
  val bir_exp_EQ_CONV = wrap_cache_result_EQ_BEQ Term.compare bir_exp_EQ_CONV;
  val bir_exp_EQ_CONV = Profile.profile "auxset_bir_exp_EQ_CONV" bir_exp_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(* faster set operations for bir variable sets (for example for: computing freevarset, symbexec composition, merging, etc) *)
(* ---------------------------------------------------------------------------------- *)
  (* for UNION and BIGUNION it should be possible to use ID_EQ_CONV,
     but current implementation of the library functions does not fully support this use.
     the problem likely starts from IN_CONV,
     which does not prove syntactical elements further into the set, only first element works *)
  val varset_UNION_CONV =
    pred_setLib.UNION_CONV bir_var_EQ_CONV;

  val varset_BIGUNION_CONV =
    BIGUNION_CONV bir_var_EQ_CONV;

  val varset_INTER_CONV =
    INTER_CONV bir_var_EQ_CONV;

  val varset_DIFF_CONV =
    DIFF_CONV bir_var_EQ_CONV;

  (* A INTER (B DIFF C) *)
  val varset_INTER_DIFF_CONV =
    (* first DIFF *) 
    (RAND_CONV varset_DIFF_CONV) THENC
    (* then INTER *)
    varset_INTER_CONV;


(* ---------------------------------------------------------------------------------- *)
(*  variables of bir expressions                                                      *)
(* ---------------------------------------------------------------------------------- *)

  fun bir_exp_normalizer_1_CONV tm = (
      if bir_extra_expsSyntax.is_BExp_Aligned tm then
        REWR_CONV bir_extra_expsTheory.BExp_Aligned_def
      else if bir_interval_expSyntax.is_BExp_unchanged_mem_interval_distinct tm then
        REWR_CONV bir_interval_expTheory.BExp_unchanged_mem_interval_distinct_def
      else
        ALL_CONV
    ) tm;

  
  exception bir_vars_of_exp_exception of string * term;
  (* here apply only one "unfolding" and get empty or singleton sets, or one or two UNION operations, left-associative *)
  local
    val bir_vars_of_exp_rec_rewr_thm = (LIST_CONJ) ((CONJUNCTS bir_typing_expTheory.bir_vars_of_exp_def)@[bir_extra_expsTheory.bir_vars_of_exp_BExp_IntervalPred_thm]);
    fun bir_vars_of_exp_rec_CONV f_rec tm =
      let
        open pred_setSyntax;
        val t1 =
          (RAND_CONV bir_exp_normalizer_1_CONV THENC
           REWRITE_CONV [Once bir_vars_of_exp_rec_rewr_thm]) tm;
        val t2 = CONV_RULE (RAND_CONV (
        GEN_match_conv is_bir_vars_of_exp (f_rec))) t1;
        fun union_conv tm_ =
          varset_UNION_CONV tm_
          handle _ => raise bir_vars_of_exp_exception ("could not apply UNION", tm);
        val t2_rhs = (rhs o concl) t2;
        val t3 =
          if is_union (t2_rhs) then
            if is_union ((fst o dest_union) t2_rhs) then
              CONV_RULE (RAND_CONV (LAND_CONV union_conv THENC union_conv)) t2
            else
              CONV_RULE (RAND_CONV union_conv) t2
          else
            t2;
      in
        t3
      end;
  in
    val bir_vars_of_exp_wrapped_CONV = wrap_cache_CONV_inter_result ("bir_vars_of_exp_wrapped_CONV") (dest_bir_vars_of_exp) (can pred_setSyntax.strip_set) bir_vars_of_exp_rec_CONV;
  end;

  fun bir_vars_of_exp_DIRECT_CONV tm =
    let
     val _ = if is_bir_vars_of_exp tm then () else
               raise ERR "bir_vars_of_exp_DIRECT_CONV" "cannot handle term";
    in
      (*(SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL)*)
      bir_vars_of_exp_wrapped_CONV tm
      handle e => (print_term tm; print "\n\n"; raise e)
    end;
  (*val bir_vars_of_exp_DIRECT_CONV = wrap_cache_result Term.compare bir_vars_of_exp_DIRECT_CONV;*)
  val bir_vars_of_exp_DIRECT_CONV =
    Profile.profile "bir_vars_of_exp_DIRECT_CONV" bir_vars_of_exp_DIRECT_CONV;

  val bir_vars_of_exp_CONV =
    GEN_match_conv (is_bir_vars_of_exp) bir_vars_of_exp_DIRECT_CONV;

  fun get_vars_of_bexp tm =
    let
      open pred_setSyntax;
      val thm = bir_vars_of_exp_DIRECT_CONV (mk_bir_vars_of_exp tm);
    in
      (strip_set o snd o dest_eq o concl) thm
    end
    handle _ => (print_term tm; print "\n\n"; raise ERR "get_vars_of_bexp" "did not work");



(* ---------------------------------------------------------------------------------- *)
(*  BIR programs                                                      *)
(* ---------------------------------------------------------------------------------- *)

(* NOTE: this can be done much better, but already much better than before *)
  val bir_vars_of_program_DIRECT_CONV =
    REWRITE_CONV [bir_typing_progTheory.bir_vars_of_program_ALT_thm] THENC
    EVAL;

  val bir_vars_of_program_CONV =
    GEN_match_conv (bir_typing_progSyntax.is_bir_vars_of_program) bir_vars_of_program_DIRECT_CONV;


  val bir_labels_of_program_DIRECT_CONV =
    (*RESTR_EVAL_CONV [bir_programSyntax.bir_labels_of_program_tm] THENC*)
    REWR_CONV bir_programTheory.bir_labels_of_program_def THENC
    listLib.MAP_CONV (SIMP_CONV (std_ss++HolBACoreSimps.bir_TYPES_ss) []);

  val bir_labels_of_program_CONV =
    GEN_match_conv (bir_programSyntax.is_bir_labels_of_program) bir_labels_of_program_DIRECT_CONV;


end (* local *)

end (* struct *)
