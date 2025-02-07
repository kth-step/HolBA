structure bir_exp_typecheckLib =
struct

local

  open HolKernel Parse boolLib bossLib;
  open computeLib;

  open holba_convLib;

  open bir_exp_substitutionsTheory;
  open bir_expTheory;

  open bir_typing_expSyntax;

  (* error handling *)
  val libname = "bir_exp_typecheckLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* TODO: we really have to put this in a central place..., stolen from: bir_exp_to_wordsLib.type_of_bir_exp_CONV (and maybe modified) *)
  local
    open bir_immTheory
    open bir_valuesTheory
    open bir_envTheory
    open bir_exp_memTheory
    open bir_bool_expTheory
    open bir_extra_expsTheory
    open bir_nzcv_expTheory
    open bir_interval_expTheory;
    open bir_typing_expTheory;
    val type_of_bir_exp_thms = [
      type_of_bir_exp_def,
      bir_var_type_def,
      bir_type_checker_REWRS (*bir_type_is_Imm_def*),
      type_of_bir_imm_def,
      BExp_Aligned_type_of,
      BExp_unchanged_mem_interval_distinct_type_of,
      bir_number_of_mem_splits_REWRS,
      BType_Bool_def,
      bir_exp_true_def,
      bir_exp_false_def,
      BExp_MSB_type_of,
      BExp_nzcv_ADD_DEFS,
      BExp_nzcv_SUB_DEFS,
      n2bs_def,
      BExp_word_bit_def,
      BExp_Align_type_of,
      BExp_ror_type_of,
      BExp_LSB_type_of,
      BExp_word_bit_exp_type_of,
      BExp_ADD_WITH_CARRY_type_of,
      BExp_word_reverse_type_of,
      BExp_ror_exp_type_of,
      bir_immtype_of_size_def,
      type_of_bir_exp_BExp_IntervalPred_thm
    ];
    val distinct_thms = [
      bir_immTheory.bir_immtype_t_distinct,
      GSYM bir_immTheory.bir_immtype_t_distinct,
      bir_valuesTheory.bir_type_t_11,
      bir_valuesTheory.bir_type_t_distinct,
      GSYM bir_valuesTheory.bir_type_t_distinct,
      bir_exp_memTheory.bir_endian_t_distinct,
      GSYM bir_exp_memTheory.bir_endian_t_distinct,
      optionTheory.SOME_11,
      optionTheory.NOT_SOME_NONE,
      GSYM optionTheory.NOT_SOME_NONE];
    val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms;

    open optionSyntax;
    open bir_valuesSyntax;
    fun is_type_of_bir_exp_val result =
      is_none result orelse
        (is_some result andalso
         ((fn x => is_BType_Imm x orelse is_BType_Mem x) o dest_some) result);

    val type_of_bir_exp_finish_CONV =
      REPEATC (
        CHANGED_CONV (
          REWRITE_CONV (distinct_thms@[bir_valuesTheory.bir_type_t_case_def,pairTheory.pair_case_def, boolTheory.COND_CLAUSES, optionTheory.option_case_def]@type_of_bir_exp_thms) THENC
          TRY_CONV LIST_BETA_CONV
      ));

    fun type_of_bir_exp_rec_CONV f_rec tm =
      let
        val thm_opened =
          (REWRITE_CONV [type_of_bir_exp_BExp_IntervalPred_thm] THENC
           REWRITE_CONV [Once bir_typing_expTheory.type_of_bir_exp_def]) tm;
        val thm = CONV_RULE (RHS_CONV (GEN_match_conv is_type_of_bir_exp f_rec THENC type_of_bir_exp_finish_CONV)) thm_opened;
      in
        thm
      end;
  in
    (* manual test
    val term = ``
      BExp_BinExp BIExp_Plus
        (BExp_Const (Imm32 20w))
        (BExp_Const (Imm32 22w))
    ``;
    val thm = type_of_bir_exp_gen_CONV ``type_of_bir_exp ^term``;
    *)
    fun type_of_bir_exp_gen_CONV term =
      let
        (* check input and output: is_type_of_bir_exp, NONE/SOME(type), already have functions for this below *)
        val _ = if is_type_of_bir_exp term then () else
                  raise ERR "type_of_bir_exp_gen_CONV" "cannot handle term";
        val res =
          conv term;
        val _ = if (is_type_of_bir_exp_val o rhs o concl) res then () else
          raise (print "\nunfinished:\n"; print_thm res; print "\n\n"; ERR "type_of_bir_exp_gen_CONV" "didn't reach the value");
      in
        res
      end;

    (* manual test
    val bexp_term = ``type_of_bir_exp (BExp_BinPred BIExp_LessOrEqual
              (BExp_Den (BVar "countw" (BType_Imm Bit64)))
              (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))``;
    val term = bexp_term;
    type_of_bir_exp_DIRECT_CONV bexp_term
    *)
    val type_of_bir_exp_DIRECT_CONV = holba_cacheLib.wrap_cache_CONV_inter_result ("type_of_bir_exp_DIRECT_CONV") (dest_type_of_bir_exp) (is_type_of_bir_exp_val) type_of_bir_exp_rec_CONV;
  end;
  val type_of_bir_exp_DIRECT_CONV = Profile.profile "type_of_bir_exp_DIRECT_CONV" type_of_bir_exp_DIRECT_CONV;

  val type_of_bir_exp_CONV =
    GEN_match_conv (is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV);
    
  fun get_type_of_bexp tm =
    let
      open optionSyntax;
      val thm = type_of_bir_exp_DIRECT_CONV (mk_type_of_bir_exp tm);
    in
      (dest_some o snd o dest_eq o concl) thm
    end
    handle _ => raise ERR "get_type_of_bexp" "not well-typed expression or other issue";

(*
val tm = ``type_of_bir_exp
    (BExp_BinExp BIExp_And
       (BExp_IntervalPred (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
          (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 31w)),
           BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 34w))))
       (BExp_BinExp BIExp_And
          (BExp_UnaryExp BIExp_Not
             (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1))))
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_Equal
                (BExp_BinExp BIExp_And
                   (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                   (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w)))
             (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_LessOrEqual
                   (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 0xFFFFFA8w)))
                (BExp_BinExp BIExp_And
                   (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                   (BExp_BinExp BIExp_And
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)))
                         (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1))))
                      (BExp_BinExp BIExp_And
                         (BExp_UnaryExp BIExp_Not
                            (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1))))
                         (BExp_BinExp BIExp_And
                            (BExp_BinPred BIExp_Equal
                               (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 0w)))
                            (BExp_BinExp BIExp_And
                               (BExp_UnaryExp BIExp_Not
                                  (BExp_BinPred BIExp_Equal
                                     (BExp_Den
                                        (BVar "sy_R3" (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 0w))))
                               (BExp_BinExp BIExp_And
                                  (BExp_UnaryExp BIExp_Not
                                     (BExp_BinPred BIExp_Equal
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "sy_R7" (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 1w)))
                                        (BExp_Const (Imm32 0w))))
                                  (BExp_UnaryExp BIExp_Not
                                     (BExp_BinPred BIExp_Equal
                                        (BExp_Den
                                           (BVar "sy_R4" (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 255w))))))))))))))``;
val tm = ``type_of_bir_exp
       (BExp_BinExp BIExp_And
          (BExp_UnaryExp BIExp_Not
             (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1))))
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_Equal
                (BExp_BinExp BIExp_And
                   (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                   (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w)))
             (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_LessOrEqual
                   (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 0xFFFFFA8w)))
                (BExp_BinExp BIExp_And
                   (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                   (BExp_BinExp BIExp_And
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)))
                         (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1))))
                      (BExp_BinExp BIExp_And
                         (BExp_UnaryExp BIExp_Not
                            (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1))))
                         (BExp_BinExp BIExp_And
                            (BExp_BinPred BIExp_Equal
                               (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 0w)))
                            (BExp_BinExp BIExp_And
                               (BExp_UnaryExp BIExp_Not
                                  (BExp_BinPred BIExp_Equal
                                     (BExp_Den
                                        (BVar "sy_R3" (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 0w))))
                               (BExp_BinExp BIExp_And
                                  (BExp_UnaryExp BIExp_Not
                                     (BExp_BinPred BIExp_Equal
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "sy_R7" (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 1w)))
                                        (BExp_Const (Imm32 0w))))
                                  (BExp_UnaryExp BIExp_Not
                                     (BExp_BinPred BIExp_Equal
                                        (BExp_Den
                                           (BVar "sy_R4" (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 255w)))))))))))))``;
val _ = print_thm (type_of_bir_exp_DIRECT_CONV tm);
val _ = print_thm (type_of_bir_exp_gen_CONV tm);
val _ = raise Fail "";
*)


end (* local *)

end (* struct *)
