structure birs_simpLib =
struct

local

open HolKernel Parse boolLib bossLib;

open bir_symb_simpTheory;

open bir_exp_typecheckLib;
open bir_smtLib;

open birs_auxLib;

  (* error handling *)
  val libname = "bir_simpLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(*

(*symb_rulesTheory.symb_simplification_def*)
fun birs_trysimp 

    fun try_inst t simp_thm =
      let
        val t_ = SPEC_ALL t;
        val bir_simp_tm = (fst o dest_comb o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl) t_;
        val bir_simp_inst_tm = (fst o dest_comb o fst o dest_imp o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl o Q.SPEC `symbexp'`) simp_thm;

        val tm_subst = match_term bir_simp_tm bir_simp_inst_tm;
        val final_thm = INST_TY_TERM tm_subst t_;
      in
        CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL) final_thm
      end;

    fun try_fold_match simp_thm (t, thm_o) =
      if isSome thm_o then
        thm_o
      else
        SOME (MATCH_MP simp_thm (try_inst t simp_thm))
        handle _ => NONE;

    fun repeat_fold step_thm =
      let
        val assignment_thm = MATCH_MP birs_rule_SUBST_thm step_thm;
        val thm_o = List.foldr (try_fold_match assignment_thm) NONE const_add_subst_thms;
      in
        if isSome thm_o then
          repeat_fold (valOf thm_o)
        else
          step_thm
      end;

*)

  fun birs_simp_gen_term pcond bexp = ``
    birs_simplification ^pcond ^bexp symbexp'
  ``;



(*
val t = ASSUME ``
  IS_SOME
       (type_of_bir_exp
          (BExp_IfThenElse
             (BExp_BinPred BIExp_Equal
                (BExp_Cast BIExp_UnsignedCast
                   (BExp_Cast BIExp_LowCast
                      (BExp_BinExp BIExp_RightShift
                         (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 31w))) Bit8) Bit32)
                (BExp_Const (Imm32 0w)))
             (BExp_BinExp BIExp_Plus
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 19w))) (BExp_Const (Imm64 3w)))
             (BExp_BinExp BIExp_Plus
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 19w))) (BExp_Const (Imm64 1w)))))
  ==> (abcd)
``;
*)




(*
val t = instd_thm;
*)

  (* need to handle typecheck, IS_SOME typecheck *)
  fun birs_simp_try_justify_assumptions t =
    if (not o is_imp o concl) t then
      t
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
	val type_ofbirexp_CONV = GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV);
        val assmpt_thm = (type_ofbirexp_CONV THENC EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "birs_simp_try_justify_assumptions" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "birs_simp_try_justify_assumptions" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        birs_simp_try_justify_assumptions
          (REWRITE_RULE [assmpt_thm] t)
      end;
  val birs_simp_try_justify_assumptions = Profile.profile "birs_simp_try_justify_assumptions" birs_simp_try_justify_assumptions;


(*
val simp_t = birs_simplification_Plus_Plus_Const_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  (* for the plain cases (not subexpression, not pcond implication) *)
  fun birs_simp_try_inst simp_inst_tm simp_t =
      let
        val simp_t_ = SPEC_ALL simp_t;
        val simp_tm = ((fn tm => (if is_imp tm then (snd o strip_imp) else (I)) tm) o concl) simp_t_;

        (* see if the simplification instance fits the simplification theorem conclusion (i.e. simplification term part) *)
        val tm_subst_o =
          SOME (match_term ((fst o dest_comb) simp_tm) ((fst o dest_comb) simp_inst_tm))
          handle _ => NONE;
      in
        (*
        val SOME tm_subst = tm_subst_o;
        *)
        Option.map (fn tm_subst => INST_TY_TERM tm_subst simp_t_) tm_subst_o
      end;

  fun birs_simp_try_fix_assumptions instd_thm =
    let
      (* now try to check the assumptions *)
      val final_thm_o =
        SOME (birs_simp_try_justify_assumptions instd_thm)
        handle _ => NONE;
    in
      Option.map (fn final_thm => CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL) final_thm) final_thm_o
    end;
  val birs_simp_try_fix_assumptions = Profile.profile "birs_simp_try_fix_assumptions" birs_simp_try_fix_assumptions;

  val birs_simp_exp_plain_thms =
    [birs_simplification_UnsignedCast_LowCast_Twice_thm,

     birs_simplification_Plus_Const64_thm,

     birs_simplification_Plus_Plus_Const64_thm,
     birs_simplification_Minus_Plus_Const64_thm,
     birs_simplification_Minus_Minus_Const64_thm,
     birs_simplification_Plus_Minus_Const64_thm(*,

     birs_simplification_Plus_Plus_Const32_thm,
     birs_simplification_Minus_Plus_Const32_thm,
     birs_simplification_Minus_Minus_Const32_thm,
     birs_simplification_Plus_Minus_Const32_thm*)];

  (* try simplifying with the theorems of the list in order and return NONE or SOME simplification theorem *)
  fun simp_try_fold_fun_gen simp_try_fun (t, thm_o) =
      if isSome thm_o then
        thm_o
      else
        (* SOME (MATCH_MP simp_thm (try_inst t simp_thm)) *)
        simp_try_fun t
        (*handle _ => NONE*);

  fun simp_try_fold_gen simp_try_fun simp_inst_tm simp_thms acc =
    List.foldr (simp_try_fold_fun_gen (simp_try_fun simp_inst_tm)) acc simp_thms;

  val birs_simp_try_plain_simp_ =
    fn x => fn y => Option.mapPartial birs_simp_try_fix_assumptions (birs_simp_try_inst x y);
  fun birs_simp_try_plain_simp x = Profile.profile "birs_simp_try_plain_simp" (birs_simp_try_plain_simp_ x);
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_plain_simp simp_inst_tm birs_simp_exp_plain_thms NONE;
*)


  fun check_imp_tm imp_tm =
    let
      (* input term: birs_exp_imp *)
      (* ================================================= *)
      (* TODO: function/code to remove imp assumption, with smt solver *)
      val pred1_tm = (snd o dest_comb o fst o dest_comb) imp_tm;
      val pred2_tm = (snd o dest_comb) imp_tm;
      val imp_bexp_tm = bslSyntax.bor (bslSyntax.bnot pred1_tm, pred2_tm);
      val imp_is_taut = bir_smt_check_taut false imp_bexp_tm;
      val imp_thm =
            if imp_is_taut then
              (* SOME (prove(imp_tm, cheat)) *)
              mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], imp_tm)
            else (
	      (*print_term imp_tm;*)
	      print "implication term is not a tautology";
              raise ERR "check_imp_tm" "implication term is not a tautology"
	    )
    in
      imp_thm
    end;



(*
val simp_t = birs_simplification_IfThenElse_T_thm;
val simp_t = birs_simplification_IfThenElse_F_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_pcond_simp_ simp_inst_tm simp_t =
    let
      val SOME birs_simp_IMP_inst_t = birs_simp_try_inst simp_inst_tm birs_simplification_IMP_thm;
      val simp_inst_tm = (fst o dest_imp o snd o dest_imp o concl) birs_simp_IMP_inst_t;

      val simp_t_ = SPEC_ALL simp_t;
      val simp_tm = ((fn tm => (if is_imp tm then (snd o strip_imp) else (I)) tm) o concl) simp_t_;

      (* see if the simplification instance fits the simplification theorem conclusion (i.e. simplification term part) *)
      val tm_subst_o =
        SOME (match_term ((snd o dest_comb o fst o dest_comb) simp_tm) ((snd o dest_comb o fst o dest_comb) simp_inst_tm))
        handle _ => NONE;

      val SOME instd_thm =   Option.map (fn tm_subst => INST_TY_TERM tm_subst simp_t_) tm_subst_o;

      val SOME basic_simp_thm = birs_simp_try_fix_assumptions instd_thm;

      val birs_simp_IMP_inst_tm = (fst o dest_imp o snd o dest_imp o concl) birs_simp_IMP_inst_t;

      val tm_subst_o =
          SOME (match_term birs_simp_IMP_inst_tm (concl basic_simp_thm))
          handle _ => NONE;

      val SOME instd_thm =   Option.map (fn tm_subst => INST_TY_TERM tm_subst birs_simp_IMP_inst_t) tm_subst_o;


      val imp_tm = (fst o dest_imp o concl) instd_thm;
      (* ================================================= *)
      val imp_thm = check_imp_tm imp_tm;

      val final_thm = MP (MP instd_thm imp_thm) basic_simp_thm;
    in
      SOME final_thm
    end
    handle _ => NONE;
  fun birs_simp_try_pcond_simp x = Profile.profile "birs_simp_try_pcond_simp" (birs_simp_try_pcond_simp_ x);


  val birs_simp_exp_pcond_thms =
    [(*birs_simplification_And_Minus_CM0_thm,*)
     birs_simplification_LSB0_And64_RV_thm,
     birs_simplification_SignedLowCast3264_RV_thm,

     birs_simplification_IfThenElse_T_thm,
     birs_simplification_IfThenElse_F_thm]@
    (CONJUNCTS birs_simplification_Mem_Match_64_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm)(*@
    (CONJUNCTS birs_simplification_Mem_Match_32_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_32_8_thm)*);


(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_pcond_simp simp_inst_tm birs_simp_exp_pcond_thms NONE;
*)


  (* combination function of the two kinds above (direct simplification) *)
  (* - try plain simplification *)
  (* - try implied simplification *)
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_direct_simp simp_inst_tm =
    let
      val plain_o = simp_try_fold_gen birs_simp_try_plain_simp simp_inst_tm birs_simp_exp_plain_thms NONE;
      val pcond_o = simp_try_fold_gen birs_simp_try_pcond_simp simp_inst_tm birs_simp_exp_pcond_thms plain_o;
    in
      pcond_o
    end;
  val birs_simp_try_direct_simp = Profile.profile "birs_simp_try_direct_simp" birs_simp_try_direct_simp;


  (* "recursion" into certain subexpressions *)
(*
val simp_t = birs_simplification_Minus_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_subexp_simp_ simp_inst_tm simp_t =
    let
      val SOME birs_simp_IMP_inst_t = birs_simp_try_inst simp_inst_tm simp_t;
      val simp_inst_tm__ = (fst o dest_imp o concl) birs_simp_IMP_inst_t;

      val SOME simp_thm = birs_simp_try_direct_simp simp_inst_tm__;
    in
      SOME (MATCH_MP birs_simp_IMP_inst_t simp_thm)
    end
    handle _ => NONE;
  fun birs_simp_try_subexp_simp x = Profile.profile "birs_simp_try_subexp_simp" (birs_simp_try_subexp_simp_ x);

  val birs_simp_exp_subexp_thms =
    [birs_simplification_UnsignedCast_thm,
     birs_simplification_SignedCast_thm,
     birs_simplification_LowCast_thm,
     birs_simplification_Minus_left_thm,
     birs_simplification_Plus_left_thm,
     birs_simplification_Plus_right_thm,
     birs_simplification_Load_addr_thm,
     birs_simplification_Store_addr_thm];

(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_subexp_simp simp_inst_tm birs_simp_exp_subexp_thms NONE;
*)


  (* TODO: need to keep simplifying using the three functions above repeatedly until not possible to simplify anymore *)
  (* - try direct simplification *)
  (* - try direct simplification in subexpressions *)
  (* - repeat the above until can't find anything to simplify *)


  fun birs_simp_ID_fun simp_inst_tm =
    let
      val simp_t_ = SPEC_ALL birs_simplification_ID_thm;
      val simp_tm_ = (concl) simp_t_;
      val tm_subst_o =
        SOME (match_term ((fst o dest_comb) simp_tm_) ((fst o dest_comb) simp_inst_tm))
        handle _ => NONE;
      val SOME instd_thm = Option.map (fn tm_subst => INST_TY_TERM tm_subst simp_t_) tm_subst_o;
    in
      instd_thm
    end
    handle _ => raise ERR "birs_simp_ID_thm" ("this shouldn't happen :: " ^ (term_to_string simp_inst_tm));

(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val start_simp_thm = birs_simp_ID_fun simp_inst_tm;
  birs_simp_repeat simp_inst_tm;
*)
  fun birs_simp_repeat_ start_simp_thm =
      let
        val pcond_tm = (snd o dest_comb o fst o dest_comb o fst o dest_comb o concl) start_simp_thm;
        val bexp_tm = (snd o dest_comb o concl) start_simp_thm;
        val simp_inst_tm__ = birs_simp_gen_term pcond_tm bexp_tm;

        val direct_o = birs_simp_try_direct_simp simp_inst_tm__;
        val subexp_o = simp_try_fold_gen birs_simp_try_subexp_simp simp_inst_tm__ birs_simp_exp_subexp_thms direct_o;
      in
        if isSome subexp_o then
          birs_simp_repeat_ (MATCH_MP (MATCH_MP birs_simplification_TRANS_thm start_simp_thm) (valOf subexp_o))
        else
          start_simp_thm
      end;
  val birs_simp_repeat_ = Profile.profile "birs_simp_repeat_" birs_simp_repeat_;

  fun birs_simp_repeat simp_inst_tm =
    birs_simp_repeat_ (birs_simp_ID_fun simp_inst_tm);

(*

val pcond = ````;
val bexp = ````;

val pcond = ``(BExp_Const (Imm1 1w))``;
val bexp = ``BExp_Cast BIExp_SignedCast
                        (BExp_Cast BIExp_LowCast
                           (BExp_Cast BIExp_SignedCast
                              (BExp_Cast BIExp_LowCast
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_Const (Imm64 3w)) Bit32)
                                       Bit64)
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_Const (Imm64 7w)) Bit32)
                                       Bit64)) Bit32) Bit64) Bit32) Bit64``;

val bexp = ``BExp_Cast BIExp_SignedCast
                        (BExp_Cast BIExp_LowCast
                           (BExp_Cast BIExp_SignedCast
                              (BExp_Cast BIExp_LowCast
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_Const (Imm64 3w)) Bit32)
                                       Bit64)
                                    (BExp_Cast BIExp_SignedCast
                                       (BExp_Cast
                                                         BIExp_LowCast
                                                         (BExp_Const
                                                            (Imm64 1w))
                                                         Bit32) Bit64))
                                 Bit32) Bit64) Bit32) Bit64``;

val pcond = ``BExp_BinExp BIExp_And
                    (BExp_BinPred BIExp_Equal
                       (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 pre_x2)))
                    (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_Equal
                          (BExp_BinExp BIExp_And
                             (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 7w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinExp BIExp_And
                          (BExp_BinPred BIExp_LessOrEqual
                             (BExp_Const (Imm64 4096w))
                             (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
                          (BExp_BinPred BIExp_LessThan
                             (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 0x100000000w)))))``;
val bexp = ``(BExp_Load
                           (BExp_Store
                              (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                              (BExp_BinExp BIExp_Minus
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_Den
                                       (BVar "sy_x2" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 32w)))
                                 (BExp_Const (Imm64 28w)))
                              BEnd_LittleEndian
                              (BExp_Cast BIExp_LowCast
                                 (BExp_Const (Imm64 7w)) Bit32))
                           (BExp_BinExp BIExp_Minus
                              (BExp_BinExp BIExp_Minus
                                 (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32)``;
val bexp = ``(BExp_Load
                           (BExp_Store
                              (BExp_Store
                                 (BExp_Store
                                    (BExp_Store
                                       (BExp_Store
                                          (BExp_Store
                                             (BExp_Den
                                                (BVar "sy_MEM8"
                                                   (BType_Mem Bit64 Bit8)))
                                             (BExp_BinExp BIExp_Plus
                                                (BExp_BinExp BIExp_Minus
                                                   (BExp_Den
                                                      (BVar "sy_x2"
                                                         (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 32w)))
                                                (BExp_Const (Imm64 24w)))
                                             BEnd_LittleEndian
                                             (BExp_Den
                                                (BVar "sy_x1"
                                                   (BType_Imm Bit64))))
                                          (BExp_BinExp BIExp_Plus
                                             (BExp_BinExp BIExp_Minus
                                                (BExp_Den
                                                   (BVar "sy_x2"
                                                      (BType_Imm Bit64)))
                                                (BExp_Const (Imm64 32w)))
                                             (BExp_Const (Imm64 16w)))
                                          BEnd_LittleEndian
                                          (BExp_Den
                                             (BVar "sy_x8"
                                                (BType_Imm Bit64))))
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_BinExp BIExp_Minus
                                             (BExp_Den
                                                (BVar "sy_x2"
                                                   (BType_Imm Bit64)))
                                             (BExp_Const (Imm64 0w)))
                                          (BExp_Const (Imm64 20w)))
                                       BEnd_LittleEndian
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_Const (Imm64 1w)) Bit32))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_Den
                                             (BVar "sy_x2"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 64w)))
                                       (BExp_Const (Imm64 24w)))
                                    BEnd_LittleEndian
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 0w))))
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 32w)))
                                    (BExp_Const (Imm64 24w)))
                                 BEnd_LittleEndian (BExp_Const (Imm64 3w)))
                              (BExp_BinExp BIExp_Minus
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_Den
                                       (BVar "sy_x2" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 32w)))
                                 (BExp_Const (Imm64 28w)))
                              BEnd_LittleEndian
                              (BExp_Cast BIExp_LowCast
                                 (BExp_Const (Imm64 7w)) Bit32))
                           (BExp_BinExp BIExp_Minus
                              (BExp_BinExp BIExp_Minus
                                 (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32)``;
val bexp = ``BExp_Cast BIExp_SignedCast
                        (BExp_Load
                           (BExp_Store
                              (BExp_Store
                                 (BExp_Store
                                    (BExp_Store
                                       (BExp_Store
                                          (BExp_Store
                                             (BExp_Den
                                                (BVar "sy_MEM8"
                                                   (BType_Mem Bit64 Bit8)))
                                             (BExp_BinExp BIExp_Plus
                                                (BExp_BinExp BIExp_Minus
                                                   (BExp_Den
                                                      (BVar "sy_x2"
                                                         (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 32w)))
                                                (BExp_Const (Imm64 24w)))
                                             BEnd_LittleEndian
                                             (BExp_Den
                                                (BVar "sy_x1"
                                                   (BType_Imm Bit64))))
                                          (BExp_BinExp BIExp_Plus
                                             (BExp_BinExp BIExp_Minus
                                                (BExp_Den
                                                   (BVar "sy_x2"
                                                      (BType_Imm Bit64)))
                                                (BExp_Const (Imm64 32w)))
                                             (BExp_Const (Imm64 16w)))
                                          BEnd_LittleEndian
                                          (BExp_Den
                                             (BVar "sy_x8"
                                                (BType_Imm Bit64))))
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_BinExp BIExp_Minus
                                             (BExp_Den
                                                (BVar "sy_x2"
                                                   (BType_Imm Bit64)))
                                             (BExp_Const (Imm64 0w)))
                                          (BExp_Const (Imm64 20w)))
                                       BEnd_LittleEndian
                                       (BExp_Cast BIExp_LowCast
                                          (BExp_Const (Imm64 1w)) Bit32))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_BinExp BIExp_Minus
                                          (BExp_Den
                                             (BVar "sy_x2"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 64w)))
                                       (BExp_Const (Imm64 24w)))
                                    BEnd_LittleEndian
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 0w))))
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_BinExp BIExp_Minus
                                       (BExp_Den
                                          (BVar "sy_x2" (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 32w)))
                                    (BExp_Const (Imm64 24w)))
                                 BEnd_LittleEndian (BExp_Const (Imm64 3w)))
                              (BExp_BinExp BIExp_Minus
                                 (BExp_BinExp BIExp_Minus
                                    (BExp_Den
                                       (BVar "sy_x2" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 32w)))
                                 (BExp_Const (Imm64 28w)))
                              BEnd_LittleEndian
                              (BExp_Cast BIExp_LowCast
                                 (BExp_Const (Imm64 7w)) Bit32))
                           (BExp_BinExp BIExp_Minus
                              (BExp_BinExp BIExp_Minus
                                 (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32) Bit64``;

val pcond = ``(BExp_BinPred BIExp_Equal
      (BExp_Cast BIExp_UnsignedCast
        (BExp_Cast BIExp_LowCast
          (BExp_BinExp BIExp_RightShift
            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
            (BExp_Const (Imm32 31w))) Bit8) Bit32)
      (BExp_Const (Imm32 0w)))``;

val pcond = ``BExp_UnaryExp BIExp_Not (^pcond)``

val bexp = ``
  (BExp_IfThenElse
    (BExp_BinPred BIExp_Equal
      (BExp_Cast BIExp_UnsignedCast
        (BExp_Cast BIExp_LowCast
          (BExp_BinExp BIExp_RightShift
            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
            (BExp_Const (Imm32 31w))) Bit8) Bit32)
      (BExp_Const (Imm32 0w)))
    (BExp_BinExp BIExp_Plus
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 19w))) (BExp_Const (Imm64 3w)))
    (BExp_BinExp BIExp_Plus
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 19w))) (BExp_Const (Imm64 1w))))``;




val pcond = ``(BExp_Const (Imm1 1w))``;
val bexp = ``
  BExp_BinExp BIExp_Plus
    (BExp_BinExp BIExp_Plus
      (BExp_Den (BVar "abcd" (BType_Imm Bit64)))
        (BExp_Const (Imm64 22w)))
    (BExp_Const (Imm64 14w))``;



val pcond = ``
  BExp_BinPred BIExp_Equal
    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
    (BExp_Const (Imm32 35w))``;

val bexp = ``
  BExp_IfThenElse
    (BExp_BinPred BIExp_LessThan
      (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
      (BExp_Const (Imm32 31w)))
    (BExp_Const (Imm64 19w))
    (BExp_Const (Imm64 77w))``;

val bexp = ``
  BExp_BinExp BIExp_Minus
    ^bexp
    (BExp_Const (Imm64 2w))``;


*)


end (* local *)

end (* struct *)
