structure birs_simpLib =
struct

local

open bir_symb_simpTheory;

val const_add_subst_thms = [
];

in (* local *)

    (*
    val t = hd const_add_subst_thms;
    *)

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
    birs_simplification_e ^pcond ^bexp symbexp'
  ``;

val t = instd_thm;

  (* TODO: need to handle imp case and recursion case, recursion needs to be handled correctly one function "above" *)
  fun birs_simp_justify_assumptions t =
    if (not o is_imp o concl) t then
      t
    else
      birs_simp_justify_assumptions
        (REWRITE_RULE [] (CONV_RULE (TRY_CONV (RATOR_CONV (RAND_CONV EVAL)) THENC REFL) t));

val simp_t = birs_simplification_Plus_Plus_Const_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;

  fun birs_simp_try_inst simp_t simp_inst_tm =
      let
        val simp_t_ = SPEC_ALL simp_t;
        val simp_tm = ((fn tm => (if is_imp tm then (snd o strip_imp) else (I)) tm) o concl) simp_t_;

        val tm_subst = match_term ((fst o dest_comb) simp_tm) ((fst o dest_comb) simp_inst_tm);
        val instd_thm = INST_TY_TERM tm_subst simp_t_;

        (* now try to check the assumptions *)
        val final_thm = birs_simp_justify_assumptions instd_thm;
      in
        CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL) final_thm
      end;


(* TODO: need to repeat simplifying until there is nothing more to simplify *)



(*

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

*)


end (* local *)

end (* struct *)
