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

(*
val t = instd_thm;
*)

  (* TODO: need to handle typecheck, IS_SOME typecheck *)
  fun birs_simp_try_justify_assumptions t =
    if (not o is_imp o concl) t then
      t
    else
      (* TODO: raise exception when we couldn't resolve the assumption *)
      birs_simp_justify_assumptions
        (REWRITE_RULE [] (CONV_RULE (TRY_CONV (RATOR_CONV (RAND_CONV EVAL)) THENC REFL) t));


(*
val simp_t = birs_simplification_Plus_Plus_Const_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  (* for the plain cases (not subexpression, not pcond implication) *)
  fun birs_simp_try_inst simp_t simp_inst_tm =
      let
        val simp_t_ = SPEC_ALL simp_t;
        val simp_tm = ((fn tm => (if is_imp tm then (snd o strip_imp) else (I)) tm) o concl) simp_t_;

        (* see if the simplification instance fits the simplification theorem conclusion (i.e. simplification term part) *)
        val tm_subst_o =
          SOME (match_term ((fst o dest_comb) simp_tm) ((fst o dest_comb) simp_inst_tm))
          handle _ => NONE;
      in
        case tm_subst_o of
           NONE => NONE
         | SOME tm_subst => 
            (*
            val SOME tm_subst = tm_subst_o;
            *)
            let
              val instd_thm = INST_TY_TERM tm_subst simp_t_;

              (* now try to check the assumptions *)
              val final_thm_o =
                SOME (birs_simp_try_justify_assumptions instd_thm)
                handle _ => NONE;
            in
              case final_thm_o of
                 NONE => NONE
               | SOME final_thm => 
                    SOME (CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL) final_thm)
            end
      end;

  val birs_simp_exp_plain_t_l =
    [birs_simplification_UnsignedCast_LowCast_Twice_thm,

     birs_simplification_Plus_Plus_Const_thm,
     birs_simplification_Minus_Plus_Const_thm,
     birs_simplification_Minus_Minus_Const_thm,
     birs_simplification_Plus_Minus_Const_thm];

  (* TODO: use foldfun from above to try simplifying with the theorems of the list in order and return NONE or SOME simplification theorem *)



(* TODO: function/code to remove imp assumption, with smt solver *)

birs_simplification_IMP_thm
birs_exp_imp_def


  val birs_simp_exp_pcond_t_l =
    [birs_simplification_And_Minus_thm,

     birs_simplification_IfThenElse_T_thm,
     birs_simplification_IfThenElse_F_thm,

     birs_simplification_Mem_Match_thm,
     birs_simplification_Mem_Bypass_32_8_thm,
     birs_simplification_Mem_Bypass_32_32_thm,
     birs_simplification_Mem_Bypass_8_8_thm,
     birs_simplification_Mem_Bypass_8_32_thm];


  (* TODO: combination function of the two kinds above (direct simplification) *)
  (* - try plain simplification *)
  (* - try implied simplification *)



  (* TODO: "recursion" into certain subexpressions *)
  val birs_simp_subexp_t_l =
    [birs_simplification_UnsignedCast_thm,
     birs_simplification_Minus_thm];
  (* TODO: need to keep simplifying using the three functions above repeatedly until not possible to simplify anymore *)
  (* - try direct simplification *)
  (* - try direct simplification in subexpressions *)
  (* - repeat the above until can't find anything to simplify *)


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
