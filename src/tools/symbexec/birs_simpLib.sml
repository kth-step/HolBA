structure birs_simpLib =
struct

local

open HolKernel Parse boolLib bossLib;

open bir_symb_simpTheory;

open bir_exp_typecheckLib;

open birs_auxLib;

  (* error handling *)
  val libname = "bir_simpLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  local
    val symbexp_prim_tm = ``symbexp':bir_exp_t``;
  in
    fun birs_simp_gen_term pcond bexp = 
      birsSyntax.mk_birs_simplification (pcond, bexp, symbexp_prim_tm);
  end

  fun birs_simp_gen_term_from_prev_simp_thm pre_simp_thm =
    let
        val (pcond_tm, _, bexp_tm) = (birsSyntax.dest_birs_simplification o concl) pre_simp_thm;
    in
      birs_simp_gen_term pcond_tm bexp_tm
    end;

  fun birs_simp_ID_fun simp_tm =
    let
      val (pcond_tm, bexp_tm, _) = birsSyntax.dest_birs_simplification simp_tm;
      val simp_thm = ISPECL [pcond_tm, bexp_tm] birs_simplification_ID_thm;
    in
      simp_thm
    end
    handle _ => raise ERR "birs_simp_ID_fun" ("this shouldn't happen :: " ^ (term_to_string simp_tm));

  fun birs_simp_check_ID_opt_fun simp_tm_fun simp_tm =
    let
      val simp_thm = simp_tm_fun simp_tm;
      val (_,exp1,exp2) = (birsSyntax.dest_birs_simplification o concl) simp_thm;
      val is_ID = identical exp1 exp2;
    in
      if is_ID then
        NONE
      else
        SOME simp_thm
    end;

  fun birs_simp_apply_trans post_fun pre_simp_thm simp_thm_o =
    if isSome simp_thm_o then
        let
          val t1 = pre_simp_thm;
          val t2 = valOf simp_thm_o;
          val (pcond_tm, bexp1_tm, bexp2_tm) = (birsSyntax.dest_birs_simplification o concl) t1;
          val (_, _, bexp3_tm) = (birsSyntax.dest_birs_simplification o concl) t2;
          val trans_spec_thm = SPECL [pcond_tm, bexp1_tm, bexp2_tm, bexp3_tm] birs_simplification_TRANS_thm;
          val t3 = MP (MP trans_spec_thm t1) t2;
        in
          post_fun t3
        end
    else
      pre_simp_thm;

(* ----------------------------------------------------------------------------------- *)

  (* try simplifying with the theorems of the list in order and return NONE or SOME simplification theorem *)
  fun simp_try_fold_gen simp_try_fun [] (_, simp_thm_o) = simp_thm_o
    | simp_try_fold_gen simp_try_fun (h_thm::h_thms) (simp_tm, simp_thm_o) =
        if isSome simp_thm_o then
          simp_thm_o
        else
          let
            val simp_thm_o1 = simp_try_fun h_thm (simp_tm, NONE);
          in
            simp_try_fold_gen simp_try_fun h_thms (simp_tm, simp_thm_o1)
          end;

  fun simp_try_list_gen [] (_, simp_thm_o) = simp_thm_o
    | simp_try_list_gen (fh::fl) (simp_tm, simp_thm_o) =
        if isSome simp_thm_o then
          simp_thm_o
        else
          let
            val simp_thm_o1 = fh (simp_tm, NONE);
          in
            simp_try_list_gen fl (simp_tm, simp_thm_o1)
          end;

  fun simp_try_make_option_fun basic_fun (simp_tm, simp_thm_o) =
    if isSome simp_thm_o then
      simp_thm_o
    else
      basic_fun simp_tm;

  fun simp_try_list_cont_gen_1 [] pre_simp_thm = pre_simp_thm
    | simp_try_list_cont_gen_1 (fh::fl) pre_simp_thm =
          let
            val simp_tm = birs_simp_gen_term_from_prev_simp_thm pre_simp_thm;
            val simp_thm_o = fh (simp_tm, NONE);
            val post_simp_thm = birs_simp_apply_trans I pre_simp_thm simp_thm_o;
          in
            simp_try_list_cont_gen_1 fl post_simp_thm
          end;
  fun simp_try_list_cont_gen_2 simp_funs simp_tm =
    simp_try_list_cont_gen_1 simp_funs (birs_simp_ID_fun simp_tm);
  fun simp_try_list_cont_gen simp_funs = simp_try_make_option_fun (birs_simp_check_ID_opt_fun (simp_try_list_cont_gen_2 simp_funs));
   
  fun simp_try_repeat_gen_1 simp_fun pre_simp_thm =
      let
        val simp_tm = birs_simp_gen_term_from_prev_simp_thm pre_simp_thm;
        val simp_thm_o = simp_fun (simp_tm, NONE);
      in
        birs_simp_apply_trans (simp_try_repeat_gen_1 simp_fun) pre_simp_thm simp_thm_o
      end;
  fun simp_try_repeat_gen_2 simp_fun simp_tm =
    simp_try_repeat_gen_1 simp_fun (birs_simp_ID_fun simp_tm);
  fun simp_try_repeat_gen simp_fun = simp_try_make_option_fun (birs_simp_check_ID_opt_fun (simp_try_repeat_gen_2 simp_fun));

  fun simp_try_apply_gen simp_fun simp_tm =
    let
      val simp_thm_o = simp_fun (simp_tm, NONE);
    in
      Option.getOpt (simp_thm_o, birs_simp_ID_fun simp_tm)
    end;

(* ----------------------------------------------------------------------------------- *)

(*
val instd_thm = ASSUME ``
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

birs_simp_try_fix_assumptions instd_thm;
*)
  fun birs_simp_try_justify_assumption assmpt =
    let
        val type_ofbirexp_CONV = type_of_bir_exp_CONV;
        val assmpt_thm = (type_ofbirexp_CONV THENC EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "birs_simp_try_justify_assumption" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "birs_simp_try_justify_assumption" ("failed to fix the assumption: " ^ (term_to_string assmpt));
    in
      if identical assmpt_new T then
        SOME (EQ_MP (GSYM assmpt_thm) TRUTH)
      else
        NONE
    end
    handle _ => NONE;
   val birs_simp_try_justify_assumption = aux_moveawayLib.wrap_cache_result Term.compare birs_simp_try_justify_assumption;

  (* need to handle typecheck, IS_SOME typecheck *)
  fun birs_simp_try_justify_assumptions NONE = NONE
    | birs_simp_try_justify_assumptions (SOME t) =
    if (not o is_imp o concl) t then
      SOME t
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm_o = birs_simp_try_justify_assumption assmpt;
      in
        case assmpt_thm_o of
           NONE => NONE
         | SOME assmpt_thm =>
             birs_simp_try_justify_assumptions
               (SOME (MP t assmpt_thm))
      end;

  fun birs_simp_try_fix_assumptions instd_thm =
    let
      (* now try to check the assumptions *)
      val final_thm_o = birs_simp_try_justify_assumptions (SOME instd_thm);
      val _ = if isSome final_thm_o andalso (birsSyntax.is_birs_simplification o concl) (valOf final_thm_o) then () else
        raise ERR "birs_simp_try_fix_assumptions" "this should not happen";
    in
      final_thm_o
    end;
  val birs_simp_try_fix_assumptions = Profile.profile "birs_simp_try_fix_assumptions" birs_simp_try_fix_assumptions;
  
(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)


  val get_op = fst o dest_comb;
  val get_rarg = snd o dest_comb;
  val get_larg = get_rarg o get_op;
  val get_fst_antec = fst o dest_imp;
  val get_snd_antec = get_fst_antec o snd o dest_imp;
  val get_conseq = fn tm => (if is_imp tm then (snd o strip_imp) else (I)) tm;

  (* match a term tm within in a theorem thm, use thm_tm_get to extract the part of the theorem to be matched with the part of the term tm that is extracted with tm_get *)
  fun simp_try_match_gen (thm_tm_get, tm_get) thm tm =
    let
      val thm_tm = (thm_tm_get o concl) thm;
      val tm_tm = tm_get tm;

      (* see if the simplification instance fits the simplification theorem conclusion (i.e. simplification term part) *)
      val tm_subst_o =
          SOME (match_term thm_tm tm_tm)
          handle _ => NONE;
    in
      (*
      val SOME tm_subst = tm_subst_o;
      *)
      Option.map (fn tm_subst => INST_TY_TERM tm_subst thm) tm_subst_o
    end;

  (* special case of matching, where first the forall quantifiers are removed and then the rightmost consequent is extracted (if it is an implication) *)
  fun simp_try_inst_gen (inst_tm_get, tm_get) simp_t tm =
    simp_try_match_gen (inst_tm_get o get_conseq, tm_get) (SPEC_ALL simp_t) tm;

(*
val simp_t = birs_simplification_Plus_Plus_Const_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;

birs_simp_try_inst simp_t simp_inst_tm;
*)
  (* for the plain cases (not subexpression, not pcond implication) *)
  (* select only the operations because in case of plain theorems, the last operand is the symbexp' we are trying to find *)
  val birs_simp_try_inst =
    simp_try_inst_gen (get_op, get_op);


  fun birs_simp_try_plain h_thm simp_tm =
    Option.mapPartial birs_simp_try_fix_assumptions (birs_simp_try_inst h_thm simp_tm);
  val birs_simp_try_plain = fn h_thm => simp_try_make_option_fun (birs_simp_try_plain h_thm);
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_plain birs_simp_exp_plain_thms (simp_inst_tm, NONE);
*)

(*
val simp_t = birs_simplification_IfThenElse_T_thm;
val simp_t = birs_simplification_IfThenElse_F_thm;
val simp_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_pcond simp_t simp_tm =
    let
      val simp_IMP_thm_inst =
        case birs_simp_try_inst birs_simplification_IMP_thm simp_tm of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_pcond" "this should always work if the arguments are right";
      (* continue with the instantiated simplification term that has a free variable for the path condition *)
      val simp_tm_new = (get_snd_antec o concl) simp_IMP_thm_inst;

      (* try to instantiate and fix the assumptions of the simplification theorem simp_t *)
      val simp_t_inst =
        case simp_try_inst_gen (get_larg, get_larg) simp_t simp_tm_new of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_pcond" "the provided theorem is not applicable for the provided simplification term";
      val simp_thm =
        case birs_simp_try_fix_assumptions simp_t_inst of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_pcond" "not all assumptions of the provided theorem hold";

      (* finish instantiation (i.e., path condition required by simp_t) *)
      val instd_thm =
        case simp_try_match_gen (get_snd_antec, I) simp_IMP_thm_inst (concl simp_thm) of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_pcond" "this should always work if the arguments are right";

      (* take out the implication predicate, prove it with the smt solver function, and remove it from the theorem *)
      val imp_tm = (get_fst_antec o concl) instd_thm;
      val imp_thm =
        case birs_utilsLib.check_imp_tm imp_tm of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_pcond" "path condition does not entail the simplification condition";
      val final_thm = MP (MP instd_thm imp_thm) simp_thm;
    in
      SOME final_thm
    end
    handle _ => NONE;
  val birs_simp_try_pcond = fn h_thm => simp_try_make_option_fun (birs_simp_try_pcond h_thm);
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_pcond birs_simp_exp_pcond_thms (simp_inst_tm, NONE);
*)

  (* "recursion" into certain subexpressions *)
(*
val simp_t = birs_simplification_Minus_thm;
val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_subexp sub_simp_fun simp_t simp_inst_tm =
    let
      val birs_simp_IMP_inst_t =
        case birs_simp_try_inst simp_t simp_inst_tm of
            SOME t => t
          | NONE => raise ERR "birs_simp_try_subexp" "cannot instantiate subexp theorem for the target simplification";
      val simp_inst_tm__ = (fst o dest_imp o concl) birs_simp_IMP_inst_t;

      val simp_thm_o = sub_simp_fun (simp_inst_tm__, NONE);
    in
      Option.map (fn simp_thm => MATCH_MP birs_simp_IMP_inst_t simp_thm) simp_thm_o
    end
    handle _ => NONE;
  val birs_simp_try_subexp = fn sub_simp_fun => fn simp_t => simp_try_make_option_fun (birs_simp_try_subexp sub_simp_fun simp_t);
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val abc = simp_try_fold_gen birs_simp_try_subexp birs_simp_exp_subexp_thms (simp_inst_tm, NONE);
*)


end (* local *)

end (* struct *)
