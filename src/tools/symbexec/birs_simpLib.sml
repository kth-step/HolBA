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
(*
  fun simp_try_fold_fun_gen simp_try_fun (t, thm_o) =
      if isSome thm_o then
        thm_o
      else
        (* SOME (MATCH_MP simp_thm (try_inst t simp_thm)) *)
        simp_try_fun (t, NONE)
        (*handle _ => NONE*);

  fun simp_try_fold_gen simp_try_fun h_thms (simp_tm, simp_thm_o) =
    List.foldl (fn (h_thm, simp_thm_o) => simp_try_fold_fun_gen (simp_try_fun h_thm) (simp_tm, simp_thm_o)) simp_thm_o h_thms;
*)
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
  fun wrap_cache_result f =
    let
      val assumption_dict = ref (Redblackmap.mkDict Term.compare);
      fun assumption_add (k_tm, tc_thm) = assumption_dict := Redblackmap.insert (!assumption_dict, k_tm, tc_thm);
      fun assumption_lookup k_tm = 
        SOME (Redblackmap.find (!assumption_dict, k_tm))
        handle NotFound => NONE;
      fun f_wrapped tm =
        let
          val a_thm_o = assumption_lookup tm;
        in
          if isSome a_thm_o then valOf a_thm_o else
          let
            val a_thm = f tm;
          in
            assumption_add (tm, a_thm);
            a_thm
          end
        end;
    in
      f_wrapped
    end;

  fun birs_simp_try_justify_assumption assmpt =
    let
        val type_ofbirexp_CONV = GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV);
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
   val birs_simp_try_justify_assumption = wrap_cache_result birs_simp_try_justify_assumption;

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
      (* Option.map (CONV_RULE (TRY_CONV (RAND_CONV EVAL) THENC REFL)) (* why was this here??*) *) final_thm_o
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

  fun check_imp_tm imp_tm =
   let
      (* input term: birs_exp_imp *)
      (* ================================================= *)
      (* TODO: function/code to remove imp assumption, with smt solver *)
      val pred1_tm = get_larg imp_tm;
      val pred2_tm = get_rarg imp_tm;
      val imp_bexp_tm = bslSyntax.bor (bslSyntax.bnot pred1_tm, pred2_tm);
      val imp_is_taut = bir_smt_check_taut false imp_bexp_tm;
      val imp_thm =
            if imp_is_taut then
              (* SOME (prove(imp_tm, cheat)) *)
              mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], imp_tm)
            else (
	      (*print_term imp_tm;*)
	      print "implication term is not a tautology\n";
              raise ERR "check_imp_tm" "implication term is not a tautology"
	    )
   in
      SOME imp_thm
   end
   handle _ => NONE;
   val check_imp_tm = wrap_cache_result check_imp_tm;



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
        case check_imp_tm imp_tm of
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


  (* TODO: need to keep simplifying using the three functions above repeatedly until not possible to simplify anymore *)
  (* - try direct simplification *)
  (* - try direct simplification in subexpressions *)
  (* - repeat the above until can't find anything to simplify *)



(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
  val pre_simp_thm = birs_simp_ID_fun simp_inst_tm;
  birs_simp_repeat simp_inst_tm;
*)

  (* combination function of the two kinds above (direct simplification) *)
  (* - try plain simplification *)
  (* - try implied simplification *)
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
(* ----------------------------------------------------------------------------------- *)

(*
  4 types of simplification functions, and recursive rinse&repeat
    - plain (only basic assumptions as typing or some numbers or other basic equalities)
    - pcond (starts out with basic assumptions, justify pcond implication with smt solver)
    - direct (first try all plain, then try pcond)
    - subexp (go into subexpression and then try direct, no recusion into subexpressions of subexpressions)

  recursive rinse&repeat
    - try direct, then try subexp, one simplification = one iteration, repeat until no more possible
  special treatment of store sequences, and load operations
*)

  val birs_simp_exp_plain_thms = List.rev (
    [birs_simplification_UnsignedCast_LowCast_Twice_thm,

     birs_simplification_Plus_Const64_thm,

     birs_simplification_Plus_Plus_Const64_thm,
     birs_simplification_Minus_Plus_Const64_thm,
     birs_simplification_Minus_Minus_Const64_thm,
     birs_simplification_Plus_Minus_Const64_thm(*,

     birs_simplification_Plus_Plus_Const32_thm,
     birs_simplification_Minus_Plus_Const32_thm,
     birs_simplification_Minus_Minus_Const32_thm,
     birs_simplification_Plus_Minus_Const32_thm*)]
  );

  val birs_simp_exp_pcond_thms = List.rev (
    [(*birs_simplification_And_Minus_CM0_thm,*)
     birs_simplification_LSB0_And64_RV_thm,
     birs_simplification_SignedLowCast3264_RV_thm,

     birs_simplification_IfThenElse_T_thm,
     birs_simplification_IfThenElse_F_thm]@
    (CONJUNCTS birs_simplification_Mem_Match_64_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm)(*@
    (CONJUNCTS birs_simplification_Mem_Match_32_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_32_8_thm)*)
  );

  val birs_simp_exp_subexp_thms = List.rev (
    [birs_simplification_UnsignedCast_thm,
     birs_simplification_SignedCast_thm,
     birs_simplification_LowCast_thm,
     birs_simplification_Minus_left_thm,
     birs_simplification_Plus_left_thm,
     birs_simplification_Plus_right_thm,
     birs_simplification_Load_addr_thm,
     birs_simplification_Store_addr_thm]
  );

(* ----------------------------------------------------------------------------------- *)

  val birs_simp_try_direct =
    simp_try_list_gen [
      simp_try_fold_gen birs_simp_try_plain birs_simp_exp_plain_thms,
      simp_try_fold_gen birs_simp_try_pcond birs_simp_exp_pcond_thms
    ];
  
  fun birs_simp_repeat simp_tm =
    let
      val simp_fun = simp_try_list_gen
          [birs_simp_try_direct,
           simp_try_fold_gen (birs_simp_try_subexp birs_simp_try_direct) birs_simp_exp_subexp_thms];
    in
      simp_try_apply_gen (simp_try_repeat_gen simp_fun) simp_tm
    end;
  val birs_simp_repeat = Profile.profile "birs_simp_repeat" birs_simp_repeat;

  fun birs_simp_load simp_tm =
    let
      (* TODO: constant propagation on the address, bypass as many stores as possible, try to match the load with a store *)
      val load_thms =
        (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm)@
        (CONJUNCTS birs_simplification_Mem_Match_64_8_thm);
      val simp_fun_mem_load = simp_try_repeat_gen (simp_try_fold_gen birs_simp_try_pcond load_thms);
      val cast_thms =
        [birs_simplification_UnsignedCast_thm,
         birs_simplification_SignedCast_thm,
         birs_simplification_LowCast_thm];
      val simp_fun = simp_try_list_gen
        [simp_try_fold_gen (birs_simp_try_subexp simp_fun_mem_load) cast_thms,
         simp_fun_mem_load];
      val simp_thm = simp_try_apply_gen simp_fun simp_tm;
      (*val _ = (print_term o get_rarg o concl) simp_thm;*)
    in
      simp_thm
    end;
  val birs_simp_load = Profile.profile "birs_simp_load" birs_simp_load;
  fun birs_simp_store simp_tm = birs_simp_ID_fun simp_tm; (* constant propagation on the address/value, try to remove another store (only one) *)
  val birs_simp_store = Profile.profile "birs_simp_store" birs_simp_store;
  (*fun birs_simp_load simp_tm = birs_simp_repeat simp_tm;*)
  fun birs_simp_store simp_tm = birs_simp_repeat simp_tm;
  fun birs_simp_gen simp_tm =
    let
        val start_exp_tm = get_larg simp_tm;
        open bir_expSyntax;
        (* loads are more complicated, in this case we have a cast, and within there is a load *)
        val isLoad = (fn t => is_BExp_Load t orelse (is_BExp_Cast t andalso (is_BExp_Load o (fn (_,x,_) => x) o dest_BExp_Cast) t)) start_exp_tm;
        val isStore = (is_BExp_Store) start_exp_tm;
        val _ =
          if isLoad then print "simplifying a load\n" else
          if isStore then print "simplifying a store\n" else
          print "it is neither a load nor a store\n";
    in
      if isLoad then birs_simp_load simp_tm else
      if isStore then birs_simp_store simp_tm else
      birs_simp_repeat simp_tm (* TODO: needs refactoring, bound the depth *)
    end;
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
