structure birs_intervalLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open stringSyntax;
  open bir_envSyntax bir_expSyntax bir_exp_immSyntax;

  open birsSyntax;
  open birs_utilsLib;
  open birs_mergeLib;

  (* error handling *)
  val libname = "birs_intervalLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  val debug_mode = false;

  fun vn_symb vn = "syi_" ^ vn;
  fun init_symb vn = ("sy_"^vn);

  fun dest_BExp_IntervalPred_normform_limit tm =
    let
      val (bop, left, right) = dest_BExp_BinExp tm;
      val refvar = dest_BExp_Den left;
      val v = dest_BExp_Const right;
      val _ =
        if is_BIExp_Plus bop
        then ()
        else raise ERR "dest_BExp_IntervalPred_normform_limit" "";
    in
      (refvar, v)
    end
    handle _ => raise ERR "dest_BExp_IntervalPred_normform_limit" ("not in standard shape" ^ (term_to_string tm));

  fun is_beq_left ref_symb tm = (is_comb tm) andalso ((identical (mk_comb (mk_comb (BExp_BinPred_tm, BIExp_Equal_tm), mk_BExp_Den ref_symb)) o fst o dest_comb) tm);
  fun is_binterval ref_symb tm = (is_comb tm) andalso ((identical (mk_comb (BExp_IntervalPred_tm, mk_BExp_Den ref_symb)) o fst o dest_comb) tm);
  fun beq_left_to_binterval ref_symb tm =
    let
      val minmax_tm = (snd o dest_comb) tm;
      val minmax_fixed_tm =
        if can dest_BExp_IntervalPred_normform_limit minmax_tm then
          minmax_tm
        else if is_BExp_Den minmax_tm then
          mk_BExp_BinExp (BIExp_Plus_tm, minmax_tm, mk_BExp_Const (``0w:word64``))
        else
          raise (print_term tm; ERR "beq_left_to_binterval" "unexpected expression");
    in mk_BExp_IntervalPred (mk_BExp_Den ref_symb, pairSyntax.mk_pair(minmax_fixed_tm, minmax_fixed_tm)) end;

  fun interval_from_state vn tm =
    let
      val (_,env,_,pcond) = dest_birs_state tm;
      val env_exp = (snd o get_env_top_mapping) env;
      (* check that env_exp is just a bexp_den and has the name vn_symb *)
      val _ = if (is_BExp_Den env_exp) andalso (((fn x => x = vn_symb vn) o fst o dest_BVar_string o dest_BExp_Den) env_exp) then () else
        raise ERR "interval_from_state" ("unexpected, the expression should be just the syi_ symbol: " ^ (term_to_string env_exp));
      val env_symbol = dest_BExp_Den env_exp;
      val pcondl = dest_bandl pcond;
      val pcond_intervaltms = List.filter (is_binterval env_symbol) pcondl;
      val pcondl_filtd = List.filter (not o is_binterval env_symbol) pcondl;
      val _ = if length pcond_intervaltms = 1 then () else
        raise ERR "interval_from_state" ("unexpected, could not find interval for: " ^ (term_to_string env_symbol));
      val interval = hd pcond_intervaltms;
    in
      (interval, fn x => bslSyntax.bandl (x::pcondl_filtd))
    end;

  fun dest_BExp_IntervalPred_normform tm =
    let
      val (x,iv) = dest_BExp_IntervalPred tm;
      val (l,h) = pairSyntax.dest_pair iv;
      val xvar = dest_BExp_Den x;
      val (refvarl, lval) = dest_BExp_IntervalPred_normform_limit l;
      val (refvarh, hval) = dest_BExp_IntervalPred_normform_limit h;
      val _ =
        if identical refvarl refvarh
        then ()
        else raise ERR "dest_BExp_IntervalPred_normform" "";
    in
      (xvar, refvarl, (lval,hval))
    end
    handle _ => raise ERR "dest_BExp_IntervalPred_normform" ("not in standard shape" ^ (term_to_string tm));

  fun is_BExp_IntervalPred_normform vn tm =
    let
      val (xvar, refvar, _) = dest_BExp_IntervalPred_normform tm;
    in
      ((fst o dest_BVar_string) xvar) = vn_symb vn andalso
      ((fst o dest_BVar_string) refvar) = init_symb vn
    end
    handle _ => false;

  fun check_BExp_IntervalPred_normform_RULE vn thm =
    let
      val Pi_tms = (pred_setSyntax.strip_set o get_birs_Pi o concl) thm;
      val intervaltms = List.map (fst o interval_from_state vn) Pi_tms;

      val is_ok = if List.all (is_BExp_IntervalPred_normform vn) intervaltms then () else (
        print_thm thm;
        raise ERR "check_BExp_IntervalPred_normform_RULE" "some interval is not in a standard form"
      );
    in
      thm
    end;

local
val intervalpattern64_tm = ``
  BExp_IntervalPred (BExp_Den (BVar x_a (BType_Imm Bit64)))
    (BExp_BinExp BIExp_Plus (BExp_Den (BVar x_b (BType_Imm Bit64)))
     (BExp_Const (Imm64 x_c)),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar x_b (BType_Imm Bit64)))
     (BExp_Const (Imm64 x_d)))``;
val intervalpattern64_inst_tm = ``
  BExp_IntervalPred (BExp_Den (BVar x_a (BType_Imm Bit64)))
    (BExp_BinExp BIExp_Plus (BExp_BinExp BIExp_Plus (BExp_Den (BVar x_b (BType_Imm Bit64)))
     (BExp_Const (Imm64 x_c1)))
     (BExp_Const (Imm64 x_c2)),
   BExp_BinExp BIExp_Plus (BExp_BinExp BIExp_Plus (BExp_Den (BVar x_b (BType_Imm Bit64)))
     (BExp_Const (Imm64 x_d1)))
     (BExp_Const (Imm64 x_d2)))``;

fun get_interval_parameters i_tm =
  let
          val (vs, _) = hol88Lib.match intervalpattern64_tm i_tm;
          val symb_str      = fst (List.nth (vs, 0));
          val refsymb_str = fst (List.nth (vs, 1));
          val lc = fst (List.nth (vs, 2));
          val hc = fst (List.nth (vs, 3));
  in
    (fromHOLstring symb_str, fromHOLstring refsymb_str,
     (Arbnum.toInt o wordsSyntax.dest_word_literal) lc,
     (Arbnum.toInt o wordsSyntax.dest_word_literal) hc)
  end
  handle _ => raise ERR "get_interval_parameters" ("no match? : " ^ (term_to_string i_tm));
fun get_interval_parameters_inst i_tm =
  let
          val (vs, _) = hol88Lib.match intervalpattern64_inst_tm i_tm;
          val symb_str      = fst (List.nth (vs, 0));
          val refsymb_str = fst (List.nth (vs, 1));
          val lc1 = fst (List.nth (vs, 2));
          val lc2 = fst (List.nth (vs, 3));
          val hc1 = fst (List.nth (vs, 4));
          val hc2 = fst (List.nth (vs, 5));
  in
    (fromHOLstring symb_str, fromHOLstring refsymb_str,
     (Arbnum.toInt o wordsSyntax.dest_word_literal) lc1 +
     (Arbnum.toInt o wordsSyntax.dest_word_literal) lc2,
     (Arbnum.toInt o wordsSyntax.dest_word_literal) hc1 +
     (Arbnum.toInt o wordsSyntax.dest_word_literal) hc2)
  end
  handle _ => raise ERR "get_interval_parameters_inst" ("no match? : " ^ (term_to_string i_tm));
fun mk_interval_tm (symb_str, refsymb_str, lc, hc) =
  subst [``x_a:string`` |-> fromMLstring symb_str,
         ``x_b:string`` |-> fromMLstring refsymb_str,
         ``x_c:word64`` |-> wordsSyntax.mk_wordii(lc, 64),
         ``x_d:word64`` |-> wordsSyntax.mk_wordii(hc, 64)
        ] intervalpattern64_tm;
in
(*
val interval1 = ``BExp_IntervalPred (BExp_Den (BVar "syr_7" (BType_Imm Bit64)))
  (BExp_BinExp BIExp_Plus (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)))``;

val interval2 = ``BExp_IntervalPred (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
  (BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 (5w))),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 (5w))))``;
*)
  (* interval1 uses interval2 *)
  fun fuse_intervals interval1 interval2 =
    let
      val _ = if not debug_mode then () else print "starting to fuse two intervals\n";
      (* quickfix for unfinished word expression in constants *)
      val interval1 = (snd o dest_eq o concl o RAND_CONV EVAL) interval1;
      val interval2 = (snd o dest_eq o concl o RAND_CONV EVAL) interval2;
      val _ = if not debug_mode then () else print_term interval1;
      val _ = if not debug_mode then () else print_term interval2;
      val (symb_str1, refsymb_str1, lc1, hc1) = get_interval_parameters interval1;
      val (symb_str2, refsymb_str2, lc2, hc2) = get_interval_parameters interval2;
      val _ = if (refsymb_str1 = symb_str2) then () else
        raise ERR "fuse_intervals" "intervals are not trivially compatible";
      val lc_min = lc1 + lc2;
      val hc_max = hc1 + hc2;
      val interval = mk_interval_tm (symb_str1, refsymb_str2, lc_min, hc_max);
    in
      interval
    end;

(*
val interval1 = ``BExp_IntervalPred (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
  (BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)))``;

val interval2 = ``BExp_IntervalPred (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
  (BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)),
   BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
     (BExp_Const (Imm64 21w)))``;
*)
  fun widen_intervals (interval1, interval2) =
    let
      val _ = if not debug_mode then () else print "starting to find the widest limits of two intervals\n";
      (* quickfix for unfinished word expression in constants *)
      val interval1 = (snd o dest_eq o concl o RAND_CONV EVAL) interval1;
      val interval2 = (snd o dest_eq o concl o RAND_CONV EVAL) interval2;
      val _ = if not debug_mode then () else print_term interval1;
      val _ = if not debug_mode then () else print_term interval2;
      val (symb_str1, refsymb_str1, lc1, hc1) = get_interval_parameters interval1;
      val (symb_str2, refsymb_str2, lc2, hc2) = get_interval_parameters interval2;
      val _ = if (symb_str1 = symb_str2) andalso (refsymb_str1 = refsymb_str2) then () else
        raise ERR "widen_intervals" "intervals are not trivially compatible";
      val lc_min = if lc1 < lc2 then lc1 else lc2;
      val hc_max = if hc1 > hc2 then hc1 else hc2;
      val interval = mk_interval_tm (symb_str1, refsymb_str1, lc_min, hc_max);
    in
      interval
    end;

  (*
  val interval = ``
          BExp_IntervalPred
            (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
            (BExp_BinExp BIExp_Plus
              (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 5w))) (BExp_Const (Imm64 21w)),
            BExp_BinExp BIExp_Plus
              (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 5w))) (BExp_Const (Imm64 21w)))
  ``;
  val i_tm = interval;
  *)
  fun simplify_interval tm =
    (mk_interval_tm o get_interval_parameters_inst) tm
    handle _ => tm;
end

in (* local *)

  fun birs_intervals_Pi_first_simplify_limits thm =
    let
      (* simplify the limits of the intervals in the pathcondition *)
      val pcond = (get_birs_Pi_first_pcond o concl) thm;
      val pcondl = dest_bandl pcond;
      val pcondl_fixed = List.map (fn tm => if is_BExp_IntervalPred tm then simplify_interval tm else tm) pcondl;
      val thm_fixed = birs_Pi_first_pcond_RULE (bslSyntax.bandl pcondl_fixed) thm;
    in
      thm_fixed
    end;

  (* unifies the representation of the interval for env mapping vn (handles introduction (e.g., after symbolic execution without interval) and also fusion of transitive intervals (e.g., after instantiation)) *)
    (* afterwards: vn is on top, symbolname mapped for interval is ("syi_"^vn), exactly one interval relating to it in the pathcondition *)
    (* this has to be used after an instantiation and after an execution (which in turn is either from an initial state, or from after a merge operation), and before a bounds operation below *)
  fun birs_intervals_Pi_first_unify_RULE vn thm =
    let
      val _ = birs_check_norm_thm ("birs_intervals_Pi_first_unify_RULE", "") thm;

      val _ = if not debug_mode then () else print "starting to unify interval for one Pi state\n";

      (* bring up mapping vn to the top of env mappings *)
      val thm_ = CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV vn)) thm;
      val thm0 = birs_intervals_Pi_first_simplify_limits thm_;
      val env_exp = (snd o get_birs_Pi_first_env_top_mapping o concl) thm0;

      (* is the mapping just a symbol, which is not the initial symbolic one?
          then remember it (because there should already be an interval for it in the path condition),
          otherwise freesymbol the mapping *)
      val (thm1, env_symbol) =
        if (is_BExp_Den env_exp) andalso (((fn x => x <> init_symb vn) o fst o dest_BVar_string o dest_BExp_Den) env_exp) then
          (thm0, dest_BExp_Den env_exp)
        else
          let
            val exp_tm = env_exp;
            val symbname = get_freesymb_name ();
            val symb_tm = mk_BVar (fromMLstring symbname, (bir_exp_typecheckLib.get_type_of_bexp exp_tm));
            val thm1 = birs_Pi_first_freesymb_RULE symbname exp_tm (fn x => (K (K x))) thm0;
          in (thm1, symb_tm) end;
      val _ = if not debug_mode then () else print "freesymboling done\n";
      (* now we have only one symbol env_symbol in the mapping and the rest should be in the path condition *)

      (* need to operate on the path condition *)
      val pcond = (get_birs_Pi_first_pcond o concl) thm1;
      val pcondl = dest_bandl pcond;

      (* search for related simple equality, or for an interval *)
      val pcond_eqtms = List.filter (is_beq_left env_symbol) pcondl;
      val pcond_intervaltms_0 = List.filter (is_binterval env_symbol) pcondl;
      val pcondl_filtd = (List.filter (not o is_binterval env_symbol) o List.filter (not o is_beq_left env_symbol)) pcondl;
      val intervaltm =
        if length pcond_eqtms = 0 then (
          if length pcond_intervaltms_0 = 0 then
            raise ERR "birs_intervals_Pi_first_unify_RULE" ("unexpected, seems like " ^ vn ^ "is a free symbol or not managed by birs_intervalLib")
          else if length pcond_intervaltms_0 > 1 then
            raise ERR "birs_intervals_Pi_first_unify_RULE" ("unexpected1")
          else
            hd pcond_intervaltms_0
        ) else if length pcond_eqtms > 1 then
          raise ERR "birs_intervals_Pi_first_unify_RULE" "unexpected2"
        else
          (* introduction of interval must already start in standard form, limits have to be plus(den,const) *)
          (beq_left_to_binterval env_symbol (hd pcond_eqtms));
      val _ = if not debug_mode then () else print_term intervaltm;

      (* TODO: this interval should relate to the original symbol, or maybe another interval that it relates to *)
      (* TODO: the following is a quick solution without much checks *)
      fun get_ref_symb intervaltm_ =
        let
          val refsymbs = List.filter (fn x => not (identical x env_symbol)) (bir_vars_ofLib.get_vars_of_bexp intervaltm_);
          (*
          val _ = PolyML.print_depth 10;
          val _ = PolyML.print refsymbs;
          val _ = print_term (hd refsymbs);
          *)
          val _ = if length refsymbs = 1 then () else
            (print "\n\n"; print_term env_symbol; print_term intervaltm_; print "\n\n";
             raise ERR "birs_intervals_Pi_first_unify_RULE::get_ref_symb" "unexpected");
        in
          hd refsymbs
        end;
      val refsymb = get_ref_symb intervaltm;
      val (intervalterm_fusion, pcondl_filtd_two) =
        if (fst o dest_BVar_string) refsymb = init_symb vn then
          (intervaltm, pcondl_filtd)
        else
          let
            val pcond_intervaltms_1 = List.filter (is_binterval refsymb) pcondl_filtd;
            val pcondl_filtd_two = List.filter (not o is_binterval refsymb) pcondl_filtd;
          in
            if length pcond_intervaltms_1 = 1 then
              (fuse_intervals (intervaltm) (hd pcond_intervaltms_1), pcondl_filtd_two)
            else
              (print "\n\n";print_term pcond;print "\n\n";print_term (bslSyntax.bandl pcondl_filtd);print "\n\n";List.map print_term pcond_intervaltms_1;print "\n\n";
               raise ERR "birs_intervals_Pi_first_unify_RULE" ("unexpected3"))
          end;
      val _ = if not debug_mode then () else print_term intervalterm_fusion;

      val pcond_new = bslSyntax.bandl (intervalterm_fusion::pcondl_filtd_two);
      val thm2 = birs_Pi_first_pcond_RULE pcond_new thm1;
      val thmx = thm2;

      (* all that is left is to make sure that we use the standardname for the symbol in the envmapping, if not, just rename it *)
        (* rename so that the symbol used is ("syi_"^vn) for readability *)
      (* TODO: check, at this point no BVar symbol with the name vn_symb should occur in thm *)
      (* TODO: we will need a rename rule for this later, this one just works now because it is not following the theorem checks *)
      val thm9 = birs_instantiationLib.birs_sound_symb_inst_RULE [(env_symbol, mk_BExp_Den (mk_BVar_string (vn_symb vn, (snd o dest_BVar) env_symbol)))] thmx;

      val _ = if not debug_mode then () else print "done unifying interval for one Pi state\n";
    in
      thm9
    end;

  fun birs_intervals_Pi_unify_RULE vn = birs_Pi_each_RULE (birs_intervals_Pi_first_unify_RULE vn);
  val birs_intervals_Pi_unify_RULE = fn vn => check_BExp_IntervalPred_normform_RULE vn o birs_intervals_Pi_unify_RULE vn;
  val birs_intervals_Pi_unify_RULE = fn x => Profile.profile "birs_intervals_Pi_unify_RULE" (birs_intervals_Pi_unify_RULE x);

  (* goes through all Pi states and unifies the interval bounds for env mapping vn (needed prior to merging of states) *)
    (* assumes that the unify rule was running before *)
    (* this has to be used after a unify operation above, and before the actual merging to be able to keep the interval in the path condition and the symbol reference in the environment mapping *)
  fun birs_intervals_Pi_bounds_RULE vn thm =
    let
      val _ = birs_check_norm_thm ("birs_intervals_Pi_bounds_RULE", "") thm;
      val Pi_len = (get_birs_Pi_length o concl) thm;
    in
     if Pi_len < 2 then thm else
     let
      val _ = if not debug_mode then () else print "starting to widen the bounds of the intervals in all Pi states\n";

      (* collect the intervals from each Pi pathcondition *)
      val Pi_tms = (pred_setSyntax.strip_set o get_birs_Pi o concl) thm;
      fun interval_from_state tm =
        let
          val (_,env,_,pcond) = dest_birs_state tm;
          val env_exp = (snd o get_env_top_mapping) env;
          (* check that env_exp is just a bexp_den and has the name vn_symb *)
          val _ = if (is_BExp_Den env_exp) andalso (((fn x => x = vn_symb vn) o fst o dest_BVar_string o dest_BExp_Den) env_exp) then () else
            raise ERR "birs_intervals_Pi_bounds_RULE" ("unexpected, the expression should be just the syi_ symbol: " ^ (term_to_string env_exp));
          val env_symbol = dest_BExp_Den env_exp;
          val pcondl = dest_bandl pcond;
          val pcond_intervaltms = List.filter (is_binterval env_symbol) pcondl;
          val pcondl_filtd = List.filter (not o is_binterval env_symbol) pcondl;
          val _ = if length pcond_intervaltms = 1 then () else
            raise ERR "birs_intervals_Pi_bounds_RULE" ("unexpected, could not find interval for: " ^ (term_to_string env_symbol));
          val interval = hd pcond_intervaltms;
        in
          (interval, fn x => bslSyntax.bandl (x::pcondl_filtd))
        end;
      val (intervaltms, pcond_new_funs) = unzip (List.map interval_from_state Pi_tms);

      (* compute the new min and max, generate the new interval predicate with it *)
      val interval_largest = List.foldl widen_intervals (hd intervaltms) (tl intervaltms);

      (* for each Pi state: replace the old predicate with the new one and justify with Pi_first_pcond_RULE *)
      val pconds = List.map (fn x => x interval_largest) pcond_new_funs;
      val thm_new = List.foldl (birs_Pi_rotate_RULE o (fn (pcond,acc) => birs_Pi_first_pcond_RULE pcond acc)) thm pconds;

      val _ = if not debug_mode then () else print "done widening the bounds of the intervals in all Pi states\n";
     in
      thm_new
     end
    end;
  val birs_intervals_Pi_bounds_RULE = fn vn => check_BExp_IntervalPred_normform_RULE vn o birs_intervals_Pi_bounds_RULE vn;
  val birs_intervals_Pi_bounds_RULE = fn x => Profile.profile "birs_intervals_Pi_bounds_RULE" (birs_intervals_Pi_bounds_RULE x);

(*
  (* use this function after an execution (or after merging), and before the next merging *)
  fun birs_intervals_Pi_RULE vn = (birs_intervals_Pi_bounds_RULE vn o birs_intervals_Pi_unify_RULE vn);
*)


end (* local *)

end (* struct *)

(* ================================================================================================================ *)

(*
    local
      open pred_setSyntax;
      val rotate_first_INSERTs_thm = prove(``
        !x1 x2 xs.
        (x1 INSERT x2 INSERT xs) = (x2 INSERT x1 INSERT xs)
      ``,
        cheat
      );
      fun is_two_INSERTs tm = (is_insert tm) andalso ((is_insert o snd o dest_insert) tm);
    in
      fun rotate_two_INSERTs_conv tm =
        let
          val _ = if is_two_INSERTs tm then () else
            raise ERR "rotate_two_INSERTs_conv" "need to be a term made up of two inserts";
          val (x1_tm, x2xs_tm) = dest_insert tm;
          val (x2_tm, xs_tm) = dest_insert x2xs_tm;
          val inst_thm = ISPECL [x1_tm, x2_tm, xs_tm] rotate_first_INSERTs_thm;
        in
          (* TODO: the result of this should actually just be inst_thm *)
          REWRITE_CONV [Once inst_thm] tm
        end;

      fun rotate_INSERTs_conv tm =
        (if not (is_two_INSERTs tm) then REFL else
         (rotate_two_INSERTs_conv THENC
          RAND_CONV rotate_INSERTs_conv)) tm;
    end


rotate_INSERTs_conv “{1;2;3;4;5}”

val thm = (prove(“
birs_symb_exec bir_balrob_prog
          (<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x100013B4w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [];
             bsst_status := BST_Running;
             bsst_pcond := BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)) |>,
           {<|bpc_label := BL_Address (Imm32 0x100013BCw); bpc_index := 2|>},
{
<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x0w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
                  ("PSR_Z",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                  ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));];
             bsst_status := BST_Running;
             bsst_pcond := BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)) |>
;
<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x1w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
                  ("PSR_Z",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                  ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));];
             bsst_status := BST_Running;
             bsst_pcond := BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)) |>
;
<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x2w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
                  ("PSR_Z",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                  ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));];
             bsst_status := BST_Running;
             bsst_pcond := BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)) |>
;
<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x3w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
                  ("PSR_Z",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                  ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));];
             bsst_status := BST_Running;
             bsst_pcond := BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)) |>

})
”, cheat));


birs_utilsLib.birs_Pi_rotate_RULE thm;

birs_intervals_Pi_unify_RULE "PSR_Z" thm
*)
