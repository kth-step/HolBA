structure bir_symbexec_coreLib =
struct

local
  open bir_symbexec_stateLib;

  open bir_constpropLib;
  open bir_envSyntax;
  open bir_exp_helperLib;
in (* outermost local *)


(* primitive for symbolic/abstract computation for expressions *)
local
  open bir_expSyntax;

  fun subst_fun env vals (bev, (e, vars)) =
    let
      val bv_ofvals = find_bv_val "subst_fun" env bev;

      val (exp, vars') =
        let
          val symbv = find_bv_val "subst_fun" vals bv_ofvals;
          val expo = case symbv of
                       SymbValBE (x, _) => SOME x
                     | _ => NONE;
          val use_expo_var =
            isSome expo andalso
            (bir_expSyntax.is_BExp_Const o valOf) expo;
        in
          if use_expo_var then
            (valOf expo, vars)
          else raise ERR "subst_fun" "this is never seen"
        end
        handle _ => (mk_BExp_Den bv_ofvals, bv_ofvals::vars);
    in
      (subst_exp (bev, exp, e),
       vars')
    end;

  (* TODO: make this available at some more central location (it is from src/tools/exec/auxLib *)
  fun find_subterm is_tm_fun tm =
    if is_tm_fun tm then
      SOME tm
    else if is_comb tm then
      let
        val (l,r) = dest_comb tm;
      in
        case find_subterm is_tm_fun l of
           SOME tm2 => SOME tm2
         | NONE => find_subterm is_tm_fun r
      end
    else
      NONE
    ;

  fun subterm_satisfies is_tm_fun tm =
    (isSome o find_subterm is_tm_fun) tm;

  fun compute_val_try_const_only vals (besubst, besubst_vars) deps_l2 =
    let
      val all_deps_const = List.all (fn bv =>
             (is_bvar_bound vals) bv andalso
             (case find_bv_val "compute_val_try_const_only" vals bv of
                 SymbValBE (exp,_) => is_BExp_Const exp
               | _ => false)
           ) besubst_vars;
    in
      if all_deps_const then
        if List.null besubst_vars then NONE else
        let
          val _ = if Redblackset.isEmpty deps_l2 then () else
                  raise ERR "compute_val_try_const_only" "deps_l2 is not empty. Unexpected here.";

          fun subst_fun_symbvalbe vals (bv_dep, e) =
            let
              val symbv_dep = find_bv_val "compute_val_try_const_only" vals bv_dep;
              val exp = case symbv_dep of
                           SymbValBE (exp,_) => exp
                         | _ => raise ERR "compute_val_try_const_only" "cannot happen";
            in
              subst_exp (bv_dep, exp, e)
            end;

          val becomp = List.foldr (subst_fun_symbvalbe vals) besubst besubst_vars;
        in
          SOME (SymbValBE (becomp, symbvalbe_dep_empty))
        end
      else
        NONE
    end;

  open bslSyntax;
  val var_add_const_match_tm = bplus (bden ``x:bir_var_t``, bconstimm ``y:bir_imm_t``);
  val const_add_var_match_tm = bplus (bconstimm ``y:bir_imm_t``, bden ``x:bir_var_t``);
  val var_sub_const_match_tm = bminus(bden ``x:bir_var_t``, bconstimm ``y:bir_imm_t``);

  fun add_imms imm_val imm_val_2 = 
        (snd o dest_eq o concl o EVAL) ``bir_bin_exp BIExp_Plus ^imm_val ^imm_val_2``;
  fun sub_imms imm_val imm_val_2 = 
        (snd o dest_eq o concl o EVAL) ``bir_bin_exp BIExp_Minus ^imm_val ^imm_val_2``;

  fun compute_val_try_single_interval vals (besubst, besubst_vars) =
    let
      val depends_on_single_interval =
             length besubst_vars = 1 andalso
             (is_bvar_bound vals) (hd besubst_vars) andalso
             (case find_bv_val "compute_val_try_single_interval" vals (hd besubst_vars) of
                 SymbValInterval _ => true
               | _ => false);
    in
      if depends_on_single_interval then
        let
          val (vs, _) = hol88Lib.match var_add_const_match_tm besubst;
          val bv      = fst (List.nth (vs, 0));
          val imm_val = fst (List.nth (vs, 1));

          val _ = if identical bv (hd besubst_vars) then () else
                  raise ERR "compute_val_try_single_interval" "something is not right 1...";

          val ((itv_exp1, itv_exp2), itv_deps) =
             (case find_bv_val "compute_val_try_single_interval" vals bv of
                 SymbValInterval x => x
               | _ => raise ERR "compute_val_try_single_interval" "something is not right 2...");

          fun add_const exp imm_val =
            if is_BExp_Den exp then bplus (exp, bconstimm imm_val) else
            let
              val (vs, _) = hol88Lib.match var_add_const_match_tm exp;
              val bv_       = fst (List.nth (vs, 0));
              val imm_val_2 = fst (List.nth (vs, 1));

              val res_tm = add_imms imm_val imm_val_2;
            in
              bplus (bden bv_, bconstimm res_tm)
            end;
        in
          SOME (SymbValInterval ((add_const itv_exp1 imm_val,
                                  add_const itv_exp2 imm_val),
                                 itv_deps))
        end
        handle HOL_ERR _ => NONE
      else
        NONE
    end;
(*
(print "(((((((((((((((((((((((())))))))))))))))))))))))\n\n\n"; 
*)
  fun get_var_plusminus_const exp =
    let
      val (vs, _) = hol88Lib.match var_add_const_match_tm exp;
      val bv      = fst (List.nth (vs, 0));
      val imm_val = fst (List.nth (vs, 1));
    in
      (bv, (imm_val, true))
    end
    handle HOL_ERR _ => (
    let
      val (vs, _) = hol88Lib.match const_add_var_match_tm exp;
      val bv      = fst (List.nth (vs, 1));
      val imm_val = fst (List.nth (vs, 0));
    in
      (bv, (imm_val, true))
    end
    handle HOL_ERR _ =>
    let
      val (vs, _) = hol88Lib.match var_sub_const_match_tm exp;
      val bv      = fst (List.nth (vs, 0));
      val imm_val = fst (List.nth (vs, 1));
    in
      (bv, (imm_val, false))
    end);

  fun add_imm_plusminus (imm_val1, true) (imm_val2, true) =
        (add_imms imm_val1 imm_val2, true)
    | add_imm_plusminus (imm_val1, false) (imm_val2, false) =
        (add_imms imm_val1 imm_val2, false)
    | add_imm_plusminus (imm_val1, true) (imm_val2, false) =
        add_imm_plusminus (imm_val2, false) (imm_val1, true)
    | add_imm_plusminus (imm_val1, false) (imm_val2, true) =
        if Arbnum.<= (
             (wordsSyntax.dest_word_literal o snd o bir_immSyntax.gen_dest_Imm) imm_val1,
             (wordsSyntax.dest_word_literal o snd o bir_immSyntax.gen_dest_Imm) imm_val2) then
          (sub_imms imm_val2 imm_val1, true)
        else
          (sub_imms imm_val1 imm_val2, false);

  fun exp_from_bv_plusminus_imm bv (imm_val, imm_plus) =
    (if imm_plus then bplus else bminus)
    (bden bv, bconstimm imm_val);

  fun compute_val_try_expplusminusconst vals (besubst, besubst_vars) =
    let
      val depends_on_single_exp =
             length besubst_vars = 1 andalso
             (is_bvar_bound vals) (hd besubst_vars) andalso
             (case find_bv_val "compute_val_try_expplusminusconst" vals (hd besubst_vars) of
                 SymbValBE _ => true
               | _ => false);
    in
      if depends_on_single_exp then
        let
          val (bv, imm_val_pm) = get_var_plusminus_const besubst;

          val (exp2, deps2) =
             (case find_bv_val "compute_val_try_expplusminusconst" vals bv of
                 SymbValBE x => x
               | _ => raise ERR "compute_val_try_expplusminusconst" "something is not right 2...");

          val (bv2, imm_val_pm2) = get_var_plusminus_const exp2;

          val imm_val_pm12 = add_imm_plusminus imm_val_pm imm_val_pm2;
        in
          SOME (SymbValBE (exp_from_bv_plusminus_imm bv2 imm_val_pm12, deps2))
        end
        handle HOL_ERR _ => NONE
      else
        NONE
    end;

  fun process_addr str_op vals addr_tm =
    let
      val debugOn = false;
      val _ = if not debugOn then () else
              print (str_op ^ "\n---------------\n");
      (*
      val _ = (print ("addr " ^ str_op ^ ": [[[\n"); print_term addr_tm; print "]]]\n\n");
      *)
      val addr_tm_vars = get_birexp_vars addr_tm;
      val addr_ =
          if is_BExp_Den addr_tm then
            SOME (find_bv_val "state_make_interval" vals (dest_BExp_Den addr_tm))
          else
            compute_val_try_expplusminusconst vals (addr_tm, addr_tm_vars);
      (*
      val _ = if isSome addr_ then print (symbv_to_string (valOf addr_)) else
              print "NONE";
      *)
      val (addr, addr_deps) =
          case addr_ of
             SOME (SymbValBE x) => x
           | NONE => (addr_tm, Redblackset.addList (symbvalbe_dep_empty, addr_tm_vars))
           | _ => raise ERR "process_addr" "NEEDS TO BE A SYMBOLIC EXPRESSION";

      val _ = if not debugOn then () else
              (print ("addr proc: {{{\n"); print_term addr; print "}}}\n\n");
    in
      (addr, addr_deps)
    end;

  fun compute_val_try_mem vals (besubst, besubst_vars) =
    let
      val debugOn = false;
      val _ = if not debugOn then () else
              print_term besubst;
      val _ = if not debugOn then () else 
              print "\n==========================================\n\n";
    in
      if is_BExp_Load besubst then
        let
          val (mem_tm, addr_tm, end_tm, sz_tm) = dest_BExp_Load besubst;
          val (addr, addr_deps) = process_addr "load" vals addr_tm;

          val _ = if not debugOn then () else
                  print_term sz_tm;
        in
          if true then NONE else raise ERR "compute_val_try" "load debugging"
        end
      else if is_BExp_Store besubst orelse is_BExp_Load besubst then
        let
          val (mem_tm, addr_tm, end_tm, val_tm) = dest_BExp_Store besubst;
          val (addr, addr_deps) = process_addr "store" vals addr_tm;

          val _ = if not debugOn then () else
                  print_term val_tm;
        in
          if true then NONE else raise ERR "compute_val_try" "store debugging"
        end
(*
      else if subterm_satisfies is_BExp_Load besubst orelse
              subterm_satisfies is_BExp_Store besubst then
        raise ERR "compute_val_try"
                  ("found load or store as subexpression, unexpected: " ^
                   term_to_string besubst)
*)
      else
        NONE
    end;

  fun compute_val_try vals (besubst, besubst_vars) deps_l2 =
    case compute_val_try_const_only vals (besubst, besubst_vars) deps_l2 of
        SOME x => SOME x
      | NONE => (
    case compute_val_try_single_interval vals (besubst, besubst_vars) of
        SOME x => SOME x
      | NONE => (
    case compute_val_try_expplusminusconst vals (besubst, besubst_vars) of
        SOME x => SOME x
      | NONE => (
         compute_val_try_mem vals (besubst, besubst_vars)
    )));

  fun compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    let
      val deps_l2 = List.foldr (Redblackset.union)
                               symbvalbe_dep_empty
                               (List.map (deps_find_symbval "compute_val_and_resolve_deps" vals) besubst_vars);
    in
      case compute_val_try vals (besubst, besubst_vars) deps_l2 of
         SOME x => x
       | NONE   =>
          let
            val deps = Redblackset.addList(deps_l2, besubst_vars);
            val be_new_val = SymbValBE (besubst, deps);
          in
            be_new_val
          end
    end;

  val sp_align_sub_const_match_tm = ``
        (BExp_BinExp BIExp_Minus
          (BExp_Align Bit32 2 (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
          (BExp_Const y))``;

  fun simplify_be be syst =
    let
      val (vs, _) = hol88Lib.match sp_align_sub_const_match_tm be;
      val imm_val = fst (List.nth (vs, 0));

      val replacewith_tm = ``
        (BExp_BinExp BIExp_Minus
          (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
          (BExp_Const ^imm_val))``;

      (* TODO: use smt solver to prove equality under path predicate *)
    in
      replacewith_tm
    end
    handle HOL_ERR _ => be;

in (* local *)

  fun compute_valbe be syst =
    let
      val env  = SYST_get_env  syst;
      val vals = SYST_get_vals syst;

      val be_   = simplify_be be syst;
      (* TODO: we may be left with an expression that fetches a single variable from the environment *)

      val be_vars = get_birexp_vars be_;
      val besubst_with_vars = List.foldr (subst_fun env vals) (be_, []) be_vars;
    in
      compute_val_and_resolve_deps vals besubst_with_vars
    end;

end (* local *)


(* primitive to compute expression and store result using fresh variable *)
  fun state_insert_symbval_from_be bv_fr be syst =
      insert_symbval bv_fr (compute_valbe be syst) syst;

(* primitive to carry out assignment *)
  fun state_assign_bv bv be syst =
    let
      val symbv = compute_valbe be syst;
      val expo = case symbv of
                    SymbValBE (x, _) => SOME x
                  | _ => NONE;
      val use_expo_var =
            isSome expo andalso
            (bir_expSyntax.is_BExp_Den o valOf) expo;

      val bv_fr = if use_expo_var then
                    (bir_expSyntax.dest_BExp_Den o valOf) expo
                  else
                    (get_bvar_fresh) bv;
    in
      (update_envvar bv bv_fr o
       (if use_expo_var then
          I
        else
          insert_symbval bv_fr symbv)
      ) syst
    end;

  fun state_make_interval bv syst =
    let
      val env    = SYST_get_env syst;
      val bv_val = find_bv_val "state_make_interval" env bv;
      val _ = if is_bvar_init bv_val then () else
              raise ERR "state_make_interval" "can only make interval values from initial variables currently";

      val exp   = bir_expSyntax.mk_BExp_Den bv_val;
      val deps  = Redblackset.add (symbvalbe_dep_empty, bv_val);
      val symbv = SymbValInterval ((exp, exp), deps);

      val bv_fresh = (get_bvar_fresh) bv;
    in
      (update_envvar bv bv_fresh o
       insert_symbval bv_fresh symbv
      ) syst
    end;

  fun state_make_mem bv layout syst =
    let
      val env    = SYST_get_env syst;
      val bv_val = find_bv_val "state_make_interval" env bv;
      val _ = if is_bvar_init bv_val then () else
              raise ERR "state_make_mem" "can only make interval values from initial variables currently";

      val exp   = bir_expSyntax.mk_BExp_Den bv_val;
      val deps  = Redblackset.add (symbvalbe_dep_empty, bv_val);
      val symbv = SymbValMem ((I, exp, exp), layout, deps);

      val bv_fresh = (get_bvar_fresh) bv;
    in
      (update_envvar bv bv_fresh o
       insert_symbval bv_fresh symbv
      ) syst
    end;

(* primitives for adding conjuncts to the path predicate *)
  fun state_add_pred bv_str pred syst =
    let
      val bv = bir_envSyntax.mk_BVar_string (bv_str, bir_valuesSyntax.BType_Bool_tm);
      val bv_fresh = get_bvar_fresh bv;
    in
      (SYST_update_pred ((bv_fresh)::(SYST_get_pred syst)) o
       state_insert_symbval_from_be bv_fresh pred
      ) syst
    end;

  fun state_add_preds bv_str preds syst =
    List.foldr (fn (pred, syst_) => state_add_pred bv_str pred syst_) syst preds;

(* primitive for removing the head of the path predicate *)
  fun state_remove_preds_by_suffix pred_suffix syst =
    let
      val preds = SYST_get_pred syst;
      val (preds_keep, preds_removed) =
        List.partition (not o String.isSuffix pred_suffix o
                        fst o bir_envSyntax.dest_BVar_string)
                       preds;

      (* notice: rely on tidy up state function for stale values *)
    in
      SYST_update_pred preds_keep syst
    end;

(* primitives for branching states based on a boolean condition expression *)
  fun state_branch str_prefix cnd f_bt f_bf syst =
    let
      val bv_str = str_prefix ^ "_cnd";

      val debugOn = false;

      val systs1 = (f_bt o state_add_pred bv_str cnd) syst;
      val systs2 = (f_bf o state_add_pred bv_str (bslSyntax.bnot cnd)) syst;
    in
      if not debugOn then
        systs1@systs2
      else
        systs1
    end;

  fun state_branch_simp str_prefix cnd f_bt f_bf syst =
      state_branch str_prefix cnd (fn s => [f_bt s]) (fn s => [f_bf s]) syst;

end (* outermost local *)

end (* struct *)
