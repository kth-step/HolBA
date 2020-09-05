structure bir_symbexec_compLib =
struct

local
  open bir_symbexec_stateLib;

  open bir_constpropLib;
  open bir_exp_helperLib;
  open bir_expSyntax;
in (* outermost local *)

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

  val bexpden_match_tm = bden ``x:bir_var_t``;
  fun lookup_mem_symbv vals symbv =
    case symbv of
       SymbValBE (t, _) => (
         let
           val (vs, _) = hol88Lib.match bexpden_match_tm t;
           val bv      = fst (List.nth (vs, 0));
         in
           find_bv_val "lookup_mem_symbv" vals bv
         end
         handle _ => raise ERR "lookup_mem_symbv" "SymbValBE didn't match bexpden"
        )
     | SymbValMem _ => symbv
     | _ => raise ERR "lookup_mem_symbv" "needs to be SymbValBE or SymbValMem";

  fun compute_val_try_mem compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    let
      val debugOn = false;

      fun debug_prints debugOn =
        let
          val _ = if not debugOn then () else
                  print_term besubst;
          val _ = if not debugOn then () else 
                  print "\n==========================================\n\n";
        in () end;
    in
      if is_BExp_Load besubst then
        let
          val _ = debug_prints debugOn;

          val (mem_tm, addr_tm, end_tm, sz_tm) = dest_BExp_Load besubst;
          val (addr, addr_deps) = process_addr "load" vals addr_tm;

          val mem_tm_resolve = compute_val_and_resolve_deps vals (mem_tm, besubst_vars);

          val _ = if not debugOn then () else
                  print_term sz_tm;
        in
          if true then NONE else raise ERR "compute_val_try" "load debugging"
        end
      else if is_BExp_Store besubst orelse is_BExp_Load besubst then
        let
          val _ = debug_prints debugOn;

          val (mem_tm, addr_tm, end_tm, val_tm) = dest_BExp_Store besubst;
          val (addr, addr_deps) = process_addr "store" vals addr_tm;

          val mem_symbv_resolve = compute_val_and_resolve_deps vals (mem_tm, besubst_vars);
(*
          val mem_symbv = lookup_mem_symbv vals mem_symbv_resolve;
          val _ = print ((symbv_to_string mem_symbv) ^ "\n\n");
*)

          val _ = if not debugOn then () else
                  print_term val_tm;
        in
          (*SOME mem_symbv*)
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

end (* outermost local *)

end (* struct *)
