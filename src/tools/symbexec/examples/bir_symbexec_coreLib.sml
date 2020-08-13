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

  fun subst_fun env (bev, (e, vars)) =
    let
      val bv_ofvars = find_bv_val "subst_fun" env bev;
    in
      (subst_exp (bev, mk_BExp_Den bv_ofvars, e),
       bv_ofvars::vars)
    end;

  fun compute_val_try vals (besubst, besubst_vars) deps_l2 =
    let
      val all_deps_const = List.all (fn bv =>
             (not o is_bvar_init) bv andalso
             (case find_bv_val "compute_val_try" vals bv of
                 SymbValBE (exp,_) => is_BExp_Const exp
               | _ => false)
           ) besubst_vars;
    in
      if all_deps_const then
        if List.null besubst_vars then NONE else
        let
          val _ = if Redblackset.isEmpty deps_l2 then () else
                  raise ERR "compute_val_try" "deps_l2 is not empty. Unexpected here.";

          fun subst_fun_symbvalbe vals (bv_dep, e) =
            let
              val symbv_dep = find_bv_val "compute_val_try" vals bv_dep;
              val exp = case symbv_dep of
                           SymbValBE (exp,_) => exp
                         | _ => raise ERR "compute_val_and_resolve_deps" "cannot happen";
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

in (* local *)
  fun compute_valbe be syst =
    let
      val env  = SYST_get_env  syst;
      val vals = SYST_get_vals syst;

      val be_vars = get_birexp_vars be;
      (* TODO: this is a quickfix, should be handled in bir smtlib exporter: probably together with all other syntactic sugar!!!! *)
      val be_ = (snd o dest_eq o concl o REWRITE_CONV [bir_bool_expTheory.bir_exp_false_def, bir_bool_expTheory.bir_exp_true_def]) be
                handle UNCHANGED => be;
      val besubst_with_vars = List.foldr (subst_fun env) (be_, []) be_vars;
    in
      compute_val_and_resolve_deps vals besubst_with_vars
    end;
end (* local *)


(* primitive to compute expression and store result using free variable *)
  fun state_insert_symbval_from_be bv_fr be syst =
      insert_symbval bv_fr (compute_valbe be syst) syst;

(* primitive to carry out assignment *)
  fun state_assign_bv bv be syst =
    let
      val bv_fresh = (get_bvar_fresh) bv;
    in
      [(update_envvar bv bv_fresh o
        state_insert_symbval_from_be bv_fresh be
      ) syst]
    end;

(* primitives for adding conjuncts to the path predicate *)
local
  fun state_add_pred bv_str pred syst =
    let
      val bv = bir_envSyntax.mk_BVar_string (bv_str, ``BType_Bool``);
      val bv_fresh = get_bvar_fresh bv;
    in
      (SYST_update_pred ((bv_fresh)::(SYST_get_pred syst)) o
       state_insert_symbval_from_be bv_fresh pred
      ) syst
    end;
in (* local *)
  fun state_add_preds bv_str preds syst =
    List.foldr (fn (pred, syst_) => state_add_pred bv_str pred syst_) syst preds;
end (* local *)

(* primitives for branching states based on a boolean condition expression *)
  fun state_branch str_prefix cnd f_bt f_bf syst =
    let
        val cnd_bv = bir_envSyntax.mk_BVar_string (str_prefix ^ "_cnd", ``BType_Bool``);
        val cnd_bv_t = get_bvar_fresh cnd_bv;
        val cnd_bv_f = get_bvar_fresh cnd_bv;
    in
        List.concat [
          (f_bt o
           SYST_update_pred ((cnd_bv_t)::(SYST_get_pred syst)) o
           state_insert_symbval_from_be cnd_bv_t cnd
          ) syst
         ,
          (f_bf o
           SYST_update_pred ((cnd_bv_f)::(SYST_get_pred syst)) o
           state_insert_symbval_from_be cnd_bv_f (bslSyntax.bnot cnd)
          ) syst
        ]
    end;

  fun state_branch_simp str_prefix cnd f_bt f_bf syst =
      state_branch str_prefix cnd (fn s => [f_bt s]) (fn s => [f_bf s]) syst

end (* outermost local *)

end (* struct *)
