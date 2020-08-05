structure bir_symbexecLib =
struct

datatype symb_value =
    SymbValBE    of (term * term Redblackset.set)
  | SymbValRange of (term * term)
                    (* TODO: generalize this *)
                    (* memory layout: flash, globals, stack;
                                      start and size of middle portion (globals) *)
  | SymbValMem   of (((Arbnum.num -> Arbnum.num) * term * term) * (Arbnum.num * Arbnum.num));

datatype symb_state =
  SymbState of {
      SYST_pc     : term,
      SYST_env    : (term, term) Redblackmap.dict,
      SYST_status : term,
      (* symbolic observation list: id, condition, value list, aggregation function *)
      SYST_obss   : (Arbnum.num * term * term list * term) list,
      (* path condition conjuncts *)
      SYST_pred   : term list,
      (* abstracted symbolic values for some "fresh" variables *)
      SYST_vals   : (term, symb_value) Redblackmap.dict
    };

val symbvalbe_dep_empty = Redblackset.empty Term.compare;

fun SYST_get_pc     (SymbState systr) =
  #SYST_pc systr;
fun SYST_get_env    (SymbState systr) =
  #SYST_env systr;
fun SYST_get_status (SymbState systr) =
  #SYST_status systr;
fun SYST_get_obss   (SymbState systr) =
  #SYST_obss systr;
fun SYST_get_pred   (SymbState systr) =
  #SYST_pred systr;
fun SYST_get_vals   (SymbState systr) =
  #SYST_vals systr;

fun SYST_mk pc env status obss pred vals =
  SymbState {SYST_pc     = pc,
             SYST_env    = env,
             SYST_status = status,
             SYST_obss   = obss,
             SYST_pred   = pred,
             SYST_vals   = vals };

fun SYST_update_pc pc' (SymbState systr) =
  SYST_mk (pc')
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_env env' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (env')
          (#SYST_status systr)
          (#SYST_obss   systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_status status' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (status')
          (#SYST_obss   systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_obss obss' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (obss')
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_pred pred' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
          (pred')
          (#SYST_vals   systr);
fun SYST_update_vals vals' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
          (#SYST_pred   systr)
          (vals');



local
  open bir_envSyntax;
  open bir_expSyntax;
  val freshvarcounter_ = ref (0:int);
  fun get_fresh_var_counter () =
    let val i = !freshvarcounter_; in
    (freshvarcounter_ := i + 1; i) end;
in
  fun get_bvar_fresh bv =
    let
      val (s, bty) = dest_BVar_string bv;
      val new_s = "fr_" ^ (Int.toString (get_fresh_var_counter ())) ^ "_" ^ s;
    in
      mk_BVar_string (new_s, bty)
    end;

  fun get_bvar_init bv =
    let
      val (s, bty) = dest_BVar_string bv;
      val new_s = "sy_" ^ s;
    in
      mk_BVar_string (new_s, bty)
    end;

  fun is_bvar_init bv =
    let
      val (s, _) = dest_BVar_string bv;
    in
      String.isPrefix "sy_" s
    end;
end

local
  open bir_envSyntax;
in
  fun init_state lbl_tm pred_conjs prog_vars_0 =
    let
(*
      val prog_vars_1      = List.map (snd o dest_eq o concl o EVAL) prog_vars_0;
*)
      val prog_vars_1      = prog_vars_0;
      val prog_vars        = List.filter ((fn x => x <> "countw") o fst o dest_BVar_string) prog_vars_1;
      val envlist_progvars = List.map (fn bv => (bv, get_bvar_init bv)) prog_vars;

      val countw_bv       = mk_BVar_string ("countw", ``BType_Imm Bit64``);
      val countw_bv_fresh = get_bvar_fresh countw_bv;
      val countw_exp_init = SymbValBE (``BExp_Const (Imm64 0w)``, symbvalbe_dep_empty);

      val envlist_init  = [(countw_bv, countw_bv_fresh)]@envlist_progvars;
      val varslist_init = [(countw_bv_fresh, countw_exp_init)];

      (* TODO: process pred_conjs with substitutions for initial variable names *)
    in
      SYST_mk lbl_tm
              (Redblackmap.fromList Term.compare envlist_init)
              ``BST_Running``
              []
              pred_conjs
              (Redblackmap.fromList Term.compare varslist_init)
    end;
end

local
  open bir_constpropLib;
  open bir_envSyntax;
  open bir_expSyntax;
  open bir_exp_helperLib;
in (* local *)

  fun subst_fun env (bev, (e, vars)) =
    let
      val bv_ofvars = (valOf o Redblackmap.peek) (env, bev)
                      handle Option =>
                      raise ERR "subst_fun"
                                ("couldn't find state variable: " ^ (term_to_string bev));
    in
      (subst_exp (bev, mk_BExp_Den bv_ofvars, e),
       bv_ofvars::vars)
    end;

  fun compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    let
      fun find_symbval bv = if is_bvar_init bv then (SymbValBE (F, symbvalbe_dep_empty)) else
                            (valOf o Redblackmap.peek) (vals, bv)
                            handle Option =>
                            raise ERR "compute_val_and_resolve_deps"
                                      ("couldn't find symbolic value variable: " ^ (term_to_string bv));
      fun find_deps bv = case find_symbval bv of
                            SymbValBE (_,deps) => deps
                          | _ => raise ERR "compute_val_and_resolve_deps"
                                           ("expect bir expression for variable: " ^ (term_to_string bv));

      val deps_l2 = List.foldr (Redblackset.union)
                               symbvalbe_dep_empty
                               (List.map find_deps besubst_vars);
      val deps = Redblackset.addList(deps_l2, besubst_vars);
      val be_new_val = SymbValBE (besubst, deps);
    in
      be_new_val
    end;

  fun insert_valbe bv_fr be syst =
    let
      val env  = SYST_get_env  syst;
      val vals = SYST_get_vals syst;

      val be_vars = get_birexp_vars be;
      (* TODO: this is a quickfix, should be handled in bir smtlib exporter: probably together with all other syntactic sugar!!!! *)
      val be_ = (snd o dest_eq o concl o REWRITE_CONV [bir_bool_expTheory.bir_exp_false_def, bir_bool_expTheory.bir_exp_true_def]) be
                handle UNCHANGED => be;
      val besubst_with_vars = List.foldr (subst_fun env) (be_, []) be_vars;

      val be_new_val = compute_val_and_resolve_deps vals besubst_with_vars;

      val vals' = Redblackmap.insert (vals, bv_fr, be_new_val);
    in
      (SYST_update_vals vals') syst
    end;

  (*
  val syst = init_state prog_vars;
  val SymbState systr = syst;
  val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
  val (bv, be) = dest_BStmt_Assign s
  *)
  fun update_state (bv, be) syst =
    if is_BExp_IfThenElse be then
      let
        val (cnd, be1, be2) = dest_BExp_IfThenElse be;

        val cnd_bv = bir_envSyntax.mk_BVar_string ("assign_cnd", ``BType_Bool``);
        val cnd_bv_1 = get_bvar_fresh cnd_bv;
        val cnd_bv_2 = get_bvar_fresh cnd_bv;
      in
        List.concat [
          (update_state (bv, be1) o
           SYST_update_pred ((cnd_bv_1)::(SYST_get_pred syst)) o
           insert_valbe cnd_bv_1 cnd
          ) syst
         ,
          (update_state (bv, be2) o
           SYST_update_pred ((cnd_bv_2)::(SYST_get_pred syst)) o
           insert_valbe cnd_bv_2 (bslSyntax.bnot cnd)
          ) syst
        ]
      end
    else
    let
      val env  = SYST_get_env  syst;

      val bv_fresh = (get_bvar_fresh) bv;

      val env'  = Redblackmap.insert (env, bv, bv_fresh);
    in
      [(SYST_update_env  env' o
        insert_valbe bv_fresh be
      ) syst]
    end;



(*
val SymbState systr = update_state (bv, be) (SymbState systr);
*)
(*
fun tidyup_state prog_vars syst =
  let
    val old_pred = SYST_get_pred syst;
    val old_env  = SYST_get_env  syst;

    val exps_env = List.map (fn (_, e) => e) old_env;

    fun subst_exp_test bv e = (subst_exp (bv, e, e) <> e);
    fun is_used ((s,bty), _) =
      let val bv = mk_BVar_string (s, bty)
          val exp_test = subst_exp_test bv in
      (((isSome o (List.find (fn x => x = bv))) prog_vars) orelse
       ((isSome o (List.find exp_test)) (Redblackmap.listItems exps_env)) orelse
       ((isSome o (List.find exp_test)) old_pred))
      end;

    val pred = old_pred;
    val env  = List.filter is_used old_env;
  in
    (SYST_update_pred pred o
     SYST_update_env  env
    ) syst
  end;
*)
end (* local *)

local
  open bir_programSyntax;
in (* local *)
fun symb_exec_stmt (s, syst) =
  (* TODO: no update if state is not running *)
  if is_BStmt_Assign s then
      update_state (dest_BStmt_Assign s) syst
  else if is_BStmt_Assert s then
      [syst] (* TODO: fix *)
  else if is_BStmt_Assume s then
      [syst] (* TODO: fix *)
  else if is_BStmt_Observe s then
      [syst] (* TODO: fix *)
  else raise ERR "symb_exec_stmt" "unknown statement type";
end (* local *)

local
  open bir_cfgLib;
  open binariesCfgLib;
in (* local *)
fun get_next_exec_sts lbl_tm est syst =
  let
    val (vs, _) = hol88Lib.match ``BStmt_Jmp (BLE_Label xyz)`` est;
    val tgt     = (fst o hd) vs;
  in
    [SYST_update_pc tgt syst]
    handle Empty =>
      raise ERR "get_next_exec_sts" ("unexpected 1 at " ^ (term_to_string lbl_tm))
  end
  handle HOL_ERR _ => (
  let
    val (vs, _) = hol88Lib.match ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)`` est;
    val cnd     = fst (List.nth (vs, 0));
    val tgt1    = fst (List.nth (vs, 1));
    val tgt2    = fst (List.nth (vs, 2));

    val cnd_bv = bir_envSyntax.mk_BVar_string ("cjmp_cnd", ``BType_Bool``);
    val cnd_bv_1 = get_bvar_fresh cnd_bv;
    val cnd_bv_2 = get_bvar_fresh cnd_bv;

    val syst1   =
      (SYST_update_pred ((cnd_bv_1)::(SYST_get_pred syst)) o
       insert_valbe cnd_bv_1 cnd o
       SYST_update_pc   tgt1
      ) syst;
    val syst2   =
      (SYST_update_pred ((cnd_bv_2)::(SYST_get_pred syst)) o
       insert_valbe cnd_bv_2 (bslSyntax.bnot cnd) o
       SYST_update_pc   tgt2
      ) syst;
  in
    [syst1, syst2]
    handle Empty =>
      raise ERR "get_next_exec_sts" ("unexpected 1 at " ^ (term_to_string lbl_tm))
  end
  handle HOL_ERR _ =>
    let
      val n       = find_node n_dict lbl_tm;
      val n_type  = #CFGN_type n;
      val _       = if cfg_nodetype_is_call n_type orelse n_type = CFGNT_Jump then () else
                      raise ERR "get_next_exec_sts" ("unexpected 2 at " ^ (term_to_string lbl_tm));

      val n_targets  = #CFGN_targets n;
      val lbl_tms = n_targets
    in
      List.map (fn t => SYST_update_pc t syst) lbl_tms
    end);
end (* local *)

fun simplify_state syst =
  let
(*    val syst2 = tidyup_state syst; *)

    (* implement search for possible simplifications, and simiplifications *)
    (* first approach: try to simplify memory loads by expanding variables successively, abort if it fails *)
    (* TODO: implement *)

    (* - derive constants from the state predicate (update both places to not loose information) *)
    (* - propagate constant variable assignments to expressions *)
    (* - constant propagation in expressions *)
    (* - tidy up state *)
    (* - resolve load and store pairs, use smt solver if reasoning arguments are needed *)
  in
    syst
  end;

local
  open bir_block_collectionLib;
in (* local *)
(*
val syst = init_state prog_vars;
*)
fun symb_exec_block bl_dict syst =
  let
    val lbl_tm = SYST_get_pc syst;

    val bl = (valOf o (lookup_block_dict bl_dict)) lbl_tm;
    val (_, stmts, est) = dest_bir_block bl;
    val s_tms = (fst o listSyntax.dest_list) stmts;

    val systs2 = List.foldl (fn (s, systs) => List.concat(List.map (fn x => symb_exec_stmt (s,x)) systs)) [syst] s_tms;

    (* generate list of states from end statement *)
    val systs = List.concat(List.map (get_next_exec_sts lbl_tm est) systs2);
  in
    List.map simplify_state systs
  end;

fun symb_exec_to_stop _       []                  _            acc = acc
  | symb_exec_to_stop bl_dict (exec_st::exec_sts) stop_lbl_tms acc =
      let
        val sts = symb_exec_block bl_dict exec_st;
        val (new_acc, new_exec_sts) =
              List.partition (fn (syst) => List.exists (fn x => (SYST_get_pc syst) = x) stop_lbl_tms) sts;
      in
        symb_exec_to_stop bl_dict (new_exec_sts@exec_sts) stop_lbl_tms (new_acc@acc)
      end;
end (* local *)

local
  open bir_expSyntax;
  open bir_envSyntax;
  open bir_smtLib;

  val BIExp_Equal_tm = ``BIExp_Equal``;

  fun proc_preds (vars, asserts) pred =
    List.foldr (fn (exp, (vl1,al)) =>
      let val (_,vl2,a) = bexp_to_smtlib [] vl1 exp in
        (vl2, a::al)
      end) (vars, asserts) pred;

  fun symbval_eq_to_bexp (bv, symbv) =
       case symbv of
          SymbValBE (exp,_) =>
            mk_BExp_BinPred (BIExp_Equal_tm, mk_BExp_Den bv, exp)
        | _ => raise ERR "symbval_eq_to_bexp" "cannot handle symbolic value type";

  fun collect_pred_expsdeps vals (bv, (exps, deps)) =
    let
      val symbv = (valOf o Redblackmap.peek) (vals, bv)
                  handle Option => raise ERR "collect_pred_expsdeps"
                                      ("couldn't fine symbolic value for " ^ (term_to_string bv));
      val (exp, deps_delta) =
       case symbv of
          SymbValBE x => x
        | _ => raise ERR "collect_pred_expsdeps" "cannot handle symbolic value type";
    in
      (exp::exps, Redblackset.union(deps_delta, deps))
    end;

in (* local *)

fun check_feasible syst =
  let
    val vals  = SYST_get_vals syst;
    val pred_bvl = SYST_get_pred syst;

    val (pred_conjs, pred_deps) =
      List.foldr (collect_pred_expsdeps vals) ([], symbvalbe_dep_empty) pred_bvl;

    val pred_depsl_ = Redblackset.listItems pred_deps;
    val pred_depsl = List.filter (not o is_bvar_init) pred_depsl_;

    val valsl = List.map (fn bv => (bv, (valOf o Redblackmap.peek) (vals, bv)
                                        handle Option =>
                                          raise ERR
                                                "check_feasible"
                                                ("couldn't fine symbolic value for " ^ (term_to_string bv))))
                         pred_depsl;
    val vals_eql =
      List.map symbval_eq_to_bexp valsl;

    (* memory accesses should not end up here (actually only SymbValBE should be relevant),
       ignore this detail for now *)

    (* start with no variable and no assertions *)
    val vars    = Redblackset.empty smtlib_vars_compare;
    val asserts = [];

    (* process the predicate conjuncts *)
    val (vars, asserts) = proc_preds (vars, asserts) pred_conjs;

    (* process the symbolic values *)
    val (vars, asserts) = proc_preds (vars, asserts) vals_eql;

    val result = querysmt bir_smtLib_z3_prelude vars asserts;

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "check_feasible" "smt solver couldn't determine feasibility"
  in
    result <> BirSmtUnsat
  end;
end (* local *)

end (* struct *)
