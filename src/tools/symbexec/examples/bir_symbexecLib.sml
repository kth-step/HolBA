structure bir_symbexecLib =
struct

datatype symb_value =
    SymbValBE of term
  | SymbValRange of (term * term);

datatype symb_state =
  SymbState of {
      SYST_env    : (term, symb_value) Redblackmap.dict,
      SYST_pred   : term list,
      SYST_pc     : term,
      SYST_status : term,
      SYST_obss   : term list
    };

fun SYST_get_env (SymbState systr) =
  #SYST_env systr;
fun SYST_get_pred (SymbState systr) =
  #SYST_pred systr;
fun SYST_get_pc (SymbState systr) =
  #SYST_pc systr;
fun SYST_get_status (SymbState systr) =
  #SYST_status systr;
fun SYST_get_obss (SymbState systr) =
  #SYST_obss systr;

fun SYST_update_env env' (SymbState systr) =
  SymbState {SYST_env    = env',
             SYST_pred   = #SYST_pred systr,
             SYST_pc     = #SYST_pc systr,
             SYST_status = #SYST_status systr,
             SYST_obss   = #SYST_obss systr };
fun SYST_update_pred pred' (SymbState systr) =
  SymbState {SYST_env    = #SYST_env systr,
             SYST_pred   = pred',
             SYST_pc     = #SYST_pc systr,
             SYST_status = #SYST_status systr,
             SYST_obss   = #SYST_obss systr };
fun SYST_update_pc pc' (SymbState systr) =
  SymbState {SYST_env    = #SYST_env systr,
             SYST_pred   = #SYST_pred systr,
             SYST_pc     = pc',
             SYST_status = #SYST_status systr,
             SYST_obss   = #SYST_obss systr };
fun SYST_update_status status' (SymbState systr) =
  SymbState {SYST_env    = #SYST_env systr,
             SYST_pred   = #SYST_pred systr,
             SYST_pc     = #SYST_pc systr,
             SYST_status = status',
             SYST_obss   = #SYST_obss systr };
fun SYST_update_obss obss' (SymbState systr) =
  SymbState {SYST_env    = #SYST_env systr,
             SYST_pred   = #SYST_pred systr,
             SYST_pc     = #SYST_pc systr,
             SYST_status = #SYST_status systr,
             SYST_obss   = obss' };

fun SYST_mk env pred pc status obss =
  SymbState {SYST_env    = env,
             SYST_pred   = pred,
             SYST_pc     = pc,
             SYST_status = status,
             SYST_obss   = obss };


local
open bir_envSyntax;
open bir_expSyntax;
val freshvarcounter_ = ref (0:int);
fun get_fresh_var_counter () =
  let val i = !freshvarcounter_; in
  (freshvarcounter_ := i + 1; i) end;
in
  fun get_fresh_var bv =
    let
      val (s, bty) = dest_BVar_string bv;
      val new_s = "fr_" ^ (Int.toString (get_fresh_var_counter ())) ^ "_" ^ s;
    in
      ((s, bty), (new_s, bty), (mk_BExp_Den o mk_BVar_string) (new_s, bty))
    end;

  fun init_exp_from_bvar bv =
    let
      val (name, bty) = dest_BVar_string bv;
    in
      ((name, bty), (mk_BExp_Den o mk_BVar_string) ("sy_" ^ name, bty))
    end;
end

local
  open bir_envSyntax;
in
  (*
  val t = hd prog_vars;
  *)
  fun init_state lbl_tm prog_vars =
    let
      val initsymblist = List.map init_exp_from_bvar prog_vars;
      val init_countw = (("countw", ``BType_Imm Bit64``), SymbValBE ``BExp_Const (Imm64 0w)``);
      val initenvlist = List.map (fn (a,b) => (mk_BVar_string a,b)) [init_countw];
    in
      SYST_mk (Redblackmap.fromList Term.compare initenvlist)
              []
              lbl_tm
              ``BST_Running``
              []
    end;
end

local
  open bir_constpropLib;
  open bir_envSyntax;
in (* local *)
(*
val syst = init_state prog_vars;
val SymbState systr = syst;
val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
val (bv, be) = dest_BStmt_Assign s
*)
fun update_state syst (bv, be) =
  let
    val (sear, repl, bv_fresh_e) = (get_fresh_var) bv;

    val old_env = SYST_get_env syst;
    val elem = (valOf o Redblackmap.peek) (old_env, mk_BVar_string sear)
(*
               handle Option => raise ERR "update_state" ("couldn't find searched variable: " ^ (fst sear));
*)
               handle Option => (SymbValBE o snd o init_exp_from_bvar) bv;

    val new_assignments =
      [(mk_BVar_string sear, SymbValBE be),
       (mk_BVar_string repl, elem)];

    val new_env = Redblackmap.insertList (old_env, new_assignments);

    fun subst_exp_ e = subst_exp (bv, bv_fresh_e, e);
    val new_env_subst = Redblackmap.map (fn (_, symbv) =>
            case symbv of
               SymbValBE e  => SymbValBE (subst_exp_ e)
             | _ => raise ERR "update_state" "unhandled symbolic value type") new_env;

    val old_pred_conjs = SYST_get_pred syst;
    val pred_conjs_subst = List.map subst_exp_ old_pred_conjs;
  in
    (SYST_update_pred pred_conjs_subst o
     SYST_update_env  new_env_subst
    ) syst
  end;

(*
val SymbState systr = update_state (SymbState systr) (bv, be);
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
      [update_state syst (dest_BStmt_Assign s)]
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

    val syst1   =
      (SYST_update_pred ((cnd)::(SYST_get_pred syst)) o
       SYST_update_pc   tgt1
      ) syst;
    val syst2   =
      (SYST_update_pred ((bslSyntax.bnot cnd)::(SYST_get_pred syst)) o
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
  open bir_envSyntax;
  open bir_smtLib;
in (* local *)
fun check_feasible syst =
  let
    val pred = SYST_get_pred syst;
    val env  = SYST_get_env  syst;
    val envl = Redblackmap.listItems env;

    (* memory accesses should not end up here hopefully, ignore this to begin with *)

    (* start with no variable and no assertions *)
    val vars    = Redblackset.empty smtlib_vars_compare;
    val asserts = [];

    fun proc_preds (vars, asserts) pred =
      List.foldr (fn (exp, (vl1,al)) =>
        let val (_,vl2,a) = bexp_to_smtlib [] vl1 exp in
          (vl2, a::al)
        end) (vars, asserts) pred;

    (* process the predicate *)
    val (vars, asserts) = proc_preds (vars, asserts) pred;

(*
val (bv_comp,exp) = hd envl;
*)
    (* process the environment *)
    val (vars, asserts) = proc_preds (vars, asserts)
                                     (List.map (fn (bv,symbv) =>
      case symbv of
          SymbValBE exp =>
            ``BExp_BinPred BIExp_Equal (BExp_Den ^bv) ^exp``
        | _ => raise ERR "check_feasible" "cannot handle symbolic value type"
    ) envl);

    val result = querysmt bir_smtLib_z3_prelude vars asserts;

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "check_feasible" "smt solver couldn't determine feasibility"
  in
    result <> BirSmtUnsat
  end;
end (* local *)

end (* struct *)
