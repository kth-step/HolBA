structure bir_symbexec_stepLib =
struct

local
  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
in

fun symb_exec_stmt_observe ((id_tm, cnd_tm, exps_tm, ofun_tm), syst) =
  let
    val _  = if numSyntax.is_numeral id_tm then () else
             raise ERR "symb_exec_stmt_observe" "the observation id has to be a numeral.";
    val id = numSyntax.dest_numeral id_tm;

    val (exp_tms,_) = listSyntax.dest_list exps_tm;

    val cnd_bv = bir_envSyntax.mk_BVar_string ("observe_cnd", ``BType_Bool``);

    fun fold_exp (exp_tm, (exp_bvs, insert_fun)) =
      let
        val exp_ty = ``BType_Bool``; (* TODO: fix this, it needs to use type checking *)
        val exp_bv = bir_envSyntax.mk_BVar_string ("observe_exp", exp_ty);
      in
        (exp_bv::exp_bvs, (insert_valbe exp_bv exp_tm) o insert_fun)
      end;
    val (exp_bvs, insert_fun) = List.foldr fold_exp ([],I) exp_tms; 

    val obs = (id, cnd_bv, exp_bvs, ofun_tm);
    val obss' = obs::(SYST_get_obss syst);
  in
    [(SYST_update_obss obss' o
      insert_fun o
      insert_valbe cnd_bv cnd_tm
      ) syst]
  end;

local
  open bir_programSyntax;
in (* local *)
  fun symb_exec_stmt (s, syst) =
    (* no update if state is not running *)
    if SYST_get_status syst <> BST_Running_tm then [syst]
    (* assignment *)
    else if is_BStmt_Assign s then
        update_state (dest_BStmt_Assign s) syst
    (* assert and assume *)
    else if is_BStmt_Assert s then
        branch_state_simp
           "assert"
           (dest_BStmt_Assert s)
           (I)
           (SYST_update_status BST_AssertionViolated_tm)
           syst
    else if is_BStmt_Assume s then
        branch_state_simp
           "assume"
           (dest_BStmt_Assume s)
           (I)
           (SYST_update_status BST_AssumptionViolated_tm)
           syst
    (* observations *)
    else if is_BStmt_Observe s then
        symb_exec_stmt_observe ((dest_BStmt_Observe s), syst)
    else raise ERR "symb_exec_stmt" ("unknown statement type for: " ^ (term_to_string s));
end (* local *)

local
  open bir_cfgLib;
in (* local *)
  fun symb_exec_endstmt n_dict lbl_tm est syst =
    (* no update if state is not running *)
    if SYST_get_status syst <> BST_Running_tm then [syst] else
    (* try to match direct jump *)
    let
      val (vs, _) = hol88Lib.match ``BStmt_Jmp (BLE_Label xyz)`` est;
      val tgt     = (fst o hd) vs;
    in
      [SYST_update_pc tgt syst]
    end
    handle HOL_ERR _ => (
    (* try to match direct branch *)
    let
      val (vs, _) = hol88Lib.match ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)`` est;
      val cnd     = fst (List.nth (vs, 0));
      val tgt1    = fst (List.nth (vs, 1));
      val tgt2    = fst (List.nth (vs, 2));

      (* see whether the latest addition to the path condition
         matches the unnegated or negated branch condition *)
      val pred = SYST_get_pred syst;
      val vals = SYST_get_vals syst;
      val last_pred_bv = hd pred
                      handle Empty => raise ERR "symb_exec_endstmt" "oh no, pred is empty!";
      val last_pred_symbv = find_val vals last_pred_bv "symb_exec_endstmt";
      val last_pred_exp =
         case last_pred_symbv of
            SymbValBE (x,_) => x
          | _ => raise ERR "symb_exec_endstmt" "cannot handle symbolic value type for last pred exp";

      (* get branch condition *)
      val cnd_exp =
         case compute_valbe cnd syst of
            SymbValBE (x,_) => x
          | _ => raise ERR "symb_exec_endstmt" "cannot handle symbolic value type for conditions";
    in
      (* does unnegated condition match? *)
      if cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt1
         ) syst]
      (* does negated condition match? *)
      else if bslSyntax.bnot cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt2
         ) syst]
      (* no match *)
      else
      branch_state_simp
         "cjmp"
         cnd
         (SYST_update_pc tgt1)
         (SYST_update_pc tgt2)
         syst
    end
    (* no match, then we have some indirection and need to use cfg *)
    handle HOL_ERR _ =>
      let
        val n:cfg_node = binariesCfgLib.find_node n_dict lbl_tm;
        val n_type  = #CFGN_type n;
        val _       = if cfg_nodetype_is_call n_type orelse n_type = CFGNT_Jump then () else
                        raise ERR "symb_exec_endstmt" ("unexpected 2 at " ^ (term_to_string lbl_tm));

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
  fun symb_exec_block cfb n_dict bl_dict syst =
    let
      val lbl_tm = SYST_get_pc syst;

      val bl = (valOf o (lookup_block_dict bl_dict)) lbl_tm;
      val (_, stmts, est) = dest_bir_block bl;
      val s_tms = (fst o listSyntax.dest_list) stmts;

      val systs2 = List.foldl (fn (s, systs) => List.concat(List.map (fn x => symb_exec_stmt (s,x)) systs)) [syst] s_tms;

      (* generate list of states from end statement *)
      val systs = List.concat(List.map (symb_exec_endstmt n_dict lbl_tm est) systs2);
      val systs_simplified = List.map simplify_state systs;
      val systs_filtered = if cfb andalso length systs_simplified > 1 then
                             List.filter check_feasible systs_simplified
                           else
                             systs_simplified;
    in
      systs_filtered
    end;

  fun symb_exec_to_stop cfb _      _       []                  _            acc = acc
    | symb_exec_to_stop cfb n_dict bl_dict (exec_st::exec_sts) stop_lbl_tms acc =
        let
          fun state_stops syst =
            (List.exists (fn x => (SYST_get_pc syst) = x) stop_lbl_tms) orelse
            SYST_get_status syst <> BST_Running_tm;

          val sts = symb_exec_block cfb n_dict bl_dict exec_st;
          val (new_acc, new_exec_sts) = List.partition state_stops sts;
        in
          symb_exec_to_stop cfb n_dict bl_dict (new_exec_sts@exec_sts) stop_lbl_tms (new_acc@acc)
        end;
end (* local *)

end

end (* struct *)
