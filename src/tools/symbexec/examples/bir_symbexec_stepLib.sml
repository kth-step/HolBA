structure bir_symbexec_stepLib =
struct

local
  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
in

local
  open bir_programSyntax;
in (* local *)
  fun symb_exec_stmt (s, syst) =
    (* no update if state is not running *)
    if SYST_get_status syst <> ``BST_Running`` then [syst]
    (* assignment *)
    else if is_BStmt_Assign s then
        update_state (dest_BStmt_Assign s) syst
    (* assert and assume *)
    else if is_BStmt_Assert s then
        [syst] (* TODO: fix *)
    else if is_BStmt_Assume s then
        [syst] (* TODO: fix *)
    (* observations *)
    else if is_BStmt_Observe s then
        [syst] (* TODO: fix *)
    else raise ERR "symb_exec_stmt" ("unknown statement type for: " ^ (term_to_string s));
end (* local *)

local
  open bir_cfgLib;
  open binariesCfgLib;
in (* local *)
  fun get_next_exec_sts lbl_tm est syst =
    (* TODO: rename function maybe to capture connection to end statement/cfg? *)
    (* TODO: no update if state is not running *)
    let
      val (vs, _) = hol88Lib.match ``BStmt_Jmp (BLE_Label xyz)`` est;
      val tgt     = (fst o hd) vs;
    in
      [SYST_update_pc tgt syst]
    end
    handle HOL_ERR _ => (
    let
      val (vs, _) = hol88Lib.match ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)`` est;
      val cnd     = fst (List.nth (vs, 0));
      val tgt1    = fst (List.nth (vs, 1));
      val tgt2    = fst (List.nth (vs, 2));

      val cnd_valbe = compute_valbe cnd syst;
      val (cnd_exp, cnd_deps) =
         case cnd_valbe of
            SymbValBE x => x
          | _ => raise ERR "get_next_exec_sts" "cannot handle symbolic value type for conditions";

      val pred = SYST_get_pred syst;
      val vals = SYST_get_vals syst;
      val last_pred_bv = hd pred
                      handle Empty => raise ERR "get_next_exec_sts" "oh no, pred is empty!";
      val last_pred_symbv = find_val vals last_pred_bv "get_next_exec_sts";
      val last_pred_exp =
         case last_pred_symbv of
            SymbValBE (x,_) => x
          | _ => raise ERR "get_next_exec_sts" "cannot handle symbolic value type for last pred exp";
    in
      if cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt1
         ) syst]
      else if bslSyntax.bnot cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt2
         ) syst]
      else
      branch_state_simp
         "cjmp"
         cnd
         (SYST_update_pc tgt1)
         (SYST_update_pc tgt2)
         syst
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
      val systs_simplified = List.map simplify_state systs;
      val systs_filtered = if length systs_simplified > 1 then
                             List.filter check_feasible systs_simplified
                           else
                             systs_simplified;
    in
      systs_filtered
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

end

end (* struct *)
