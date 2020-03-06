open HolKernel Parse

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;
open binariesCfgVizLib;

val entry_label = "imu_handler_pid_entry";

(*
fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")");
*)

(*
=================================================================================================
*)

(*
val _ = show_call_graph ();

val _ = show_cfg_fun true  ns entry_label;
val _ = show_cfg_fun true  ns "__aeabi_fmul";
val _ = show_cfg_fun false ns "__aeabi_fmul";
val _ = show_cfg_fun false ns "__aeabi_fdiv";

val _ = List.map (print_fun_pathstats false ns)
                 (List.filter (fn x => x <> "__aeabi_fdiv") symbs_sec_text);

val _ = print_dead_code ns entry_label;
*)

val name   = "motor_prep_input";
val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;

datatype symb_state =
  SymbState of {
      SYST_env  : ((string * term) * term) list,
      SYST_pred : term list
    };



open bir_envSyntax;
open bir_expSyntax;
open stringSyntax;
open bir_programSyntax;

local
val freshvarcounter_ = ref (0:int);
fun get_fresh_var_counter () =
  let val i = !freshvarcounter_; in
  (freshvarcounter_ := i + 1; i) end;
in
  fun get_fresh_var bv =
    let
      val (bn, bty) = dest_BVar bv;
      val s = fromHOLstring bn;
      val new_s = "fr_" ^ (Int.toString (get_fresh_var_counter ())) ^ "_" ^ s;
    in
      ((s, bty), (new_s, bty), (mk_BExp_Den o mk_BVar) (fromMLstring new_s, bty))
    end;

  fun init_exp_from_bvar bv =
    let
      val (bstr, bty) = dest_BVar bv;
      val name = fromHOLstring bstr;
    in
      ((name, bty), (mk_BExp_Den o mk_BVar) (fromMLstring("sy_" ^ name), bty))
    end;
end


(*
val t = hd prog_vars;
*)
fun init_state prog_vars =
  let
    val initsymblist = List.map init_exp_from_bvar prog_vars;
  in
    SymbState { SYST_pred = [],
                SYST_env  = [] }
  end;

open bir_exp_substitutionsSyntax;
(*
val syst = init_state prog_vars;
val SymbState systr = syst;
val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
val (bv, be) = dest_BStmt_Assign s
*)
val subst_exp = (snd o dest_eq o concl o EVAL o mk_bir_exp_subst1);
fun update_state (SymbState systr) (bv, be) =
  let
    val (sear, repl, bv_fresh_e) = get_fresh_var bv;

    fun match_sear s_ = (s_ = sear);
    val old_env_filt = List.filter (not o match_sear o fst) (#SYST_env systr);
    val elem = (valOf o List.find (match_sear o fst)) (#SYST_env systr)
(*
               handle Option => raise ERR "update_state" ("couldn't find searched variable: " ^ (fst sear));
*)
               handle Option => init_exp_from_bvar bv;

    val new_env = (sear, be)::(repl, snd elem)::old_env_filt;
    fun subst_exp_ e = subst_exp (bv, bv_fresh_e, e);
    val new_env_subst = List.map (fn (x, e) => (x, subst_exp_ e)) new_env;

    val old_pred_conjs = #SYST_pred systr;
    val pred_conjs_subst = List.map subst_exp_ old_pred_conjs;
  in
    SymbState { SYST_pred = pred_conjs_subst,
                SYST_env  = new_env_subst }
  end;

(*
val SymbState systr = update_state (SymbState systr) (bv, be);
*)
fun tidyup_state (SymbState systr) =
  let
    val old_pred = #SYST_pred systr;
    val old_env  = #SYST_env  systr;

    val exps_env = List.map (fn (_, e) => e) old_env;

    fun subst_exp_test bv e = (subst_exp (bv, e, e) <> e);
    fun is_used ((s,bty), _) =
      let val bv = mk_BVar (fromMLstring s, bty)
          val exp_test = subst_exp_test bv in
      (((isSome o (List.find (fn x => x = bv))) prog_vars) orelse
       ((isSome o (List.find exp_test)) exps_env) orelse
       ((isSome o (List.find exp_test)) old_pred))
      end;

    val pred = old_pred;
    val env  = List.filter is_used old_env;
  in
    SymbState { SYST_pred = pred,
                SYST_env  = env }
  end;


fun simplify_state (SymbState systr) =
  let
    (* implement search for possible simplifications, and simiplifications *)
    (* first approach: try to simplify memory loads by expanding variables successively, abort if it fails *)
    (* TODO: implement *)
  in
    (SymbState systr)
  end;




fun symb_exec_stmt (s, syst) =
  if is_BStmt_Assign s then
      update_state syst (dest_BStmt_Assign s)
  else if is_BStmt_Assert s orelse is_BStmt_Assume s orelse is_BStmt_Observe s then
    (* TODO: shortcut for now, needs smt solver interaction, and ignore observe *)
    syst
  else raise ERR "symb_exec_stmt" "unknown statement type";




(*
val syst = init_state prog_vars;
*)
fun symb_exec_block lbl_tm syst =
  let
    val bl = (valOf o prog_get_block_) lbl_tm;
    val (_, stmts, _) = dest_bir_block bl;
    val s_tms = (fst o listSyntax.dest_list) stmts;

    val syst2 = List.foldl symb_exec_stmt syst s_tms;
    val syst3 = tidyup_state syst2;

    (* TODO: generate list of states from end statement *)
  in
    syst3
  end;


fun check_satisfiability (SymbState systr) =
  let
    val pred = #SYST_pred systr;
    val env  = #SYST_env  systr;

    (* memory accesses should not end up here hopefully, ignore this to begin with *)

    (* TODO: implement *)
  in
     true
  end;


val syst  = init_state prog_vars;
val systs = symb_exec_block lbl_tm syst;
