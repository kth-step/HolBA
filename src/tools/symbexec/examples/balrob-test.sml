open HolKernel Parse

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;
open binariesCfgVizLib;

open bir_smtLib;

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

val bir_exp_is_const_def = Define `
  (bir_exp_is_const (BExp_Const n) = T) /\
  (bir_exp_is_const _              = F)
`;

val bir_exp_is_mem_const_def = Define `
  (bir_exp_is_mem_const (BExp_MemConst aty vty mmap) = T) /\
  (bir_exp_is_mem_const _              = F)
`;

val bir_val_to_const_def = Define `
  (bir_val_to_const (BVal_Imm n) = (BExp_Const n)) /\
  (bir_val_to_const (BVal_Mem aty vty mmap) = (BExp_MemConst aty vty mmap))
`;

val bir_exp_eval_consts_def = Define `
  bir_exp_eval_consts e = bir_val_to_const(THE (bir_eval_exp e (BEnv (K NONE))))
`;


val bir_exp_const_prop_def = Define `
  (bir_exp_const_prop (BExp_Const n) = (BExp_Const n)) /\

  (bir_exp_const_prop (BExp_MemConst aty vty mmap) = (BExp_MemConst aty vty mmap)) /\

  (bir_exp_const_prop (BExp_Den v) = (BExp_Den v)) /\

  (bir_exp_const_prop (BExp_Cast ct e ty) = (
     let e_cp = (bir_exp_const_prop e); in
     if (bir_exp_is_const e_cp) then
       bir_exp_eval_consts (BExp_Cast ct e_cp ty)
     else
       (BExp_Cast ct e_cp ty)
  )) /\

  (bir_exp_const_prop (BExp_UnaryExp et e) = (
     let e_cp = (bir_exp_const_prop e); in
     if (bir_exp_is_const e_cp) then
       bir_exp_eval_consts (BExp_UnaryExp et e_cp)
     else
       (BExp_UnaryExp et e_cp)
  )) /\

  (bir_exp_const_prop (BExp_BinExp et e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_BinExp et e1_cp e2_cp)
     else
       (BExp_BinExp et e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_BinPred pt e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_BinPred pt e1_cp e2_cp)
     else
       (BExp_BinPred pt e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_MemEq e1 e2) = (
     let e1_cp = (bir_exp_const_prop e1);
         e2_cp = (bir_exp_const_prop e2); in
     if (EVERY bir_exp_is_const [e1_cp; e2_cp]) then
       bir_exp_eval_consts (BExp_MemEq e1_cp e2_cp)
     else
       (BExp_MemEq e1_cp e2_cp)
  )) /\

  (bir_exp_const_prop (BExp_IfThenElse c et ef) = (
     let c_cp  = (bir_exp_const_prop c);
         et_cp = (bir_exp_const_prop et);
         ef_cp = (bir_exp_const_prop ef); in
     if (EVERY bir_exp_is_const [c_cp; et_cp; ef_cp]) then
       bir_exp_eval_consts (BExp_IfThenElse c_cp et_cp ef_cp)
     else
       (BExp_IfThenElse c_cp et_cp ef_cp)
  )) /\

  (bir_exp_const_prop (BExp_Load mem_e a_e en ty) = (
     let mem_e_cp = (bir_exp_const_prop mem_e);
         a_e_cp   = (bir_exp_const_prop a_e); in
     if (EVERY bir_exp_is_const [mem_e_cp; a_e_cp]) then
       bir_exp_eval_consts (BExp_Load mem_e_cp a_e_cp en ty)
     else
       (BExp_Load mem_e_cp a_e_cp en ty)
  )) /\

  (bir_exp_const_prop (BExp_Store mem_e a_e en v_e) = (
     let mem_e_cp = (bir_exp_const_prop mem_e);
         a_e_cp   = (bir_exp_const_prop a_e);
         v_e_cp   = (bir_exp_const_prop v_e); in
     if (EVERY bir_exp_is_const [mem_e_cp; a_e_cp; v_e_cp]) then
       bir_exp_eval_consts (BExp_Store mem_e_cp a_e_cp en v_e_cp)
     else
       (BExp_Store mem_e_cp a_e_cp en v_e_cp)
  ))
`;

fun mk_bir_exp_const_prop t = ``bir_exp_const_prop ^t``;


(*
val t1 = ``
(BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "fr_0_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 3w)))
``
val t2 = ``
(BExp_BinExp BIExp_Plus
             (BExp_Const (Imm64 19w))
             (BExp_Const (Imm64 3w)))
``
val t = ``
(BExp_BinExp BIExp_Plus
             ^t1
             ^t2)
``

(EVAL o mk_bir_exp_const_prop) t
*)

(*
=================================================================================================
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
    val init_countw = (("countw", ``BType_Imm Bit64``), ``BExp_Const (Imm64 0w)``);
  in
    SymbState { SYST_pred = [],
                SYST_env  = [init_countw] }
  end;

open bir_exp_substitutionsSyntax;
(*
val syst = init_state prog_vars;
val SymbState systr = syst;
val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
val (bv, be) = dest_BStmt_Assign s
*)
val subst_exp = (snd o dest_eq o concl o EVAL o mk_bir_exp_const_prop o mk_bir_exp_subst1);
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

    (* - derive constants from the state predicate (update both places to not loose information) *)
    (* - propagate constant variable assignments to expressions *)
    (* - constant propagation in expressions *)
    (* - tidy up state *)
    (* - resolve load and store pairs, use smt solver if reasoning arguments are needed *)
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



fun get_next_exec_sts lbl_tm est syst =
  let
    val (vs, _) = hol88Lib.match ``BStmt_Jmp (BLE_Label xyz)`` est;
    val tgt     = (fst o hd) vs;
  in
    [(tgt, syst)]
    handle Empty =>
      raise ERR "get_next_exec_sts" ("unexpected 1 at " ^ (term_to_string lbl_tm))
  end
  handle HOL_ERR _ => (
  let
    val (vs, _) = hol88Lib.match ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)`` est;
    val cnd     = fst (List.nth (vs, 0));
    val tgt1    = fst (List.nth (vs, 1));
    val tgt2    = fst (List.nth (vs, 2));

    val SymbState systr = syst;
    val syst1   = SymbState { SYST_env = #SYST_env systr, SYST_pred = (cnd)::(#SYST_pred systr)};
    val syst2   = SymbState { SYST_env = #SYST_env systr, SYST_pred = (bslSyntax.bnot cnd)::(#SYST_pred systr)};
  in
    [(tgt1, syst1), (tgt2, syst2)]
    handle Empty =>
      raise ERR "get_next_exec_sts" ("unexpected 1 at " ^ (term_to_string lbl_tm))
  end
  handle HOL_ERR _ =>
    let
      val n       = find_node ns lbl_tm;
      val n_type  = #CFGN_type n;
      val _       = if n_type = CFGNT_Call orelse n_type = CFGNT_Jump then () else
                      raise ERR "get_next_exec_sts" ("unexpected 2 at " ^ (term_to_string lbl_tm));

      val n_goto  = #CFGN_goto n;
      val lbl_tms = (valOf o cfg_targets_to_lbl_tms) n_goto
            handle Option => raise ERR "get_next_exec_sts" ("error for " ^ (term_to_string lbl_tm));
    in
      List.map (fn t => (t, syst)) lbl_tms
    end);

(*
val syst = init_state prog_vars;
*)
fun symb_exec_block (lbl_tm, syst) =
  let
    val bl = (valOf o prog_get_block_) lbl_tm;
    val (_, stmts, est) = dest_bir_block bl;
    val s_tms = (fst o listSyntax.dest_list) stmts;

    val syst2 = List.foldl symb_exec_stmt syst s_tms;
    val syst3 = tidyup_state syst2;
    (* TODO: apply simplifications and tidy up (move this there) AFTER generating the next states,
                use function "simplify_state" *)
  in
    (* generate list of states from end statement *)
    (* TODO: move program counter into symbolic state record,
               we execute block by block, no block indexes, just labels *)
    get_next_exec_sts lbl_tm est syst3
  end;


fun symb_exec_to_stop []                  _            acc = acc
  | symb_exec_to_stop (exec_st::exec_sts) stop_lbl_tms acc =
      let
        val sts = symb_exec_block exec_st;
        val (new_acc, new_exec_sts) =
              List.partition (fn (t, _) => List.exists (fn x => x = t) stop_lbl_tms) sts;
      in
        symb_exec_to_stop (new_exec_sts@exec_sts) stop_lbl_tms (new_acc@acc)
      end;


fun check_feasible (SymbState systr) =
  let
    val pred = #SYST_pred systr;
    val env  = #SYST_env  systr;

    (* memory accesses should not end up here hopefully, ignore this to begin with *)

    (* start with no variable and no assertions *)
    val vars    = Redblackset.empty smtlib_vars_compare;
    val asserts = [];

    fun proc_preds (vars, asserts) pred =
      List.foldr (fn (exp, (vl1,al)) =>
        let val (vl2,a) = bexp_to_smtlib vl1 exp in
          (vl2, a::asserts)
        end) (vars, asserts) pred;

    (* process the predicate *)
    val (vars, asserts) = proc_preds (vars, asserts) pred;

(*
val (bv_comp,exp) = hd env;
*)
    (* process the environment *)
    val (vars, asserts) = proc_preds (vars, asserts)
                                     (List.map (fn (bv_comp,exp) =>
      ``BExp_BinPred BIExp_Equal (BExp_Den ^(mk_BVar_string bv_comp)) ^exp``
    ) env);

    val result = querysmt vars asserts;

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "check_feasible" "smt solver couldn't determine feasibility"
  in
    result <> BirSmtUnsat
  end;


val stop_lbl_tms = (List.map #CFGN_lbl_tm o
                    List.filter (fn n => node_to_rel_symbol n = name andalso
                                         #CFGN_type n = CFGNT_Return)
                   ) ns;

(* stop at first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb08w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb22w)``];
(* just check first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb22w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb24w)``, ``BL_Address (Imm32 0xb2aw)``];

val syst  = init_state prog_vars;
val exec_st = (lbl_tm, syst);

(*
val syst_new = symb_exec_block exec_st;
*)

(* TODO: speed up, probably by implementing a lookup map for "ns" *)
val exec_sts = symb_exec_to_stop [exec_st] stop_lbl_tms [];
(*
length exec_sts

val (SymbState systr) = (snd o hd) exec_sts
*)

val _ = check_feasible ((snd o hd) exec_sts)
val _ = check_feasible ((snd o hd o tl) exec_sts)


(* TODO: need min-max-abstraction for cycle counter to enable merging of states,
           we can start with considering max only *)
(* TODO: QUESTION: how to handle introduction of symbolic variables after function call?
           we cannot make the memory symbolic, we need to keep most of it, how to characterize this? *)

