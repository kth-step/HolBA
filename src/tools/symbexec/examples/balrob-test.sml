open HolKernel Parse

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;
open binariesCfgVizLib;

open bir_smtLib;

val entry_label = "motor_prep_input";

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
      SYST_pred : term list,
      SYST_pc : term
    };

fun SYST_get_env (SymbState systr) =
  #SYST_env systr;
fun SYST_get_pred (SymbState systr) =
  #SYST_pred systr;
fun SYST_get_pc (SymbState systr) =
  #SYST_pc systr;

fun SYST_update_env env' (SymbState systr) =
  SymbState {SYST_env  = env',
             SYST_pred = #SYST_pred systr,
             SYST_pc   = #SYST_pc systr };
fun SYST_update_pred pred' (SymbState systr) =
  SymbState {SYST_env  = #SYST_env systr,
             SYST_pred = pred',
             SYST_pc   = #SYST_pc systr };
fun SYST_update_pc pc' (SymbState systr) =
  SymbState {SYST_env  = #SYST_env systr,
             SYST_pred = #SYST_pred systr,
             SYST_pc   = pc' };

fun SYST_mk env pred pc =
  SymbState {SYST_env  = env,
             SYST_pred = pred,
             SYST_pc   = pc };


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


(*
val t = hd prog_vars;
*)
fun init_state lbl_tm prog_vars =
  let
    val initsymblist = List.map init_exp_from_bvar prog_vars;
    val init_countw = (("countw", ``BType_Imm Bit64``), ``BExp_Const (Imm64 0w)``);
  in
    SYST_mk [init_countw]
            []
            lbl_tm
  end;

open bir_exp_substitutionsSyntax;
(*
val syst = init_state prog_vars;
val SymbState systr = syst;
val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
val (bv, be) = dest_BStmt_Assign s
*)
val subst_exp = (snd o dest_eq o concl o EVAL o mk_bir_exp_const_prop o mk_bir_exp_subst1);
fun update_state syst (bv, be) =
  let
    val (sear, repl, bv_fresh_e) = get_fresh_var bv;

    val old_env = SYST_get_env syst;
    fun match_sear s_ = (s_ = sear);
    val old_env_filt = List.filter (not o match_sear o fst) old_env;
    val elem = (valOf o List.find (match_sear o fst)) old_env
(*
               handle Option => raise ERR "update_state" ("couldn't find searched variable: " ^ (fst sear));
*)
               handle Option => init_exp_from_bvar bv;

    val new_env = (sear, be)::(repl, snd elem)::old_env_filt;
    fun subst_exp_ e = subst_exp (bv, bv_fresh_e, e);
    val new_env_subst = List.map (fn (x, e) => (x, subst_exp_ e)) new_env;

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
fun tidyup_state syst =
  let
    val old_pred = SYST_get_pred syst;
    val old_env  = SYST_get_env  syst;

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
    (SYST_update_pred pred o
     SYST_update_env  env
    ) syst
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
      val n       = find_node ns lbl_tm;
      val n_type  = #CFGN_type n;
      val _       = if n_type = CFGNT_Call orelse n_type = CFGNT_Jump then () else
                      raise ERR "get_next_exec_sts" ("unexpected 2 at " ^ (term_to_string lbl_tm));

      val n_goto  = #CFGN_goto n;
      val lbl_tms = (valOf o cfg_targets_to_lbl_tms) n_goto
            handle Option => raise ERR "get_next_exec_sts" ("error for " ^ (term_to_string lbl_tm));
    in
      List.map (fn t => SYST_update_pc t syst) lbl_tms
    end);




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

(*
val syst = init_state prog_vars;
*)
fun symb_exec_block syst =
  let
    val lbl_tm = SYST_get_pc syst;

    val bl = (valOf o prog_get_block_) lbl_tm;
    val (_, stmts, est) = dest_bir_block bl;
    val s_tms = (fst o listSyntax.dest_list) stmts;

    val syst2 = List.foldl symb_exec_stmt syst s_tms;

    (* generate list of states from end statement *)
    val systs = get_next_exec_sts lbl_tm est syst2;
  in
    List.map simplify_state systs
  end;


fun symb_exec_to_stop []                  _            acc = acc
  | symb_exec_to_stop (exec_st::exec_sts) stop_lbl_tms acc =
      let
        val sts = symb_exec_block exec_st;
        val (new_acc, new_exec_sts) =
              List.partition (fn (syst) => List.exists (fn x => (SYST_get_pc syst) = x) stop_lbl_tms) sts;
      in
        symb_exec_to_stop (new_exec_sts@exec_sts) stop_lbl_tms (new_acc@acc)
      end;


fun check_feasible syst =
  let
    val pred = SYST_get_pred syst;
    val env  = SYST_get_env  syst;

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
val (bv_comp,exp) = hd env;
*)
    (* process the environment *)
    val (vars, asserts) = proc_preds (vars, asserts)
                                     (List.map (fn (bv_comp,exp) =>
      ``BExp_BinPred BIExp_Equal (BExp_Den ^(mk_BVar_string bv_comp)) ^exp``
    ) env);

    val result = querysmt smtlib_prelude vars asserts;

    val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
            raise ERR "check_feasible" "smt solver couldn't determine feasibility"
  in
    result <> BirSmtUnsat
  end;


val stop_lbl_tms = (List.map #CFGN_lbl_tm o
                    List.filter (fn n => node_to_rel_symbol n = name andalso
                                         #CFGN_type n = CFGNT_Return)
                   ) ns;

(*
(* stop at first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb08w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb22w)``];
(* just check first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb22w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb24w)``, ``BL_Address (Imm32 0xb2aw)``];
*)
(* stop after first branch *)
(*
val lbl_tm = ``BL_Address (Imm32 0xb08w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb24w)``, ``BL_Address (Imm32 0xb2aw)``];
*)

val syst  = init_state lbl_tm prog_vars;

(*
al syst_new = symb_exec_block syst;
*)

(* TODO: speed up: tidyup_state
           later: need a lookup map for "ns" in get_next_exec_sts (find_node) *)
(* 5s to branch with tidy up
   8s whole function without tidy up *)
val systs = symb_exec_to_stop [syst] stop_lbl_tms [];
(*
length systs

val syst = hd systs

length(SYST_get_env syst)
*)

fun simpleholset_to_list t =
  if pred_setSyntax.is_empty t then [] else
  if not (pred_setSyntax.is_insert t) then
    raise ERR "simpleholset_to_list" "cannot handle syntax"
  else
    let val (x, rset) = pred_setSyntax.dest_insert t in
      x::(simpleholset_to_list rset)
    end;


fun expand_exp env var =
  let
    val exp_o = List.find (fn (x, _) => x = var) env;
    val exp = case exp_o of
                 SOME x => snd x
               | NONE => raise ERR "expand_exp" ("\" ^ varname ^ \" not found");
    val exp_vars = (snd o dest_eq o concl o EVAL) ``(bir_vars_of_exp ^exp)``;
    val vars = (List.map dest_BVar_string o simpleholset_to_list) exp_vars;

    val subexps_raw = List.filter ((fn x => List.exists (fn y => x = y) vars) o fst) env;
    (* recursion on varexpressions first *)
    val subexps = List.map (fn (x, _) => (x, expand_exp env x)) subexps_raw;

    val exp_ = List.foldl (fn ((x, e), exp_) => subst_exp (mk_BVar_string x, e, exp_)) exp subexps;
  in
    exp_
  end;

(*
(hd(SYST_get_env syst))

val syst = List.nth(systs,0)

val env = (SYST_get_env syst);
val pred = (SYST_get_pred syst);

val (p::ps) = pred;
val benvmap = ((snd o dest_comb) ``BEnv (K NONE)``);

simple_pred_to_benvmap pred benvmap
*)

(*
             mk_comb (combinSyntax.mk_update (``2:num``,``"c"``),
                      ``\x. if x = 5:num then "a" else "b"``)
*)

open bir_exp_immSyntax;

val benvmap_empty = ((snd o dest_comb) ``BEnv (K NONE)``);
val bvalo_true = ``SOME (BVal_Imm (Imm1 1w))``;
val bvalo_false = ``SOME (BVal_Imm (Imm1 0w))``;
fun simple_pred_to_benvmap [] benvmap = benvmap
  | simple_pred_to_benvmap (p::ps) benvmap =
      let
        val benvmap_ =
          if not (is_BExp_Den p) then
            if not (is_BExp_UnaryExp p) orelse
               not ((fst o dest_BExp_UnaryExp) p = BIExp_Not_tm) orelse
               not ((is_BExp_Den o snd o dest_BExp_UnaryExp) p)
            then
              let
                val _ = print (term_to_string p);
                val _ = print "\n\n";
              in
                benvmap
              end
            else
              let
                val p_ = (snd o dest_BExp_UnaryExp) p;
                val (vn, _) = (dest_BVar o dest_BExp_Den) p_;
              in
                mk_comb (combinSyntax.mk_update(vn,bvalo_false), benvmap)
              end
          else
          let val (vn, _) = (dest_BVar o dest_BExp_Den) p; in
             mk_comb (combinSyntax.mk_update(vn,bvalo_true), benvmap)
          end
      in
        simple_pred_to_benvmap ps benvmap_
      end;

fun simple_p_to_subst p =
  if is_BExp_UnaryExp p andalso
     (fst o dest_BExp_UnaryExp) p = BIExp_Not_tm then
    subst [((snd o dest_BExp_UnaryExp) p) |-> ``(BExp_Const (Imm1 0w))``]
  else
    subst [p |-> ``(BExp_Const (Imm1 1w))``];

fun simple_pred_to_subst pred exp =
  List.foldl (fn (p, exp) => simple_p_to_subst p exp) exp pred;

fun eval_countw_in_syst syst =
  let
    val env = (SYST_get_env syst);
    val pred = (SYST_get_pred syst);
(*
    val benv = mk_BEnv (simple_pred_to_benvmap pred benvmap_empty);
*)
    val benv = ``BEnv (K NONE)``;
    val exp_ = expand_exp env ("countw", ``(BType_Imm Bit64)``);
    val exp = simple_pred_to_subst pred exp_;
  in
    (snd o dest_eq o concl o EVAL) ``bir_eval_exp ^exp ^benv``
  end;

val countws = List.map eval_countw_in_syst systs;
val counts = List.map (wordsSyntax.dest_word_literal o
                       bir_valuesSyntax.dest_BVal_Imm64 o
                       optionSyntax.dest_some) countws;

fun find_bound comp l =
  List.foldr (fn (x,m) => if comp (x, m) then x else m) (hd l) l;

val count_max = find_bound (Arbnum.>) counts;
val count_min = find_bound (Arbnum.<) counts;

val _ = print "\n\n\n";
val _ = print ("funname = " ^ (name) ^ "\n");
val _ = print ("max = " ^ (Arbnum.toString count_max) ^ "\n");
val _ = print ("min = " ^ (Arbnum.toString count_min) ^ "\n");

(*
check_feasible (syst)

val _ = check_feasible (hd systs)
val _ = check_feasible ((hd o tl) systs)
*)


(* TODO: introduce abstraction as possible value,
           the current values are concrete values (special sort),
           "top" is fresh variable,
           model unknown stack space as memory interval,
           need interval-abstraction for cycle counter to enable merging of states,
           we can start with considering max only *)

