structure birs_utilsLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  (* error handling *)
  val libname = "birs_utilsLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  (* TODO: move the generic list functions somewhere else *)
  fun list_distinct _ [] = true
    | list_distinct eq_fun (x::xs) =
        if all (fn y => (not o eq_fun) (x, y)) xs then list_distinct eq_fun xs else false;

  fun list_mk_distinct_ _ [] acc = List.rev acc
    | list_mk_distinct_ eq_fun (x::xs) acc =
        list_mk_distinct_ eq_fun (List.filter (fn y => not (eq_fun (x, y))) xs) (x::acc);

  fun list_mk_distinct eq_fun l =
      list_mk_distinct_ eq_fun l [];

  (* the following two functions are from test-z3-wrapper.sml *)
  fun list_inclusion eq_fun l1 l2 =
    foldl (fn (x, acc) => acc andalso (exists (fn y => eq_fun (x, y)) l2)) true l1;

  local
    (* better than Portable.list_eq, because not order sensitive *)
    fun mutual_list_inclusion eq_fun l1 l2 =
      list_inclusion eq_fun l1 l2 andalso
      length l1 = length l2;
  in
    val list_eq_contents =
      mutual_list_inclusion;
  end

  fun list_in eq_fun x l =
    List.exists (fn y => eq_fun (x,y)) l;

  (* find the common elements of two lists *)
  fun list_commons eq_fun l1 l2 =
    List.foldl (fn (x,acc) => if list_in eq_fun x l2 then x::acc else acc) [] l1;

  fun list_minus eq_fun l1 l2 =
    List.filter (fn x => not (list_in eq_fun x l2)) l1;

  val gen_eq = (fn (x,y) => x = y);
  val term_id_eq = (fn (x,y) => identical x y);

(* ---------------------------------------------------------------------------------------- *)

  val mk_bandl = bslSyntax.bandl;

(* ---------------------------------------------------------------------------------------- *)

  fun TRY_LIST_REWR_CONV [] _ = raise UNCHANGED
    | TRY_LIST_REWR_CONV (rw_thm::rw_thms) tm =
        REWR_CONV rw_thm tm
        handle _ => TRY_LIST_REWR_CONV rw_thms tm;

  (* eliminate left conjuncts first *)
  val CONJL_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
    in
      fn lconv => fn rconv =>
      (LAND_CONV lconv) THENC
      (fn tm =>
        if (identical T o fst o dest_conj) tm then
          (REWR_CONV thm_T THENC rconv) tm
        else
          (REWR_CONV thm_F) tm)
    end;
  (* eliminate right conjuncts first *)
  val CONJR_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES;
    in
      fn lconv => fn rconv =>
      (RAND_CONV rconv) THENC
      (fn tm =>
        if (identical T o snd o dest_conj) tm then
          (REWR_CONV thm_T THENC lconv) tm
        else
          (REWR_CONV thm_F) tm)
    end;

  (* eliminate left disjuncts first *)
  val DISJL_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
    in
      fn lconv => fn rconv =>
      (LAND_CONV rconv) THENC
      (fn tm =>
        if (identical F o fst o dest_disj) tm then
          (REWR_CONV thm_F THENC lconv) tm
        else
          (REWR_CONV thm_T) tm)
    end;
  (* eliminate right disjuncts first *)
  val DISJR_CONV =
    let
      val thm_T = (GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
      val thm_F = (GEN_ALL o (fn x => List.nth(x,3)) o CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES;
    in
      fn lconv => fn rconv =>
      (RAND_CONV rconv) THENC
      (fn tm =>
        if (identical F o snd o dest_disj) tm then
          (REWR_CONV thm_F THENC lconv) tm
        else
          (REWR_CONV thm_T) tm)
    end;
  
  fun NEG_CONV conv =
    RAND_CONV conv THENC
    REWRITE_CONV [boolTheory.NOT_CLAUSES];

  local
    val thm_T = (CONJUNCT1 o SPEC_ALL) boolTheory.COND_CLAUSES;
    val thm_F = (CONJUNCT2 o SPEC_ALL) boolTheory.COND_CLAUSES;
    fun get_cond_c tm =
      let val (c,_,_) = dest_cond tm;
      in c end;
    fun clean_conv tm =
      if (identical T o get_cond_c) tm then
        REWR_CONV thm_T tm
      else
        REWR_CONV thm_F tm;
  in
    fun ITE_CONV conv =
      RATOR_CONV (RATOR_CONV (RAND_CONV conv)) THENC
      clean_conv;
  end

(* ---------------------------------------------------------------------------------------- *)

  (* get all mapped variable names *)
  fun birs_env_varnames birs_tm =
    let
      val _ = birs_check_state_norm ("birs_env_varnames", "") birs_tm;

      val env = dest_birs_state_env birs_tm;
      val mappings = get_env_mappings env;
      val varname_tms = List.map fst mappings;
      val varnames = List.map stringSyntax.fromHOLstring varname_tms;
      (* now that we have the mappings, also check that varnames is distinct *)
      val _ = if list_distinct gen_eq varnames then () else
              raise ERR "birs_env_varnames" "state has one variable mapped twice";
    in
      varnames
    end;

(* ---------------------------------------------------------------------------------------- *)

  local
    open pred_setSyntax;
    open pred_setTheory;
    val rotate_first_INSERTs_thm = prove(``
      !x1 x2 xs.
      (x1 INSERT x2 INSERT xs) = (x2 INSERT x1 INSERT xs)
    ``,
      fs [EXTENSION] >>
      metis_tac []
    );
    fun is_two_INSERTs tm = (is_insert tm) andalso ((is_insert o snd o dest_insert) tm);
  in
    fun rotate_two_INSERTs_conv tm =
      let
        val _ = if is_two_INSERTs tm then () else
          raise ERR "rotate_two_INSERTs_conv" "need to be a term made up of two inserts";
        val (x1_tm, x2xs_tm) = dest_insert tm;
        val (x2_tm, xs_tm) = dest_insert x2xs_tm;
        val inst_thm = ISPECL [x1_tm, x2_tm, xs_tm] rotate_first_INSERTs_thm;
      in
        inst_thm
      end;

    fun rotate_INSERTs_conv tm =
      (if not (is_two_INSERTs tm) then REFL else
        (rotate_two_INSERTs_conv THENC
        RAND_CONV rotate_INSERTs_conv)) tm;
  end

(* ---------------------------------------------------------------------------------------- *)

  fun check_imp_tm imp_tm =
    if not (is_birs_exp_imp imp_tm) then raise ERR "check_imp_tm" "term needs to be birs_exp_imp" else
    let
      val (pred1_tm, pred2_tm) = dest_birs_exp_imp imp_tm;
      val imp_bexp_tm = bslSyntax.bor (bslSyntax.bnot pred1_tm, pred2_tm);
      val imp_is_taut = bir_smtLib.bir_smt_check_taut false imp_bexp_tm;
    in
      if imp_is_taut then
        SOME (mk_oracle_thm "BIRS_IMP_Z3" ([], imp_tm))
      else
        NONE
    end;
  val check_imp_tm = aux_moveawayLib.wrap_cache_result Term.compare check_imp_tm;

  fun check_pcondinf_tm pcondinf_tm =
    if not (is_birs_pcondinf pcondinf_tm) then raise ERR "check_pcondinf_tm" "term needs to be birs_pcondinf" else
    let
      val pcond_tm = dest_birs_pcondinf pcondinf_tm;
      val pcond_is_contr = bir_smtLib.bir_smt_check_unsat false pcond_tm;
    in
      if pcond_is_contr then
        SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], pcondinf_tm))
      else
        NONE
    end;
  val check_pcondinf_tm = aux_moveawayLib.wrap_cache_result Term.compare check_pcondinf_tm;

  fun check_simplification_tm simp_tm =
    if not (is_birs_simplification simp_tm) then raise ERR "check_simplification_tm" "term needs to be birs_simplification" else
    let
      val (pred_tm, bexp1_tm, bexp2_tm) = dest_birs_simplification simp_tm;
      val simp_bexp_tm = bslSyntax.bor (bslSyntax.bnot pred_tm, bslSyntax.beq (bexp1_tm, bexp2_tm));
      val simp_is_taut = bir_smtLib.bir_smt_check_taut false simp_bexp_tm;
    in
      if simp_is_taut then
        SOME (mk_oracle_thm "BIRS_SIMP_Z3" ([], simp_tm))
      else
        NONE
    end;
  val check_simplification_tm = aux_moveawayLib.wrap_cache_result Term.compare check_simplification_tm;
  
  fun check_pcond_sat pcond_tm =
    let
      val pcond_is_sat = bir_smtLib.bir_smt_check_sat false pcond_tm;
      val pcond_sat_thm =
        if pcond_is_sat then
          mk_oracle_thm "BIRS_PCOND_SAT_Z3" ([], ``?i. birs_interpret_fun i ^pcond_tm = SOME bir_val_true``)
        else
          mk_oracle_thm "BIRS_PCOND_SAT_Z3" ([], ``!i. birs_interpret_fun i ^pcond_tm = SOME bir_val_false``);
    in
      (pcond_is_sat, pcond_sat_thm)
    end;


  local
    fun try_prove_assumption conv assmpt =
      let
          val assmpt_thm = conv assmpt;

          val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

          (* raise exception when the assumption turns out to be false *)
          val _ = if not (identical assmpt_new F) then () else
                  raise ERR "try_prove_assumption" "assumption does not hold";

          val _ = if identical assmpt_new T then () else
                  raise ERR "try_prove_assumption" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        if identical assmpt_new T then
          SOME (EQ_MP (GSYM assmpt_thm) TRUTH)
        else
          NONE
      end
      handle _ => NONE;
    val try_prove_assumption = fn conv => aux_moveawayLib.wrap_cache_result Term.compare (try_prove_assumption conv);

    fun try_prove_assumptions remove_all conv NONE = NONE
      | try_prove_assumptions remove_all conv (SOME t) =
      if (not o is_imp o concl) t then
        SOME t
      else
        let
          val assmpt = (fst o dest_imp o concl) t;
          val assmpt_thm_o = try_prove_assumption conv assmpt;
        in
          case assmpt_thm_o of
            NONE => if remove_all then NONE else SOME t
          | SOME assmpt_thm =>
              try_prove_assumptions
                remove_all
                conv
                (SOME (MP t assmpt_thm))
        end;
  in
    fun prove_assumptions remove_all conv thm = try_prove_assumptions remove_all conv (SOME thm);
  end

(* ---------------------------------------------------------------------------------------- *)

  local
    val struct_CONV =
      RAND_CONV;
    fun sys_CONV conv =
      LAND_CONV conv;
    fun L_CONV conv =
      RAND_CONV (LAND_CONV conv);
    fun Pi_CONV conv =
      RAND_CONV (RAND_CONV conv);
    val first_CONV =
      LAND_CONV;
    fun second_CONV conv =
      RAND_CONV (first_CONV conv);
  in
    (* apply state transformer to sys *)
    fun birs_sys_CONV conv tm =
      let
        val _ = if is_birs_symb_exec tm then () else
                raise ERR "birs_sys_CONV" "cannot handle term";
      in
        (struct_CONV (sys_CONV conv)) tm
      end;

    (* apply state transformer to L *)
    fun birs_L_CONV conv tm =
      let
        val _ = if is_birs_symb_exec tm then () else
                raise ERR "birs_L_CONV" "cannot handle term";
      in
        struct_CONV (L_CONV conv) tm
      end;

    (* apply state transformer to Pi *)
    fun birs_Pi_CONV conv tm =
      let
        val _ = if is_birs_symb_exec tm then () else
                raise ERR "birs_Pi_CONV" "cannot handle term";
      in
        (struct_CONV (Pi_CONV conv)) tm
      end;

    (* apply state transformer to first state in Pi *)
    (* TODO: should check the number of states in Pi *)
    fun birs_Pi_first_CONV conv =
      birs_Pi_CONV (first_CONV conv);
    fun birs_Pi_second_CONV conv =
      birs_Pi_CONV (second_CONV conv);
  end

  (* modify the environment *)
  fun birs_env_CONV conv birs_tm =
    let
      val _ = birs_check_state_norm ("birs_env_CONV", "") birs_tm;
      val env_new_thm = conv (dest_birs_state_env birs_tm);
    in
      (* better use some variant of EQ_MP? should exist *)
      REWRITE_CONV [Once env_new_thm] birs_tm
    end

  (* adjust the order of a mapping according to a given list *)
  fun birs_env_set_order_CONV varnames tm (* tm is birs_state_t record *) =
    let
      fun is_m_for_varname vn = (fn x => x = vn) o stringSyntax.fromHOLstring o fst o pairSyntax.dest_pair;
      fun get_exp_if vn m =
        if is_m_for_varname vn m then SOME m else NONE;
      fun reorder_mappings [] ms acc = ((List.rev acc)@ms)
        | reorder_mappings (varname::vns) ms acc =
            let
              val m_o = List.foldl (fn (m, acc) => case acc of SOME x => SOME x | NONE => get_exp_if varname m) NONE ms;
              val m = valOf m_o handle _ => raise ERR "birs_env_set_order_CONV" "variable name not mapped in bir state";
              val ms_new = List.filter (not o is_m_for_varname varname) ms;
            in
              reorder_mappings vns ms_new (m::acc)
            end;

      fun set_env_order env =
        let
          val _ = birs_check_env_norm ("birs_env_set_order_CONV", "") env;

          val (mappings, mappings_ty) = (listSyntax.dest_list o dest_birs_gen_env) env;

          val env_new = (mk_birs_gen_env o listSyntax.mk_list) (reorder_mappings varnames mappings [], mappings_ty);
        in
          aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_ENVVARSETORDER" (mk_eq (env, env_new))
        end
        handle _ => raise ERR "birs_env_set_order_CONV" "something uncaught";

      val env_eq_thm = birs_env_CONV set_env_order tm;
    in
      env_eq_thm
    end;

  (* move a certain mapping to the top *)
  fun birs_env_var_top_CONV varname =
    birs_env_set_order_CONV [varname];

(* ---------------------------------------------------------------------------------------- *)

  (* swap the first two states in Pi *)
  fun birs_Pi_rotate_two_RULE thm =
    let
      val _ = birs_check_norm_thm ("birs_Pi_rotate_two_RULE", "") thm;
      val _ = birs_check_min_Pi_thm 2 "birs_Pi_rotate_two_RULE" thm;

      val res_thm = CONV_RULE (birs_Pi_CONV (rotate_two_INSERTs_conv)) thm;
    in
      res_thm
    end
    handle e => (print "\nerror in birs_Pi_rotate_two_RULE\n"; raise e);

  fun birs_Pi_rotate_RULE thm =
    let
      val _ = birs_check_norm_thm ("birs_Pi_rotate_RULE", "") thm;
      val _ = birs_check_min_Pi_thm 2 "birs_Pi_rotate_RULE" thm;

      val res_thm = CONV_RULE (birs_Pi_CONV (rotate_INSERTs_conv)) thm;
    in
      res_thm
    end;

  (* goes through all Pi states and applies rule *)
  fun birs_Pi_each_RULE rule thm =
    let
      val len = (get_birs_Pi_length o concl) thm;
      (* iterate through all Pi states (with Pi rotate) and apply rule *)
      val thm_new =
        if len = 0 then
          thm
        else if len = 1 then
          rule thm
        else
          List.foldl (birs_Pi_rotate_RULE o rule o snd) thm (List.tabulate(len, I));
    in
      thm_new
    end;

(* ---------------------------------------------------------------------------------------- *)

  local
    open bir_programSyntax;
    open optionSyntax;
  in
    fun birs_is_stmt_Assign tm = is_some tm andalso (is_BStmtB o dest_some) tm andalso (is_BStmt_Assign o dest_BStmtB o dest_some) tm;
    fun birs_is_exec_branch thm = (get_birs_Pi_length o concl) thm > 1;

    fun birs_cond_RULE c f =
      if c then f else I;
    
    fun birs_if_assign_RULE tm = birs_cond_RULE (birs_is_stmt_Assign tm);
    fun birs_if_branch_RULE f thm = birs_cond_RULE (birs_is_exec_branch thm) f thm;
  end

(* ---------------------------------------------------------------------------------------- *)

  local
    open bir_expSyntax;
  in
  fun is_bir_exp t =
    type_of t = bir_exp_t_ty;

  fun bir_exp_size t =
    if is_BExp_Const t then
      1
    else if is_BExp_MemConst t then
      1
    else if is_BExp_Den t then
      1
    else if is_BExp_Cast t then
    let
      val (_,x,_) = dest_BExp_Cast t;
    in
      1 + bir_exp_size x
    end
    else if is_BExp_UnaryExp t then
    let
      val (_,x) = dest_BExp_UnaryExp t;
    in
      1 + bir_exp_size x
    end
    else if is_BExp_BinExp t then
    let
      val (_,x1,x2) = dest_BExp_BinExp t;
    in
      1 + bir_exp_size x1 + bir_exp_size x2
    end
    else if is_BExp_BinPred t then
    let
      val (_,x1,x2) = dest_BExp_BinPred t;
    in
      1 + bir_exp_size x1 + bir_exp_size x2
    end
    else if is_BExp_MemEq t then
    let
      val (x1,x2) = dest_BExp_MemEq t;
    in
      1 + bir_exp_size x1 + bir_exp_size x2
    end
    else if is_BExp_IfThenElse t then
    let
      val (c,x1,x2) = dest_BExp_IfThenElse t;
    in
      1 + bir_exp_size c + bir_exp_size x1 + bir_exp_size x2
    end
    else if is_BExp_Load t then
    let
      val (mem_e,a_e,_,_) = dest_BExp_Load t;
    in
      1 + bir_exp_size mem_e + bir_exp_size a_e
    end
    else if is_BExp_Store t then
    let
      val (mem_e,a_e,_,v_e) = dest_BExp_Store t;
    in
      1 + bir_exp_size mem_e + bir_exp_size a_e + bir_exp_size v_e
    end
    else if is_BExp_IntervalPred t then
    let
      val (ref_e, lim_tm) = dest_BExp_IntervalPred t;
      val (l_e, h_e) = pairSyntax.dest_pair lim_tm;
    in
      1 + bir_exp_size ref_e + bir_exp_size l_e + bir_exp_size h_e
    end
  (*
    else if is_... t then
    let
      val (_,x1,...) = dest_... t;
    in
      1 + bir_exp_size x1 + ...
    end
  *)
    else raise ERR "bir_exp_size" ("unknown BIR expression " ^ (term_to_string t));
  end

end (* local *)

end (* struct *)
