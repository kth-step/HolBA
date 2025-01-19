structure birsSyntax =
struct

local

  open HolKernel Parse boolLib bossLib;

  (* error handling *)
  val libname = "birSyntax"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  fun check_CONV f (sfun, smsg) tm =
    ((if f tm then () else
        (print_term tm;
         raise ERR sfun smsg));
      REFL tm);

  fun check_raise f (sfun, smsg) x =
    if f x then () else
    raise ERR sfun smsg;

(* ---------------------------------------------------------------------------------------- *)

  (* turn bir conjunction into list of conjuncts (care should be taken because this is only meaningful if the type of expression is indeed bit1) *)
  fun dest_bandl x =
    let
      open bir_exp_immSyntax;
      open bir_expSyntax;
      fun is_BExp_And tm = is_BExp_BinExp tm andalso (is_BIExp_And o (fn (x,_,_) => x) o dest_BExp_BinExp) tm;
      fun dest_BExp_And tm = ((fn (_,x,y) => (x,y)) o dest_BExp_BinExp) tm;

      (* could add a typecheck of x here, to make sure that tm is indeed a Bit1 bir expression *)
      fun dest_bandl_r [] acc = acc
        | dest_bandl_r (tm::tms) acc =
        if not (is_BExp_And tm) then dest_bandl_r tms (tm::acc) else
        let
          val (tm1,tm2) = dest_BExp_And tm;
        in
          dest_bandl_r (tm1::tm2::tms) acc
        end;
    in
      List.rev (dest_bandl_r [x] [])
    end;

(* ---------------------------------------------------------------------------------------- *)

  local
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "option"
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  in
    val (OPTION_BIND_tm,  mk_OPTION_BIND, dest_OPTION_BIND, is_OPTION_BIND)  = syntax_fns2 "OPTION_BIND";
  end;

  local
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program"
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
    open bir_programTheory;
  in
    val (bir_get_current_statement_tm,  mk_bir_get_current_statement, dest_bir_get_current_statement, is_bir_get_current_statement)  = syntax_fns2 "bir_get_current_statement";
  end;

(*
local
  open symb_recordTheory;
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "symb_record"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
in
 val (symb_hl_step_in_L_sound_tm,  mk_symb_hl_step_in_L_sound, dest_symb_hl_step_in_L_sound, is_symb_hl_step_in_L_sound)  = syntax_fns2 "symb_hl_step_in_L_sound";
end;
*)

  local
    open birs_auxTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "birs_aux"
    val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns1_env = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  in
    val (birs_gen_env_tm,  mk_birs_gen_env, dest_birs_gen_env, is_birs_gen_env)  = syntax_fns1_env "birs_gen_env";
    val (bir_senv_GEN_list_tm,  mk_bir_senv_GEN_list, dest_bir_senv_GEN_list, is_bir_senv_GEN_list)  = syntax_fns1_env "bir_senv_GEN_list";
    val (birs_exps_of_senv_tm,  mk_birs_exps_of_senv, dest_birs_exps_of_senv, is_birs_exps_of_senv)  = syntax_fns1_set "birs_exps_of_senv";
    
    val (BExp_IntervalPred_tm,  mk_BExp_IntervalPred, dest_BExp_IntervalPred, is_BExp_IntervalPred)  = syntax_fns2 "BExp_IntervalPred";
  end;

  local
    open birs_rulesTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "birs_rules"
    val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
    val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns2_set = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
  in
    val (birs_symb_exec_tm,  mk_birs_symb_exec, dest_birs_symb_exec, is_birs_symb_exec)  = syntax_fns2 "birs_symb_exec";
    val (birs_symb_symbols_set_tm,  mk_birs_symb_symbols_set, dest_birs_symb_symbols_set, is_birs_symb_symbols_set)  = syntax_fns1_set "birs_symb_symbols_set";
    val (birs_freesymbs_tm,  mk_birs_freesymbs, dest_birs_freesymbs, is_birs_freesymbs)  = syntax_fns2_set "birs_freesymbs";
    val (birs_pcondinf_tm,  mk_birs_pcondinf, dest_birs_pcondinf, is_birs_pcondinf)  = syntax_fns1 "birs_pcondinf";
  end;

  local
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb";
    val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
    val syntax_fns2_env = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
    val syntax_fns2_set = syntax_fns 3 HolKernel.dest_binop HolKernel.mk_binop;
    val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
    val syntax_fns3_set = syntax_fns 4 HolKernel.dest_triop HolKernel.mk_triop;
  in
    val (birs_senv_typecheck_tm,  mk_birs_senv_typecheck, dest_birs_senv_typecheck, is_birs_senv_typecheck)  = syntax_fns2 "birs_senv_typecheck";
    
    val (birs_update_env_tm,  mk_birs_update_env, dest_birs_update_env, is_birs_update_env)  = syntax_fns2_env "birs_update_env";
    
    val (birs_exec_step_tm,  mk_birs_exec_step, dest_birs_exec_step, is_birs_exec_step)  = syntax_fns2_set "birs_exec_step";
    
    val (birs_symb_to_symbst_tm,  mk_birs_symb_to_symbst, dest_birs_symb_to_symbst, is_birs_symb_to_symbst)  = syntax_fns1 "birs_symb_to_symbst";
    
    val (birs_symbval_concretizations_tm,  mk_birs_symbval_concretizations, dest_birs_symbval_concretizations, is_birs_symbval_concretizations)  = syntax_fns2_set "birs_symbval_concretizations";

    val (birs_eval_label_exp_tm,  mk_birs_eval_label_exp, dest_birs_eval_label_exp, is_birs_eval_label_exp)  = syntax_fns3 "birs_eval_label_exp";

    val (birs_eval_exp_tm,  mk_birs_eval_exp, dest_birs_eval_exp, is_birs_eval_exp)  = syntax_fns2 "birs_eval_exp";
    val (birs_eval_exp_subst_tm,  mk_birs_eval_exp_subst, dest_birs_eval_exp_subst, is_birs_eval_exp_subst)  = syntax_fns2 "birs_eval_exp_subst";
    val (birs_eval_exp_subst_var_tm,  mk_birs_eval_exp_subst_var, dest_birs_eval_exp_subst_var, is_birs_eval_exp_subst_var)  = syntax_fns2 "birs_eval_exp_subst_var";

    val (birs_exec_stmt_jmp_tm,  mk_birs_exec_stmt_jmp, dest_birs_exec_stmt_jmp, is_birs_exec_stmt_jmp)  = syntax_fns3_set "birs_exec_stmt_jmp";
    val (birs_exec_stmt_tm,  mk_birs_exec_stmt, dest_birs_exec_stmt, is_birs_exec_stmt)  = syntax_fns3_set "birs_exec_stmt";

    val birs_state_t_ty = mk_type ("birs_state_t", []);
    fun dest_birs_state tm = let
      val (ty, l) = TypeBase.dest_record tm
      val _ = if ty = birs_state_t_ty then () else fail()
      val pc = Lib.assoc "bsst_pc" l
      val env = Lib.assoc "bsst_environ" l
      val status = Lib.assoc "bsst_status" l
      val pcond = Lib.assoc "bsst_pcond" l
    in
      (pc, env, status, pcond)
    end handle e => (print_term tm; raise wrap_exn "dest_bir_state" e);

    val is_birs_state = can dest_birs_state;

    fun mk_birs_state (pc, env, status, pcond) = let
      val l = [("bsst_pc", pc),
              ("bsst_environ", env),
              ("bsst_status", status),
              ("bsst_pcond", pcond)];
      in
          TypeBase.mk_record (birs_state_t_ty, l)
      end handle e => raise wrap_exn "mk_birs_state" e;

    val dest_birs_state_pc =
      ((fn (x,_,_,_) => x) o dest_birs_state);
    val dest_birs_state_env =
      ((fn (_,x,_,_) => x) o dest_birs_state);
    val dest_birs_state_status =
      ((fn (_,_,x,_) => x) o dest_birs_state);
    val dest_birs_state_pcond =
      ((fn (_,_,_,x) => x) o dest_birs_state);

    val birs_state_is_running = identical bir_programSyntax.BST_Running_tm o dest_birs_state_status;

    (* val (_tm,  mk_, dest_, is_)  = syntax_fns2_set "";*)
  end

  local
    open bir_symb_soundTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb_sound";
    val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
  in
    val (bir_prog_has_no_halt_tm,  mk_bir_prog_has_no_halt, dest_bir_prog_has_no_halt, is_bir_prog_has_no_halt)  = syntax_fns1 "bir_prog_has_no_halt";
  end

  local
    open bir_symb_sound_coreTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb_sound_core";
    val syntax_fns1_set = syntax_fns 2 HolKernel.dest_monop HolKernel.mk_monop;
  in
    val (birs_symb_symbols_tm,  mk_birs_symb_symbols, dest_birs_symb_symbols, is_birs_symb_symbols)  = syntax_fns1_set "birs_symb_symbols";
  end

  local
    open bir_symb_simpTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_symb_simp";
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
    val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  in
    val (birs_simplification_tm,  mk_birs_simplification, dest_birs_simplification, is_birs_simplification)  = syntax_fns3 "birs_simplification";
    val (birs_exp_imp_tm,  mk_birs_exp_imp, dest_birs_exp_imp, is_birs_exp_imp)  = syntax_fns2 "birs_exp_imp";
  end

  local
    open distribute_generic_stuffTheory;
    fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "distribute_generic_stuff";
    val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  in
    val (mk_bsysprecond_tm,  mk_mk_bsysprecond, dest_mk_bsysprecond, is_mk_bsysprecond)  = syntax_fns2 "mk_bsysprecond";
  end


(* ====================================================================================== *)

  (* extract terms from a sound structure *)
  (* ----------------------------------------------- *)
  fun mk_sysLPi (sys_tm, L_tm, Pi_tm) =
    pairSyntax.list_mk_pair [sys_tm, L_tm, Pi_tm];

  fun dest_sysLPi tm =
        case pairSyntax.strip_pair tm of
          [sys_tm, L_tm, Pi_tm] => (sys_tm, L_tm, Pi_tm)
        | _ => raise ERR "dest_sysLPi" "unexpected structure, should be triple";

  fun get_birs_prog tm =
    let
      val _ = if is_birs_symb_exec tm then () else
              raise ERR "get_birs_prog" "term must be a birs_symb_exec";
    in
      (fst o dest_birs_symb_exec) tm
    end;

  fun get_birs_sysLPi tm =
    let
      val _ = if is_birs_symb_exec tm then () else
              raise ERR "get_birs_sysLPi" "term must be a birs_symb_exec";
    in
      (dest_sysLPi o snd o dest_birs_symb_exec) tm
    end;

(* ---------------------------------------------------------------------------------------- *)

  (* function to get the initial state *)
  fun get_birs_sys tm =
    let
      val (sys_tm,_,_) = get_birs_sysLPi tm;
    in
      sys_tm
    end;

  (* function to get the set Pi *)
  fun get_birs_Pi tm =
    let
      val (_,_,Pi_tm) = get_birs_sysLPi tm;
    in
      Pi_tm
    end;

  (* function to get Pi as list *)
  val get_birs_Pi_list =
    (pred_setSyntax.strip_set o get_birs_Pi);

  (* function to get the length of Pi *)
  val get_birs_Pi_length =
    (length o get_birs_Pi_list);

  val len_of_thm_Pi = get_birs_Pi_length o concl;

  (* function to get the first Pi state *)
  val get_birs_Pi_first =
    (fst o pred_setSyntax.dest_insert o get_birs_Pi);

  (* get env mappings *)
  val get_env_mappings =
    (List.map pairSyntax.dest_pair o fst o listSyntax.dest_list o dest_birs_gen_env);

  (* get top env mapping *)
  fun get_env_top_mapping env =
    let
      val env_mappings = get_env_mappings env;
      val _ = if not (List.null env_mappings) then () else
              raise ERR "get_env_top_mapping" "need at least one mapping in the environment";
    in
      hd env_mappings
    end;
  
  (* function to get the top env mapping of the first Pi state *)
  fun get_birs_Pi_first_env_top_mapping tm =
    let
      val Pi_sys_tm = get_birs_Pi_first tm;
      val (_,env,_,_) = dest_birs_state Pi_sys_tm;
    in
      get_env_top_mapping env
    end;
  
  (* function to get the pcond of the first Pi state *)
  fun get_birs_Pi_first_pcond tm =
    let
      val Pi_sys_tm = get_birs_Pi_first tm;
      val (_,_,_,pcond) = dest_birs_state Pi_sys_tm;
    in
      pcond
    end;
  
  (* function to get the pcond of the first Pi state *)
  fun get_birs_sys_pcond tm =
    let
      val sys_tm = get_birs_sys tm;
      val (_,_,_,pcond) = dest_birs_state sys_tm;
    in
      pcond
    end;

(* ---------------------------------------------------------------------------------------- *)

(* helpers to check if sound structure terms (and subterms) are in normalform *)
(* ----------------------------------------------- *)
  (*
  val bir_state_init = ``<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
    bsst_environ :=
                birs_gen_env
                  [("x15",BExp_Den (BVar "sy_x15" (BType_Imm Bit64)));
                    ("x13",BExp_Den (BVar "sy_x13" (BType_Imm Bit64)));
                    ("x14",BExp_Den (BVar "sy_x14" (BType_Imm Bit64)));
                    ("x10",BExp_Den (BVar "sy_x10" (BType_Imm Bit64)));
                    ("MEM8",
                    BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)));
                    ("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
                    ("x1",BExp_Den (BVar "sy_x1" (BType_Imm Bit64)))];
    bsst_status := BST_Running;
    bsst_pcond :=
      BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0xFFFFFFw))
              (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_Aligned Bit32 2
              (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
        (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>``;
  *)
  fun birs_env_is_norm env =
    is_birs_gen_env env andalso
    (can listSyntax.dest_list o dest_birs_gen_env) env;

  fun birs_state_is_norm tm =
    is_birs_state tm andalso
    birs_env_is_norm (dest_birs_state_env tm);

  fun pred_set_is_norm tm =
    can pred_setSyntax.strip_set tm;

  fun birs_states_is_norm tm =
    pred_set_is_norm tm andalso
    (List.all birs_state_is_norm o pred_setSyntax.strip_set) tm;

  (* check if sound structure term is in normalform *)
  fun birs_is_norm tm =
    let
      val (sys, L, Pi) =
        get_birs_sysLPi tm
        handle _ => raise ERR "birs_is_norm" "unexpected term, should be a birs_symb_exec with a triple as structure";
    in
      birs_state_is_norm sys andalso
      pred_set_is_norm L andalso
      birs_states_is_norm Pi
    end
    handle _ => false;

(* ---------------------------------------------------------------------------------------- *)

  fun birs_check_norm_thm (sfun, smsg) =
    check_raise (birs_is_norm o concl) (sfun, "theorem is not norm" ^ smsg);

  fun birs_check_state_norm (sfun, smsg) =
    check_raise (birs_state_is_norm) (sfun, "state is not norm" ^ smsg);
  
  fun birs_check_min_Pi_thm m (sfun) =
    check_raise ((fn x => x >= m) o get_birs_Pi_length o concl) (sfun, "Pi has to have at least "^(Int.toString m)^" states");

  fun birs_check_env_norm (sfun, smsg) =
    check_raise (birs_env_is_norm) (sfun, "env is not norm" ^ smsg);

  (* check if two structures are in normform and use the same program *)
  fun birs_check_compatible A_thm B_thm =
    let
        val _ = birs_check_norm_thm ("birs_check_compatible", ": A") A_thm;
        val _ = birs_check_norm_thm ("birs_check_compatible", ": B") A_thm;

        val bprog_A_tm = (get_birs_prog o concl) A_thm;
        val bprog_B_tm = (get_birs_prog o concl) B_thm;
        val _ = if identical bprog_A_tm bprog_B_tm then () else
                raise ERR "birs_check_compatible" "the programs of A and B have to match";
    in
      ()
    end;

end (* local *)

end (* struct *)
