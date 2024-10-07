structure birs_mergeLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  (* error handling *)
  val libname = "birs_mergeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  fun list_distinct _ [] = true
    | list_distinct eq_fun (x::xs) =
        if all (fn y => (not o eq_fun) (x, y)) xs then list_distinct eq_fun xs else false;

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

  val gen_eq = (fn (x,y) => x = y);
  val term_id_eq = (fn (x,y) => identical x y);

(* ---------------------------------------------------------------------------------------- *)

  (* turn bir conjunction into list of conjuncts (care should be taken because this is only meaningful if the type of expression is indeed bit1) *)
  fun dest_band x =
    let
      open bir_exp_immSyntax;
      open bir_expSyntax;
      fun is_BExp_And tm = is_BExp_BinExp tm andalso (is_BIExp_And o (fn (x,_,_) => x) o dest_BExp_BinExp) tm;
      fun dest_BExp_And tm = ((fn (_,x,y) => (x,y)) o dest_BExp_BinExp) tm;

      (* could add a typecheck of x here, to make sure that tm is indeed a Bit1 bir expression *)
      fun dest_band_r [] acc = acc
        | dest_band_r (tm::tms) acc =
        if not (is_BExp_And tm) then dest_band_r tms (tm::acc) else
        let
          val (tm1,tm2) = dest_BExp_And tm;
        in
          dest_band_r (tm1::tm2::tms) acc
        end;
    in
      dest_band_r [x] []
    end;

(* ---------------------------------------------------------------------------------------- *)

  val birs_exp_imp_DROP_second_thm = prove(``
    !be1 be2.
    birs_exp_imp (BExp_BinExp BIExp_And be1 be2) be1
  ``,
    (* maybe only true for expressions of type Bit1 *)
    cheat
  );

  fun is_DROP_second_imp imp_tm =
    (SOME (UNCHANGED_CONV (REWRITE_CONV [birs_exp_imp_DROP_second_thm]) imp_tm)
            handle _ => NONE);

  fun is_conjunct_inclusion_imp imp_tm =
    let
      val (pcond1, pcond2) = dest_birs_exp_imp imp_tm;
      val pcond1l = dest_band pcond1;
      val pcond2l = dest_band pcond2;

      (* find the common conjuncts by greedily collecting what is identical in both *)
      val imp_is_ok = list_inclusion term_id_eq pcond2l pcond1l;
    in
      if imp_is_ok then
        SOME (mk_oracle_thm "BIRS_CONJ_INCL_IMP" ([], imp_tm))
      else
        NONE
    end;

  (* general path condition weakening with z3 (to throw away path condition conjuncts (to remove branch path condition conjuncts)) *)
  fun birs_Pi_first_pcond_RULE pcond_new thm =
    let
      val _ = if (symb_sound_struct_is_normform o concl) thm then () else
              raise ERR "birs_Pi_first_pcond_RULE" "theorem is not a standard birs_symb_exec";

      val (p_tm, tri_tm) = (dest_birs_symb_exec o concl) thm;
      val (sys_tm,L_tm,Pi_old_tm) = dest_sysLPi tri_tm;
      val (Pi_sys_old_tm, Pi_rest_tm) = pred_setSyntax.dest_insert Pi_old_tm;

      val (pc, env, status, pcond_old) = dest_birs_state Pi_sys_old_tm;
      val Pi_sys_new_tm = mk_birs_state (pc, env, status, pcond_new);
      val Pi_new_tm = pred_setSyntax.mk_insert (Pi_sys_new_tm, Pi_rest_tm);

      val imp_tm = mk_birs_exp_imp (pcond_old, pcond_new);
      (*
      val _ = print_term imp_tm;
      *)
      val pcond_drop_ok = isSome (is_DROP_second_imp imp_tm) orelse
                         isSome (is_conjunct_inclusion_imp imp_tm);
      val pcond_imp_ok = pcond_drop_ok orelse (* TODO: something might be wrong in expression simplification before smtlib-z3 exporter *)
                         isSome (birs_simpLib.check_imp_tm imp_tm);
      val _ = if pcond_imp_ok then () else
              (print "widening failed, path condition is not weaker\n";
               raise ERR "birs_Pi_first_pcond_RULE" "the supplied path condition is not weaker");
      (* TODO: use the bir implication theorem to justify the new theorem *)
    in
      mk_oracle_thm "BIRS_WIDEN_PCOND" ([], mk_birs_symb_exec (p_tm, mk_sysLPi (sys_tm,L_tm,Pi_new_tm)))
    end;

  (* TODO later (instantiate): general path condition strengthening with z3 *)
  fun birs_sys_pcond_RULE pcond_new thm =
    let
      val _ = if (symb_sound_struct_is_normform o concl) thm then () else
              raise ERR "birs_sys_pcond_RULE" "theorem is not a standard birs_symb_exec";

      val (p_tm, tri_tm) = (dest_birs_symb_exec o concl) thm;
      val (sys_old_tm,L_tm,Pi_tm) = dest_sysLPi tri_tm;

      val (pc, env, status, pcond_old) = dest_birs_state sys_old_tm;
      val sys_new_tm = mk_birs_state (pc, env, status, pcond_new);

      val imp_tm = mk_birs_exp_imp (pcond_new, pcond_old);
      val pcond_imp_ok = isSome (birs_simpLib.check_imp_tm imp_tm);
      val _ = if pcond_imp_ok then () else
              (print "narrowing failed, path condition is not stronger\n";
               raise ERR "birs_sys_pcond_RULE" "the supplied path condition is not stronger");
      (* TODO: use the bir implication theorem to justify the new theorem *)
    in
      mk_oracle_thm "BIRS_NARROW_PCOND" ([], mk_birs_symb_exec (p_tm, mk_sysLPi (sys_new_tm,L_tm,Pi_tm)))
    end;

(* ---------------------------------------------------------------------------------------- *)

  (* get all mapped variable names *)
  fun birs_env_varnames birs_tm =
    let
      val _ = if birs_state_is_normform birs_tm then () else
              raise ERR "birs_env_varnames" "symbolic bir state is not in standard form";

      val (_, env, _, _) = dest_birs_state birs_tm;
      val mappings = (fst o listSyntax.dest_list o dest_birs_gen_env) env;
      val varname_tms = List.map (fst o pairSyntax.dest_pair) mappings;
      val varnames = List.map stringSyntax.fromHOLstring varname_tms;
      (* make sure that varnames is distinct *)
      val _ = if list_distinct gen_eq varnames then () else
              raise ERR "birs_env_varnames" "state has one variable mapped twice";
    in
      varnames
    end;

  (* modify the environment *)
  fun birs_env_CONV is_start conv birs_tm =
    let
      val _ = if birs_state_is_normform_gen is_start birs_tm then () else
              raise ERR "birs_env_CONV" "symbolic bir state is not in standard form";

      val (pc, env, status, pcond) = dest_birs_state birs_tm;
      val env_new_thm = conv env;
    in
      REWRITE_CONV [env_new_thm] birs_tm
    end

  (* move a certain mapping to the top *)
  fun birs_env_var_top_CONV varname birs_tm =
    (* TODO: should use birs_env_CONV false *)
    let
      val _ = if birs_state_is_normform birs_tm then () else
              raise ERR "birs_env_var_top_CONV" "symbolic bir state is not in standard form";

      val (pc, env, status, pcond) = dest_birs_state birs_tm;
      val (mappings, mappings_ty) = (listSyntax.dest_list o dest_birs_gen_env) env;
      val is_m_for_varname = (fn x => x = varname) o stringSyntax.fromHOLstring o fst o pairSyntax.dest_pair;
      fun get_exp_if m =
        if is_m_for_varname m then SOME m else NONE;
      val m_o = List.foldl (fn (m, acc) => case acc of SOME x => SOME x | NONE => get_exp_if m) NONE mappings;
      val m = valOf m_o handle _ => raise ERR "birs_env_var_top_CONV" "variable name not mapped in bir state";
      val mappings_new = m::(List.filter (not o is_m_for_varname) mappings);

      val env_new = (mk_birs_gen_env o listSyntax.mk_list) (mappings_new, mappings_ty);
      val birs_new_tm = mk_birs_state (pc, env_new, status, pcond);
    in
      mk_oracle_thm "BIRS_ENVVARTOP" ([], mk_eq (birs_tm, birs_new_tm))
    end
    handle _ => raise ERR "birs_env_var_top_CONV" "something uncaught";

  local
    val struct_CONV =
      RAND_CONV;
    fun Pi_CONV conv =
      RAND_CONV (RAND_CONV conv);
    val first_CONV =
      LAND_CONV;
    fun second_CONV conv =
      RAND_CONV (first_CONV conv);

    val rotate_first_INSERTs_thm = prove(``
      !x1 x2 xs.
      (x1 INSERT x2 INSERT xs) = (x2 INSERT x1 INSERT xs)
    ``,
      cheat
    );
  in
    (* apply state transformer to Pi *)
    fun birs_Pi_CONV conv tm =
      let
        val _ = if symb_sound_struct_is_normform tm then () else
                raise ERR "birs_Pi_CONV" "term is not a standard birs_symb_exec";
      in
        (struct_CONV (Pi_CONV conv)) tm
      end;

    (* apply state transformer to first state in Pi *)
    fun birs_Pi_first_CONV conv =
      birs_Pi_CONV (first_CONV conv);
    fun birs_Pi_second_CONV conv =
      birs_Pi_CONV (second_CONV conv);

    (* swap the first two states in Pi *)
    fun birs_Pi_rotate_RULE thm =
      let
        (*val _ = print "rotating first two in Pi\n";*)
        val _ = if (symb_sound_struct_is_normform o concl) thm then () else
                raise ERR "birs_Pi_rotate_RULE" "theorem is not a standard birs_symb_exec";
        val (_,_,Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) thm;
        val num_Pi_el = (length o pred_setSyntax.strip_set) Pi_tm;
        val _ = if num_Pi_el > 1 then () else
                raise ERR "birs_Pi_rotate_RULE" "Pi has to have at least two states";

        val (_,_,Pi_tm) = (dest_sysLPi o snd o dest_birs_symb_exec o concl) thm;
        val (x1_tm, x2xs_tm) = pred_setSyntax.dest_insert Pi_tm;
        val (x2_tm, xs_tm) = pred_setSyntax.dest_insert x2xs_tm;
        val inst_thm = ISPECL [x1_tm, x2_tm, xs_tm] rotate_first_INSERTs_thm;
        val res_thm = CONV_RULE (struct_CONV (Pi_CONV (REWRITE_CONV [Once inst_thm]))) thm;
        (*val _ = print "finished rotating\n";*)
      in
        res_thm
      end;
  end

(* ---------------------------------------------------------------------------------------- *)

  (* function to get the initial state *)
  fun get_birs_sys tm =
    let
      val (_, tri_tm) = dest_birs_symb_exec tm;
      val (sys_tm,_,_) = dest_sysLPi tri_tm;
    in
      sys_tm
    end;

  (* function to get the set Pi *)
  fun get_birs_Pi tm =
    let
      val (_, tri_tm) = dest_birs_symb_exec tm;
      val (_,_,Pi_tm) = dest_sysLPi tri_tm;
    in
      Pi_tm
    end;

  (* function to get the first Pi state *)
  val get_birs_Pi_first =
    (fst o pred_setSyntax.dest_insert o get_birs_Pi);

  (* get top env mapping *)
  fun get_env_top_mapping env =
    let
      val (env_mappings, _) = (listSyntax.dest_list o dest_birs_gen_env) env;
      val _ = if not (List.null env_mappings) then () else
              raise ERR "get_env_top_mapping" "need at least one mapping in the environment";
    in
      (pairSyntax.dest_pair o hd) env_mappings
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

  (*
  - "free symbol" the top env mapping into the path condition (also need to be able to handle subexpression "free symboling" for the memory)
  *)
  local
    val freesymb_counter = ref (0:int);
    fun get_inc_freesymb_counter () =
      let
        val v = !freesymb_counter;
        val _ = freesymb_counter := v + 1;
      in
        v
      end;
    (* replace subexp in exp by subexp' *)
    fun substexp subexp' subexp exp =
      if identical exp subexp then subexp' else
      if (not o is_comb) exp then exp else
      let
        val (f, x) = dest_comb exp;
      in
        mk_comb
          (substexp subexp' subexp f,
           substexp subexp' subexp x)
      end;
  in
    fun set_freesymb_counter i = freesymb_counter := i;
    fun get_freesymb_name () = "syf_" ^ (Int.toString (get_inc_freesymb_counter ()));

    (* TODO: this is maybe too crude: just replace the given expression anywhere in the currently mapped expression *)
    fun birs_Pi_first_freesymb_RULE symbname exp_tm thm =
      let
        val _ = if (symb_sound_struct_is_normform o concl) thm then () else
                raise ERR "birs_Pi_first_freesymb_RULE" "theorem is not a standard birs_symb_exec";

        (* get the previously mapped expression *)
        val (p_tm, tri_tm) = (dest_birs_symb_exec o concl) thm;
        val (sys_tm,L_tm,Pi_old_tm) = dest_sysLPi tri_tm;
        val (Pi_sys_old_tm, Pi_rest_tm) = pred_setSyntax.dest_insert Pi_old_tm;
        val (pc, env_old, status, pcond_old) = dest_birs_state Pi_sys_old_tm;
        val (vn, exp_old) = get_env_top_mapping env_old;

        (* create new expression: check which part of the expression is supposed to be substituted *)
        val symb_tm = bir_envSyntax.mk_BVar (stringSyntax.fromMLstring symbname, (bir_exp_typecheckLib.get_type_of_bexp exp_tm));
        val exp_new = substexp (bslSyntax.bden symb_tm) exp_tm exp_old;

        (* debug printout *)
        (*
        val _ = print "freesymboling expression: ";
        val _ = print_term exp_tm;
        val _ = print "in: ";
        val _ = print_term exp_old;
        val _ = print "to: ";
        val _ = print_term exp_new;
        *)

        (* create updated state (pcond and env), and purge previous environment mapping *)
        val env_mod = mk_birs_update_env (pairSyntax.mk_pair (vn, exp_new), env_old);
        val purge_update_env_conv =
          REWRITE_CONV [birs_auxTheory.birs_update_env_thm] THENC
          RAND_CONV EVAL;
        val env_new = (snd o dest_eq o concl o purge_update_env_conv) env_mod;
        val pcond_new = bslSyntax.band (pcond_old, bslSyntax.beq (bslSyntax.bden symb_tm, exp_tm));
        val Pi_sys_new_tm = mk_birs_state (pc, env_new, status, pcond_new);

        (* debug printout *)
        (*
        val _ = print "freesymboling expression to pathcondition: ";
        val _ = print_term exp_tm;
        val _ = print "symb: ";
        val _ = print_term symb_tm;
        val _ = print "pcond before: ";
        val _ = print_term pcond_old;
        val _ = print "pcond after: ";
        val _ = print_term pcond_new;
        *)

        (* check that initial and modified state don't contain the free symbol (i.e., that it really is free) *)
        val symbs = List.map (pred_setSyntax.strip_set o snd o dest_eq o concl o bir_vars_ofLib.birs_symb_symbols_DIRECT_CONV o (fn x => ``birs_symb_symbols ^x``))
                    [(snd o dest_eq o concl o birs_env_CONV true (EVAL THENC REWRITE_CONV [GSYM birs_auxTheory.birs_gen_env_NULL_thm, GSYM birs_auxTheory.birs_gen_env_thm])) sys_tm, Pi_sys_old_tm];
        val _ = if not (List.exists (fn x => identical x symb_tm) (List.concat symbs)) then () else
                let
                  val _ = print_term symb_tm;
                  val _ = print "\nsymbs0:"
                  val _ = List.map (fn x => (print_term x)) (List.nth(symbs,0));
                  val _ = print "\nsymbs1:"
                  val _ = List.map (fn x => (print_term x)) (List.nth(symbs,1));
                in
                raise ERR "birs_Pi_first_freesymb_RULE" "symbol is not free in the initial state and/or the first Pi state" end;

        val Pi_new_tm = pred_setSyntax.mk_insert (Pi_sys_new_tm, Pi_rest_tm);
      in
        mk_oracle_thm "BIRS_FREESYMB" ([], mk_birs_symb_exec (p_tm, mk_sysLPi (sys_tm,L_tm,Pi_new_tm)))
      end;
  end

  (* forget the value/expression/computation of the top env mapping through free symbol and path condition widening *)
  fun birs_Pi_first_forget_RULE_gen symbname exp_tm thm =
    let
      (* "free symbol" the expression *)
      val free_thm = birs_Pi_first_freesymb_RULE symbname exp_tm thm;
      val Pi_sys_tm_free = (get_birs_Pi_first o concl) free_thm;
      val (_,_,_,pcond_free) = dest_birs_state Pi_sys_tm_free;
      val pcond_new = (snd o dest_comb o fst o dest_comb) pcond_free;

      (* debug printout *)
      (*val _ = print_thm free_thm;*)
      (*
      val _ = print "\npcond before: \n";
      val _ = print_term pcond_free;
      val _ = print "\npcond after: \n";
      val _ = print_term pcond_new;
      *)

      (* drop the pathcondition conjunct introduced by free-symboling, relies on how freesymb_RULE changes the path condition *)
      val forget_thm = birs_Pi_first_pcond_RULE pcond_new free_thm
            handle _ => ((*print_thm thm;
                         print_thm free_thm;*)
                         raise ERR "birs_Pi_first_forget_RULE_gen" "could not drop the conjunct, this should never happen");
    in
      forget_thm
    end

  fun birs_Pi_first_forget_RULE symbname thm =
    let
      (*val _ = print "forgetting first mapping in first of Pi\n";*)
      (* find the expression mapped at the top of env *)
      val Pi_sys_tm = (get_birs_Pi_first o concl) thm;
      val (_,env,_,pcond) = dest_birs_state Pi_sys_tm;
      val (_,exp) = get_env_top_mapping env;
    in
      birs_Pi_first_forget_RULE_gen symbname exp thm
    end

(* ---------------------------------------------------------------------------------------- *)

  (* helper functions for merge, merging of mapped expressions *)
  (* -------------------- *)

  (* initial implementation: just forget the two mappings, but use the same symbol name *)
  fun birs_Pi_first_env_top_mapping_merge_forget thm =
    let
      val symbname = get_freesymb_name ();
    in
      (birs_Pi_first_forget_RULE symbname o birs_Pi_rotate_RULE o birs_Pi_first_forget_RULE symbname) thm
    end;

  fun birs_Pi_first_env_top_mapping_merge_fold ((exp1,exp2), thm) =
    let
      val symbname = get_freesymb_name ();
    in
      (birs_Pi_rotate_RULE o birs_Pi_first_forget_RULE_gen symbname exp2 o
       birs_Pi_rotate_RULE o birs_Pi_first_forget_RULE_gen symbname exp1) thm
    end;

  local
    fun unify_stores_foldfun mexp (store, (stores2, stores1_new, stores2_new, forget_exps)) =
      let
        fun get_store_v (_, _, expv) = expv;
        fun is_same_loc_store (expad, endi, _) (expad2, endi2, _) =
          if not (identical endi endi2) then raise ERR "is_same_loc_store" "should be same endianness everywhere" else
          (* assuming disjunctness of stores, address can be checked by syntactical identity *)
          identical expad expad2;
        fun exp_to_mem_ld_sz expv = (bir_valuesSyntax.dest_BType_Imm o bir_exp_typecheckLib.get_type_of_bexp) expv
              handle _ => raise ERR "unify_stores_foldfun" "couldn't get type of stored expression";
        fun mk_empty_store (expad, endi, expv) = (expad, endi, bir_expSyntax.mk_BExp_Load (mexp, expad, endi, exp_to_mem_ld_sz expv));

        val match_store2_o = List.find (is_same_loc_store store) stores2;
        val store2 = Option.getOpt (match_store2_o, mk_empty_store store);
      in
        (List.filter (not o is_same_loc_store store) stores2, store::stores1_new, store2::stores2_new, (get_store_v store, get_store_v store2)::forget_exps)
      end;

    fun flippair (x,y) = (y,x);
  in
    fun unify_stores mexp stores1 stores2 =
      let
        val (stores2_0, stores1_new_0, stores2_new_0, forget_exps_0) = List.foldl (unify_stores_foldfun mexp) (stores2, [], [], []) stores1;
        val (stores1_0, stores2_new_1, stores1_new_1, forget_exps_1) = List.foldl (unify_stores_foldfun mexp) ([], [], [], List.map flippair forget_exps_0) stores2_0;
        val _ = if List.null stores1_0 then () else raise ERR "unify_stores" "this should never happen";
      in
        (List.rev (stores1_new_1@stores1_new_0), List.rev (stores2_new_1@stores2_new_0), List.rev (List.map flippair forget_exps_1))
      end;
  end

  (* do something special for store operations, cannot just forget the whole thing *)
  fun birs_Pi_first_env_top_mapping_merge_store exp1 exp2 thm =
    (* just unfold them into a list and assume they are all disjunct memory locations (TODO: for now),
         can reuse code from the cheated store-store simplification *)
    let
      (* we know that exp1 and exp2 are BExp_Store operations, when this function is called *)
      val (mexp1, stores1) = birs_simp_instancesLib.dest_BExp_Store_list exp1 [];
      val (mexp2, stores2) = birs_simp_instancesLib.dest_BExp_Store_list exp2 [];

      val _ = if identical mexp1 mexp2 then () else
              raise ERR "birs_Pi_first_env_top_mapping_merge_store" "the bir memory symbols have to be identical";

      (* find shuffled and padded store sequences, use disjunct assumption for this *)
      (* at the same time, collect a distinct set of expression pairs that should be "freesymboled" to make the states equal *)
      val (stores1_new, stores2_new, forget_exps) = unify_stores mexp1 stores1 stores2;

      (* apply the shuffling by cheated rewriting (justified by disjunct assumption) *)
      fun mk_mem_eq_thm mexp stores stores_new = mk_oracle_thm "BIRS_MEM_DISJ_SHUFFLE" ([], mk_eq (birs_simp_instancesLib.mk_BExp_Store_list (mexp, stores), birs_simp_instancesLib.mk_BExp_Store_list (mexp, stores_new)));
      val bad_cheat_eq_thm_1 = mk_mem_eq_thm mexp1 stores1 stores1_new;
      val bad_cheat_eq_thm_2 = mk_mem_eq_thm mexp1 stores2 stores2_new;
      (*val _ = print_thm bad_cheat_eq_thm_1;
      val _ = print_thm bad_cheat_eq_thm_2;*)
      val thm_shuffled =
        CONV_RULE (birs_Pi_first_CONV (REWRITE_CONV [Once bad_cheat_eq_thm_1]) THENC
                   birs_Pi_second_CONV (REWRITE_CONV [Once bad_cheat_eq_thm_2])) thm;
      (*val _ = print_thm thm_shuffled;*)

      (* apply the freesymboling as instructed by forget_exps *)
      val thm_free = List.foldl birs_Pi_first_env_top_mapping_merge_fold thm_shuffled forget_exps;
      (*val _ = print_thm thm_free;*)
      val _ = print "\ndone with birs_Pi_first_env_top_mapping_merge_store\n";
    in
      thm_free
    end;

  (* choose how to deal with the expressions at hand *)
  fun birs_Pi_first_env_top_mapping_merge exp1 exp2 thm =
    let
      open bir_expSyntax;
      val default_op = birs_Pi_first_env_top_mapping_merge_forget;
      (* choose the merging approach: *)
    in
      (* do not touch if they are syntactically identical (or semantically, when checked with z3 under the respective path conditions) *)
      if identical exp1 exp2 then thm else

      (* store operation *)
      if is_BExp_Store exp1 andalso is_BExp_Store exp2 then
        birs_Pi_first_env_top_mapping_merge_store exp1 exp2 thm else

      (* TODO: interval (specifically countw) *)
      if false then raise ERR "birs_Pi_first_env_top_mapping_merge" "not implemented yet" else

      (* just unify all others *)
      default_op thm
    end;

  val INSERT_INSERT_EQ_thm = prove(``
    !x1 x2 xs.
    (x1 = x2) ==>
    (x1 INSERT x2 INSERT xs) = (x1 INSERT xs)
  ``,
    cheat (* pred_setTheory.INSERT_INSERT *)
  );

  (* the merge function for the first two Pi states *)
  fun birs_Pi_merge_2_RULE thm =
    let
      val _ = print "merging the first two in Pi\n";
      val timer = holba_miscLib.timer_start 0;
      val _ = if (symb_sound_struct_is_normform o concl) thm then () else
              raise ERR "birs_Pi_merge_2_RULE" "theorem is not a standard birs_symb_exec";
      (* assumes that Pi has at least two states *)
      val (_,_,Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) thm;
      val Pi_tms = pred_setSyntax.strip_set Pi_tm;
      val num_Pi_el = length Pi_tms;
      val _ = if num_Pi_el > 1 then () else
              raise ERR "birs_Pi_merge_2_RULE" "Pi has to have at least two states";

      (* get the env mapped strings, make sure they have the same ones in each *)
      val Pi_sys1_tm = List.nth(Pi_tms, 0);
      val Pi_sys2_tm = List.nth(Pi_tms, 1);
      val varnames = birs_env_varnames Pi_sys1_tm;
      val _ = if list_eq_contents gen_eq varnames (birs_env_varnames Pi_sys2_tm) then () else
              raise ERR "birs_Pi_merge_2_RULE" "the two states do not have the same variables mapped in the environment";

      (* for each mapped variable: *)
      val thm_env = List.foldl (fn (vn, thm0) =>
        let
          (* move the mapping to the top *)
          val thm1 = CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV vn)) thm0;
          val exp1 = (snd o get_birs_Pi_first_env_top_mapping o concl) thm1;
          val thm2 = birs_Pi_rotate_RULE thm1;
          val thm3 = CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV vn)) thm2;
          val exp2 = (snd o get_birs_Pi_first_env_top_mapping o concl) thm3;

          val thm4 = birs_Pi_first_env_top_mapping_merge exp2 exp1 thm3;
        in thm4 end) thm varnames;
      val _ = print "unified envs\n";

      (* also unify the two path conditions *)
      val thm_env_pcond =
        let
          val thm0 = thm_env;
          val pcond1 = (get_birs_Pi_first_pcond o concl) thm0;
          val thm1 = birs_Pi_rotate_RULE thm0;
          val pcond2 = (get_birs_Pi_first_pcond o concl) thm1;

          (* get conjuncts as list *)
          val pcond1l = dest_band pcond1;
          val pcond2l = dest_band pcond2;

          (* find the common conjuncts by greedily collecting what is identical in both *)
          val pcond_commonl = list_commons term_id_eq pcond1l pcond2l;
          val pcond_common = bslSyntax.bandl pcond_commonl;

          (* fix the path condition in both states accordingly *)
          val thm2 = (birs_Pi_first_pcond_RULE pcond_common o birs_Pi_rotate_RULE o birs_Pi_first_pcond_RULE pcond_common) thm1;
        in thm2 end;
      val _ = print "unified pcond\n";

      (* merge the first two states in the HOL4 pred_set *)
      (* (TODO: maybe need to prove that they are equal because they are not syntactically identical) *)
      (*
      val rewrite_thm = ISPECL (((fn x => List.take (x, 2)) o pred_setSyntax.strip_set o get_birs_Pi o concl) thm_env_pcond) INSERT_INSERT_EQ_thm;
      (*val _ = print_thm rewrite_thm;*)
      val rewrite_thm_fix = CONV_RULE (CHANGED_CONV (QUANT_CONV (LAND_CONV (*aux_setLib.birs_state_EQ_CONV*)EVAL))) rewrite_thm;
      val thm_merged = CONV_RULE (CHANGED_CONV (birs_Pi_CONV (REWRITE_CONV [rewrite_thm_fix]))) thm_env_pcond;*)
      val thm_merged = CONV_RULE (CHANGED_CONV (birs_Pi_CONV (REWRITE_CONV [ISPEC ((get_birs_Pi_first o concl) thm_env_pcond) pred_setTheory.INSERT_INSERT]))) thm_env_pcond;
      val _ = print "eliminated one from Pi\n";
      val _ = holba_miscLib.timer_stop
        (fn delta_s => print ("  merging two in Pi took " ^ delta_s ^ "\n")) timer;
    in
      thm_merged
    end;

  (* merging of all states in Pi *)
  fun birs_Pi_merge_RULE thm =
    let
      val _ = if (symb_sound_struct_is_normform o concl) thm then () else
              raise ERR "birs_Pi_merge_RULE" "theorem is not a standard birs_symb_exec";
      val (_,_,Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) thm;
      val num_Pi_el = (length o pred_setSyntax.strip_set) Pi_tm;
    in
      (* recursion, go over all the Pi states until there is only one left *)
      if num_Pi_el < 2 then
        thm
      else
        birs_Pi_merge_RULE (birs_Pi_merge_2_RULE thm)
    end;

  (*
  TODO later: add interval handling (as general as possible, but for now also ok to focus on countw alone)
  - have interval hol4 predicate
  - squash conjuncts that are only related to the latest free symbol intro and connect to previous interval
  - widen the intervals (for now only have one)
  *)

(* ---------------------------------------------------------------------------------------- *)
(*
  (* TODO later (instantiate): rename all variables *)
  local
    val renamesymb_counter = ref (0:int);
    fun get_inc_renamesymb_counter () =
      let
        val v = !renamesymb_counter;
        val _ = renamesymb_counter := v + 1;
      in
        v
      end;
    fun get_renamesymb_name () = "syr_" ^ (Int.toString (get_inc_renamesymb_counter ()));
  in
    fun set_renamesymb_counter i = renamesymb_counter := i;
    fun birs_sound_rename_all_RULE thm =
      let
        val _ = if (symb_sound_struct_is_normform o concl) thm then () else
                raise ERR "birs_sound_rename_all_RULE" "theorem is not a standard birs_symb_exec";

                (*  *)
      in
        ()
      end;
  end

(* ---------------------------------------------------------------------------------------- *)

  (* TODO later (instantiate): the instantiation function *)
  fun birs_sound_symb_inst_RULE symb_exp_map thm =
    let
      val _ = if (symb_sound_struct_is_normform o concl) thm then () else
              raise ERR "birs_sound_symb_inst_RULE" "theorem is not a standard birs_symb_exec";

      (* for now a function that does all at once and cheats *)
      (* TODO: later have a subfunction that does one by one (hopefully not too slow) *)
    in
      ()
    end;

  (*
  TODO later (instantiate): instantiation process
  TODO: set up example like this --- execute with symbol in the path condition from the beginning (to be able to preserve path condition for after instantiation)
  *)
  fun birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm A_thm B_thm =
    let
      val _ = birs_symb_exec_check_compatible A_thm B_thm;

      (* rename all symbols before instantiating! (birs_sound_rename_all_RULE) *)

      (* identify instantiation needed for B, assumes to take the first state in Pi of A, instantiate and compose sequentially *)

      (* instantiate all environment mappings (birs_sound_symb_inst_RULE) *)

      (* take care of path conditions (after instantiating the original path condition symbol) *)
      (* ------- *)
      (* use path condition implication with z3 to remove the summary conjuncts (only keep the conjunct corresponding to the original path condition symbol) (birs_sys_pcond_RULE) *)
      (* cleanup Pi path conditions (probably only need to consider one for starters) to only preserve non-summary conjunct (as the step before) (birs_Pi_first_pcond_RULE) *)
    in
      (* sequential composition of the two theorems (birs_composeLib.birs_rule_SEQ_fun birs_rule_SEQ_thm A_thm B_thm) *)
      ()
    end;
*)

end (* local *)

end (* struct *)
