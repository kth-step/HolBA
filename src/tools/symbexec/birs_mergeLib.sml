structure birs_mergeLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;

  (* error handling *)
  val libname = "birs_mergeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  val debug_mode = false;

in (* local *)

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
        val _ = birs_check_norm_thm ("birs_Pi_first_freesymb_RULE", "") thm;

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
        val _ = if not debug_mode then () else print "created update env exp\n";
        val purge_update_env_conv =
          REWRITE_CONV [birs_auxTheory.birs_update_env_thm] THENC
          RAND_CONV EVAL;
        val _ = if not debug_mode then () else print "purged update env exp\n";
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
        val symbs = List.map (pred_setSyntax.strip_set o rhs o concl o bir_vars_ofLib.birs_symb_symbols_DIRECT_CONV o mk_birs_symb_symbols)
                    [sys_tm, Pi_sys_old_tm];
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

      (* drop the pathcondition conjunct introduced by free-symboling, relies on how freesymb_RULE changes the path condition *)
      val forget_thm = birs_Pi_first_pcond_drop true free_thm
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
      (birs_Pi_first_forget_RULE symbname o birs_Pi_rotate_two_RULE o birs_Pi_first_forget_RULE symbname) thm
    end;

  fun birs_Pi_first_env_top_mapping_merge_fold ((exp1,exp2), thm) =
    let
      val symbname = get_freesymb_name ();
    in
      (birs_Pi_rotate_two_RULE o birs_Pi_first_forget_RULE_gen symbname exp2 o
       birs_Pi_rotate_two_RULE o birs_Pi_first_forget_RULE_gen symbname exp1) thm
    end;

  local
    val bir_exp_t_tm = ``BExp_Const (Imm1 1w)``;
    fun addresses_are_equal a1 a2 =
      let
        val imp_tm = birsSyntax.mk_birs_exp_imp (bir_exp_t_tm, bslSyntax.beq (a1, a2));
        val ad_is_eq = isSome (birs_utilsLib.check_imp_tm imp_tm);
      in
        (*identical a1 a2*)
        ad_is_eq
      end;
    
    fun values_are_equal v1 v2 =
      (* TODO: could be not identical but still equal, would need smt solver to check,
                also this way we do not need to manage theorems to argue value equivalence when merging *)
      identical v1 v2;

    fun unify_stores_foldfun mexp (store, (stores2, stores1_new, stores2_new, forget_exps)) =
      (* TODO: better reuse stores_match in birs_simp_instancesLib,
           for example, here is no type-check that would be required for soundness *)
      let
        fun get_store_v (_, _, expv) = expv;
        fun is_same_loc_store (expad, endi, _) (expad2, endi2, _) =
          if not (identical endi endi2) then raise ERR "is_same_loc_store" "should be same endianness everywhere" else
          addresses_are_equal expad expad2;
        fun exp_to_mem_ld_sz expv = (bir_valuesSyntax.dest_BType_Imm o bir_exp_typecheckLib.get_type_of_bexp) expv
              handle _ => raise ERR "unify_stores_foldfun" "couldn't get type of stored expression";
        fun mk_empty_store (expad, endi, expv) = (expad, endi, bir_expSyntax.mk_BExp_Load (mexp, expad, endi, exp_to_mem_ld_sz expv));

        val match_store2s = List.filter (is_same_loc_store store) stores2;
        val match_store2_o =
          if length match_store2s = 0 then NONE
          else if length match_store2s = 1 then SOME (hd match_store2s)
          else (
            (*raise ERR "unify_stores_foldfun" "multiple stores with the same address"*)
            print "\nwarning: multiple stores with the same address\n";
            SOME (last match_store2s)
          );
        val store2 = Option.getOpt (match_store2_o, mk_empty_store store);
        val forget_exps_add =
          if values_are_equal (get_store_v store) (get_store_v store2) then [] else
          [(get_store_v store, get_store_v store2)];
        (*val forget_exps_add = [(get_store_v store, get_store_v store2)];*)
      in
        (List.filter (not o is_same_loc_store store) stores2, store::stores1_new, store2::stores2_new, forget_exps_add@forget_exps)
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


fun print_mem_exp mem_exp =
  let
    (*val _ = print_term mem_exp;*)
    val (mexp, stores) = birs_simp_instancesLib.dest_BExp_Store_list mem_exp [];
    val _ = print ("MEM " ^ (term_to_string mexp) ^ " [\n");
    fun print_store (expad, _, expv) =
      let
        val expad_s = term_to_string expad;
        val expv_s = term_to_string expv;
        val expv_s = if String.size expv_s > 100 then "(...)" else expv_s;
        val _ = print ("  " ^ expad_s ^ "\n    -> " ^ expv_s ^ "\n");
      in () end;
    val _ = map (print_store) stores;
    val _ = print ("]\n");
  in () end;

  (* do something special for store operations, cannot just forget the whole thing *)
  fun birs_Pi_first_env_top_mapping_merge_store exp1 exp2 thm =
    (* just unfold them into a list and assume they are all disjunct memory locations
      (TODO: it is like this for now)
      (NOTE: that the store address expressions themselves are not equal and disjunct is crudely justified by running the store-store cheater before)
      reused code from the cheated store-store simplification *)
    let
      (* we know that exp1 and exp2 are BExp_Store operations, when this function is called *)
      val (mexp1, stores1) = birs_simp_instancesLib.dest_BExp_Store_list exp1 [];
      val (mexp2, stores2) = birs_simp_instancesLib.dest_BExp_Store_list exp2 [];
      (*
      val _ = print "\n\n\nmemory1:\n";
      val _ = print_mem_exp exp1;
      val _ = print "\nmemory2:\n";
      val _ = print_mem_exp exp2;
      *)

      val _ = if identical mexp1 mexp2 then () else
              raise ERR "birs_Pi_first_env_top_mapping_merge_store" "the bir memory symbols have to be identical";

      (* find shuffled and padded store sequences, use disjunct assumption for this *)
      (* at the same time, collect a distinct set of expression pairs that should be "freesymboled" to make the states equal *)
      val (stores1_new, stores2_new, forget_exps) = unify_stores mexp1 stores1 stores2
        handle e => (print "\nstore unification issue:\n"; print_term exp1; print "\n"; print_term exp2; print "\n"; raise e);
      (*val forget_exps = List.filter (fn (x,y) => not (identical x y)) forget_exps;*)

      (* apply the shuffling by cheated rewriting (justified by disjunct assumption) *)
      fun mk_mem_eq_thm mexp stores stores_new = mk_oracle_thm "BIRS_MEM_DISJ_SHUFFLE" ([], mk_eq (birs_simp_instancesLib.mk_BExp_Store_list (mexp, stores), birs_simp_instancesLib.mk_BExp_Store_list (mexp, stores_new)));
      val bad_cheat_eq_thm_1 = mk_mem_eq_thm mexp1 stores1 stores1_new;
      val bad_cheat_eq_thm_2 = mk_mem_eq_thm mexp1 stores2 stores2_new;
      val _ = print "\n\n";(*
      val _ = print "\n\nmerging stores1:\n";
      val _ = print_thm bad_cheat_eq_thm_1;
      val _ = print "\n\nmerging stores2:\n";
      val _ = print_thm bad_cheat_eq_thm_2;*)
      val _ = print "\n\nforgetting:\n";
      val _ = List.map (fn (x,y) =>
        let
          val x_s = term_to_string x;
          val x_s = if String.size x_s > 100 then "(...)" else x_s;
          val y_s = term_to_string y;
          val y_s = if String.size y_s > 100 then "(...)" else y_s;
          val _ = print ("{"^x_s^";"^y_s^"}");
          val _ = print "\n";
        in () end) forget_exps;
      val _ = print "\n\n";
      (*val _ = print_thm bad_cheat_eq_thm_1;
      val _ = print_thm bad_cheat_eq_thm_2;*)
      val thm_shuffled =
        CONV_RULE (birs_Pi_first_CONV (REWRITE_CONV [Once bad_cheat_eq_thm_1]) THENC
                   birs_Pi_second_CONV (REWRITE_CONV [Once bad_cheat_eq_thm_2])) thm;
      (*val _ = print_thm thm_shuffled;*)

      (* apply the freesymboling as instructed by forget_exps *)
      val thm_free = List.foldl birs_Pi_first_env_top_mapping_merge_fold thm_shuffled forget_exps;
      (*val _ = print_thm thm_free;*)
      val _ = if not debug_mode then () else print "\ndone with birs_Pi_first_env_top_mapping_merge_store\n";
    in
      thm_free
    end;

  (* choose how to deal with the expressions at hand *)
  fun birs_Pi_first_env_top_mapping_merge exp1 exp2 thm =
    let
      (* TODO: remove extra rotations, they are there to keep the parity for clearer debug outputs *)
      open bir_expSyntax;
      val default_op = birs_Pi_first_env_top_mapping_merge_forget;
      (* choose the merging approach: *)
    in
      (* do not touch if they are syntactically identical (or semantically, when checked with z3 under the respective path conditions) *)
      if identical exp1 exp2 then birs_Pi_rotate_two_RULE thm else

      (* store operation *)
      if is_BExp_Store exp1 orelse is_BExp_Store exp2 then
        birs_Pi_first_env_top_mapping_merge_store exp2 exp1 (birs_Pi_rotate_two_RULE thm) else

      (* TODO: interval (specifically countw and SP) *)
      if false then raise ERR "birs_Pi_first_env_top_mapping_merge" "not implemented yet" else

      (* just unify all others *)
      (if not debug_mode then () else print "applying default_op\n";
      default_op thm)
    end;

  val INSERT_INSERT_EQ_thm = prove(``
    !x1 x2 xs.
    (x1 = x2) ==>
    (x1 INSERT x2 INSERT xs) = (x1 INSERT xs)
  ``,
    METIS_TAC [pred_setTheory.INSERT_INSERT]
  );

  (* the merge function for the first two Pi states *)
  fun birs_Pi_merge_2_RULE thm =
    let
      val _ = birs_check_norm_thm ("birs_Pi_merge_2_RULE", "") thm;

      val _ = if not debug_mode then () else print "merging the first two in Pi\n";
      val timer = holba_miscLib.timer_start 0;
      (* assumes that Pi has at least two states *)
      val Pi_tms = (get_birs_Pi_list o concl) thm;
      val num_Pi_el = length Pi_tms;
      val _ = if num_Pi_el > 1 then () else
              raise ERR "birs_Pi_merge_2_RULE" "Pi has to have at least two states";

      (* get the env mapped strings, check that bpc_label is the same for both, make sure they have the same ones in each *)
      val Pi_sys1_tm = List.nth(Pi_tms, 0);
      val Pi_sys2_tm = List.nth(Pi_tms, 1);
      val _ = if identical (dest_birs_state_pc Pi_sys1_tm) (dest_birs_state_pc Pi_sys2_tm) then () else
        raise ERR "birs_Pi_merge_2_RULE" "the two states have to agree in their label terms";
      val varnames = birs_env_varnames Pi_sys1_tm;
      val _ = if list_eq_contents gen_eq varnames (birs_env_varnames Pi_sys2_tm) then () else
              raise ERR "birs_Pi_merge_2_RULE" "the two states do not have the same variables mapped in the environment";

      (* for each mapped variable: *)
      val thm_env = List.foldl (fn (vn, thm0) =>
        let
          val _ = if not debug_mode then () else print ("start a mapping:" ^ vn ^ "\n");
          (* move the mapping to the top *)
          val thm1 = CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV vn)) thm0;
          val exp1 = (snd o get_birs_Pi_first_env_top_mapping o concl) thm1;
          val thm2 = birs_Pi_rotate_two_RULE thm1;
          val thm3 = CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV vn)) thm2;
          val exp2 = (snd o get_birs_Pi_first_env_top_mapping o concl) thm3;
          val _ = if not debug_mode then () else print "got the expressions\n";

          val thm4 = birs_Pi_first_env_top_mapping_merge exp2 exp1 thm3;
          val _ = if not debug_mode then () else print "fixed the mapping\n";
        in thm4 end) thm varnames;
      val _ = if not debug_mode then () else print "unified envs\n";

      (* also unify the two path conditions *)
      (* TODO: probably better to unify the path conditions first, then we can use the common path condition to massage both environments together *)
      val thm_env_pcond =
        let
          val thm0 = thm_env;
          val pcond1 = (get_birs_Pi_first_pcond o concl) thm0;
          val thm1 = birs_Pi_rotate_two_RULE thm0;
          val pcond2 = (get_birs_Pi_first_pcond o concl) thm1;

          (* get conjuncts as list *)
          val pcond1l = dest_bandl pcond1;
          val pcond2l = dest_bandl pcond2;

          (* find the common conjuncts by greedily collecting what is identical in both *)
          val pcond_commonl = list_commons term_id_eq pcond1l pcond2l;
          val pcond_common = bslSyntax.bandl pcond_commonl;

          (* fix the path condition in both states accordingly *)
          val thm2 = (birs_Pi_first_pcond_RULE pcond_common o birs_Pi_rotate_two_RULE o birs_Pi_first_pcond_RULE pcond_common) thm1;
        in thm2 end;
      val _ = if not debug_mode then () else print "unified pcond\n";

      (* merge the first two states in the HOL4 pred_set *)
      (* (TODO: maybe need to prove that they are equal because they are not syntactically identical) *)
      (*
      val rewrite_thm = ISPECL (((fn x => List.take (x, 2)) o pred_setSyntax.strip_set o get_birs_Pi o concl) thm_env_pcond) INSERT_INSERT_EQ_thm;
      (*val _ = print_thm rewrite_thm;*)
      val rewrite_thm_fix = CONV_RULE (CHANGED_CONV (QUANT_CONV (LAND_CONV (*aux_setLib.birs_state_EQ_CONV*)EVAL))) rewrite_thm;
      val thm_merged = CONV_RULE (CHANGED_CONV (birs_Pi_CONV (REWRITE_CONV [rewrite_thm_fix]))) thm_env_pcond;*)
      val thm_merged = CONV_RULE (CHANGED_CONV (birs_Pi_CONV (REWRITE_CONV [ISPEC ((get_birs_Pi_first o concl) thm_env_pcond) pred_setTheory.INSERT_INSERT]))) thm_env_pcond
        handle _ => (print_thm thm_env_pcond; raise ERR "birs_Pi_merge_2_RULE" "merging did not work");
      (*
      val _ = print "\n\nmerged:\n";
      val _ = print_thm thm_merged;
      *)
      val _ = if not debug_mode then () else print "eliminated one from Pi\n";
      val _ = holba_miscLib.timer_stop
        (fn delta_s => print ("  merging two in Pi took " ^ delta_s ^ "\n")) timer;
    in
      thm_merged
    end;

  (* merging of all states in Pi *)
  fun birs_Pi_merge_RULE_ thm =
    (* recursion, go over all the Pi states until there is only one left *)
    if (get_birs_Pi_length o concl) thm < 2 then
      thm
    else
      birs_Pi_merge_RULE_ (birs_Pi_merge_2_RULE thm);
  
  fun birs_Pi_merge_RULE thm =
    let
      val _ = birs_check_norm_thm ("birs_Pi_merge_RULE", "") thm;
      val merged_thm = birs_Pi_merge_RULE_ thm;

      (* check that the path condition has only changed in ways we want *)
      val pcond_sysl = (dest_bandl o get_birs_sys_pcond o concl) merged_thm;
      val pcond_Pifl = (dest_bandl o get_birs_Pi_first_pcond o concl) merged_thm;
      val pcond_sys_extral = list_minus term_id_eq pcond_sysl pcond_Pifl;
      val pcond_Pif_extral = list_minus term_id_eq pcond_Pifl pcond_sysl;
      fun check_extra extra =
        if (length extra = 0) orelse ((length extra = 1) andalso (birsSyntax.is_BExp_IntervalPred (hd extra))) then () else
        raise ERR "birs_Pi_merge_RULE" ("should be none or exactly one conjunct that is a BExp_IntervalPred, something is wrong:" ^ (term_to_string (bslSyntax.bandl extra)));
      val _ = check_extra pcond_sys_extral;
      val _ = check_extra pcond_Pif_extral;
    in
      merged_thm
    end;

  (*
  TODO later: add interval handling (as general as possible, but for now also ok to focus on countw alone)
  - have interval hol4 predicate
  - squash conjuncts that are only related to the latest free symbol intro and connect to previous interval
  - widen the intervals (for now only have one)
  *)

end (* local *)

end (* struct *)
