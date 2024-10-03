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
      val pcond_imp_ok = isSome (birs_simpLib.check_imp_tm imp_tm);
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

  fun list_distinct _ [] = true
    | list_distinct eq_fun (x::xs) =
        if all (fn y => (not o eq_fun) (x, y)) xs then list_distinct eq_fun xs else false;

  local
    (* the following two functions are from test-z3-wrapper.sml *)
    fun list_inclusion eq_fun l1 l2 =
      foldl (fn (x, acc) => acc andalso (exists (fn y => eq_fun (x, y)) l2)) true l1;

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
      in
        CONV_RULE (struct_CONV (Pi_CONV (REWRITE_CONV [inst_thm]))) thm
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

  (* function to get the first Pi state *)
  fun get_birs_Pi_first tm =
    let
      val (_, tri_tm) = dest_birs_symb_exec tm;
      val (_,_,Pi_tm) = dest_sysLPi tri_tm;
      val (Pi_sys_tm, _) = pred_setSyntax.dest_insert Pi_tm;
    in
      Pi_sys_tm
    end;

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
  fun birs_Pi_first_forget_RULE symbname thm =
    let
      (*val _ = print "forgetting first mapping in first of Pi\n";*)
      (* find the expression mapped at the top of env *)
      val Pi_sys_tm = (get_birs_Pi_first o concl) thm;
      val (_,env,_,pcond) = dest_birs_state Pi_sys_tm;
      val (_,exp) = get_env_top_mapping env;

      (* "free symbol" the expression *)
      val free_thm = birs_Pi_first_freesymb_RULE symbname exp thm;
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
                         raise ERR "birs_Pi_first_forget_RULE" "something uncaught");
    in
      forget_thm
    end

(* ---------------------------------------------------------------------------------------- *)

  (* helper functions for merge, merging of mapped expressions *)
  (* -------------------- *)

  (* TODO:  - initial implementation: just forget. then test this whole thing before moving on *)
  fun birs_Pi_first_env_top_mapping_merge_forget thm =
    let
      val symbname = get_freesymb_name ();
    in
      (birs_Pi_first_forget_RULE symbname o birs_Pi_rotate_RULE o birs_Pi_first_forget_RULE symbname) thm
    end;

  (*   - do something special for store operations, cannot just forget the whole thing *)
  (*     - maybe just unfold them into a list and assume they are all disjunct memory locations, can reuse code from the cheated store-store simplification *)
  (*   - later need to do something special about countw here too *)

  (* - choose how to deal with the expressions at hand *)
  fun birs_Pi_first_env_top_mapping_merge exp1 exp2 thm =
    let
      (* choose the merging approach: not touch if they are syntactically identical (or semantically, when checked with z3 under the respective path conditions), store operation, interval, others *)
      (* TODO: store operation and interval *)
    in
      if identical exp1 exp2 then thm else
      birs_Pi_first_env_top_mapping_merge_forget thm
    end;

  (* the merge function for the first two Pi states *)
  fun birs_Pi_merge_2_RULE thm =
    let
      val _ = print "merging the first two in Pi\n";
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
      (* merge the first two states in the HOL4 pred_set *)
      val _ = print "eliminating one from Pi\n";
      (* (TODO: maybe need to prove that they are equal because they are not syntactically identical) *)
      val thm_merged = CONV_RULE (birs_Pi_CONV (REWRITE_CONV [ISPEC ((get_birs_Pi_first o concl) thm_env_pcond) pred_setTheory.INSERT_INSERT])) thm_env_pcond;
      val _ = print "eliminated one from Pi\n";
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
