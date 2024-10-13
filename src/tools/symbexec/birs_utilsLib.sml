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

  fun list_minus eq_fun l1 l2 =
    List.filter (fn x => not (list_in eq_fun x l2)) l1;

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

  (* function to get the length of Pi *)
  val get_birs_Pi_length =
    (length o pred_setSyntax.strip_set o get_birs_Pi);

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

  val birs_exp_imp_DROP_R_thm = prove(``
    !be1 be2.
    birs_exp_imp (BExp_BinExp BIExp_And be1 be2) be1
  ``,
    (* maybe only true for expressions of type Bit1 *)
    cheat
  );
  val birs_exp_imp_DROP_L_thm = prove(``
    !be1 be2.
    birs_exp_imp (BExp_BinExp BIExp_And be1 be2) be2
  ``,
    (* maybe only true for expressions of type Bit1 *)
    cheat
  );

  fun is_DROP_R_imp imp_tm =
    (SOME (UNCHANGED_CONV (REWRITE_CONV [birs_exp_imp_DROP_R_thm]) imp_tm)
            handle _ => NONE);

  fun is_DROP_L_imp imp_tm =
    (SOME (UNCHANGED_CONV (REWRITE_CONV [birs_exp_imp_DROP_L_thm]) imp_tm)
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
      val _ = holba_z3Lib.debug_print := true;
      val _ = print "sending a z3 query\n";
      *)
      val pcond_drop_ok = isSome (is_DROP_R_imp imp_tm) orelse
                          isSome (is_DROP_L_imp imp_tm) orelse
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

  fun birs_Pi_first_pcond_drop drop_right thm =
    let
      val Pi_sys_tm_free = (get_birs_Pi_first o concl) thm;
      val (_,_,_,pcond_old) = dest_birs_state Pi_sys_tm_free;
      val sel_fun =
        if drop_right then
          (snd o dest_comb o fst o dest_comb)
        else
          (snd o dest_comb);
      val pcond_new = sel_fun pcond_old;

      (* debug printout *)
      (*val _ = print_thm thm;*)
      (*
      val _ = print "\npcond before: \n";
      val _ = print_term pcond_old;
      val _ = print "\npcond after: \n";
      val _ = print_term pcond_new;
      *)
    in
      birs_Pi_first_pcond_RULE pcond_new thm
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
      (*
      val _ = print_term imp_tm;
      val _ = holba_z3Lib.debug_print := true;
      val _ = print "sending a z3 query\n";
      *)
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
    fun sys_CONV conv =
      LAND_CONV conv;
    fun Pi_CONV conv =
      RAND_CONV (RAND_CONV conv);
    val first_CONV =
      LAND_CONV;
    fun second_CONV conv =
      RAND_CONV (first_CONV conv);

    local
      open pred_setSyntax;
      val rotate_first_INSERTs_thm = prove(``
        !x1 x2 xs.
        (x1 INSERT x2 INSERT xs) = (x2 INSERT x1 INSERT xs)
      ``,
        cheat
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
          (* TODO: the result of this should actually just be inst_thm *)
          REWRITE_CONV [Once inst_thm] tm
        end;

      fun rotate_INSERTs_conv tm =
        (if not (is_two_INSERTs tm) then REFL else
         (rotate_two_INSERTs_conv THENC
          RAND_CONV rotate_INSERTs_conv)) tm;
    end
  in
    (* apply state transformer to sys *)
    fun birs_sys_CONV conv tm =
      let
        val _ = if symb_sound_struct_is_normform tm then () else
                raise ERR "birs_sys_CONV" "term is not a standard birs_symb_exec";
      in
        (struct_CONV (sys_CONV conv)) tm
      end;

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
    fun birs_Pi_rotate_two_RULE thm =
      let
        (*val _ = print "rotating first two in Pi\n";*)
        val _ = if (symb_sound_struct_is_normform o concl) thm then () else
                raise ERR "birs_Pi_rotate_two_RULE" "theorem is not a standard birs_symb_exec";
        val (_,_,Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) thm;
        val num_Pi_el = (length o pred_setSyntax.strip_set) Pi_tm;
        val _ = if num_Pi_el > 1 then () else
                raise ERR "birs_Pi_rotate_two_RULE" "Pi has to have at least two states";

        val res_thm = CONV_RULE (struct_CONV (Pi_CONV (rotate_two_INSERTs_conv))) thm;
        (*val _ = print "finished rotating\n";*)
      in
        res_thm
      end;

    fun birs_Pi_rotate_RULE thm =
      let
        (*val _ = print "rotating elements of Pi\n";*)
        val _ = if (symb_sound_struct_is_normform o concl) thm then () else
                raise ERR "birs_Pi_rotate_RULE" "theorem is not a standard birs_symb_exec";
        val (_,_,Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) thm;
        val num_Pi_el = (length o pred_setSyntax.strip_set) Pi_tm;
        val _ = if num_Pi_el > 1 then () else
                raise ERR "birs_Pi_rotate_RULE" "Pi has to have at least two states";

        val res_thm = CONV_RULE (struct_CONV (Pi_CONV (rotate_INSERTs_conv))) thm;
        (*val _ = print "finished rotating\n";*)
      in
        res_thm
      end;
  end

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

end (* local *)

end (* struct *)
