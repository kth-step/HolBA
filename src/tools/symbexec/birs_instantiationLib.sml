structure birs_instantiationLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;
  open birs_conseqLib;

  (* error handling *)
  val libname = "birs_instantiationLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)


(* ---------------------------------------------------------------------------------------- *)

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
    fun symb_to_rename_map bv_symb =
      let
        val rename_vn = get_renamesymb_name ();
        val ty = (snd o bir_envSyntax.dest_BVar) bv_symb;
      in
        (bv_symb, bir_envSyntax.mk_BVar_string (rename_vn, ty))
      end;
    fun set_renamesymb_counter i = renamesymb_counter := i;

    (*
    (* TODO later (instantiate): rename all variables *)
    fun birs_sound_rename_all_RULE thm =
      let
        (* collect what to rename from the initial environment mapping, should be all just variables, skip renaming of the pathcondition *)
      in
        ()
      end;
    *)

    (* find necessary iunstantiations for birs_sound_symb_inst_RULE *)
    fun birs_find_symb_exp_map bv_syp_gen state B_thm =
      let
        (* take first env and pcond of target state *)
        val (_,A_env,_,A_pcond) = dest_birs_state state;

        (* construct symb_exp_map *)
        fun get_default_bv (vn,exp) =
          let
            val ty = bir_exp_typecheckLib.get_type_of_bexp exp;
          in
            (snd o dest_eq o concl o EVAL) ``bir_senv_GEN_bvar ^(pairSyntax.mk_pair (vn,ty))``
          end;
        val A_env_mappings = get_env_mappings A_env;
        val A_env_mappings_wsymbs = List.map (fn (x,y) => (x,get_default_bv(x,y),y)) A_env_mappings;
        val A_symb_mappings = List.map (fn (_,x,y) => (x,y)) A_env_mappings_wsymbs;
        val A_symb_mappings_changed = List.filter (fn (x,y) => not (identical (bslSyntax.bden x) y)) A_symb_mappings; (* do not need to instantiate what does not change *)
        val symb_exp_map = (bv_syp_gen, A_pcond)::A_symb_mappings_changed;

        (* check that initial state of B_thm does map these symbols in the same way (assuming B_sys_tm is in birs_gen_env standard form) *)
        val B_sys_tm = (get_birs_sys o concl) B_thm;
        val (_,B_env,_,_) = dest_birs_state B_sys_tm;
        val B_env_mappings = get_env_mappings B_env
          handle _ => raise ERR "birs_find_symb_exp_map" "cannot get env_mappings of B_thm";
        val B_env_mappings_expected = List.map (fn (x,y,_) => (x, bslSyntax.bden y)) A_env_mappings_wsymbs;
        val _ = if list_eq_contents (fn (x,y) => pair_eq identical identical x y) B_env_mappings B_env_mappings_expected then () else
          raise ERR "birs_find_symb_exp_map" "the environment of B_thm is unexpected";

        (* better add renaming of all the remaining symbols (practically that is free symbols) to avoid capture issues elsewhere *)
        val symbs_mapped_list = List.map fst symb_exp_map;
        val freesymbs_in_B =
          let
            val B_Pi_tm = (get_birs_Pi o concl) B_thm;
            val freevars_thm = bir_vars_ofLib.birs_freesymbs_DIRECT_CONV (mk_birs_freesymbs (B_sys_tm, B_Pi_tm));
          in
            (pred_setSyntax.strip_set o snd o dest_eq o concl) freevars_thm
          end;
      in
        (List.map symb_to_rename_map freesymbs_in_B, symb_exp_map)
      end;
  end

  (* the instantiation function *)
  fun birs_sound_symb_basic_subst_oracle symb_exp_map thm =
    let
      val _ = birs_check_norm_thm ("birs_sound_symb_basic_subst_oracle", "") thm;

      (* for now a function that does all at once and "cheats" *)
      val s = List.map (fn (bv_symb,exp) => ((bslSyntax.bden bv_symb) |-> exp)) symb_exp_map;
      val thm2_tm = (subst s o concl) thm;
    in
      aux_moveawayLib.mk_oracle_preserve_tags [thm] "BIRS_SYMB_INST_RENAME_SUBST" thm2_tm
    end;

  val birs_subst1_oracle_speed = ref true;
  fun birs_symb_subst1_CONV tm =
    if !birs_subst1_oracle_speed then
      let
        val (subst_tm, state_tm) = birsSyntax.dest_birs_symb_subst1 tm;
        val (alpha_tm, bexp_tm) = pairSyntax.dest_pair subst_tm;
        val s = [bslSyntax.bden alpha_tm |-> bexp_tm];
        val thm_tm = mk_eq (tm, subst s state_tm);
      in
        aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_SYMB_SUBST" thm_tm
      end
    else
      let
        (* TODO: when fixing this, better implement for multisubst and have subst1 as special case *)
        val subst1_conv = EVAL THENC REWRITE_CONV [GSYM birs_auxTheory.BExp_IntervalPred_def]; (* TODO big TODO, also: reverting BExp_IntervalPred_def only needed for pcond *)
        val env_subst1_conv =
          REWR_CONV birs_auxTheory.birs_symb_env_subst1_gen_env_thm THENC
          RAND_CONV (listLib.MAP_CONV EVAL); (* TODO: ? *)

        val conv =
          REWR_CONV bir_symb_soundTheory.birs_symb_subst1_REWR_thm THENC
          birs_auxLib.GEN_match_conv birsSyntax.is_birs_symb_env_subst1 env_subst1_conv THENC
          birs_auxLib.GEN_match_conv bir_exp_substitutionsSyntax.is_bir_exp_subst1 subst1_conv;
        val thm = conv tm;
      in
        thm
      end;
  val birs_symb_subst1_CONV = Profile.profile "0_birs_symb_subst1_CONV" (birs_symb_subst1_CONV);

  val bir_var_type_EQ_CONV =
    LAND_CONV (REWR_CONV bir_envTheory.bir_var_type_def) THENC
    RAND_CONV (REWR_CONV bir_envTheory.bir_var_type_def) THENC
    REWR_CONV boolTheory.REFL_CLAUSE (*aux_setLib.bir_type_EQ_CONV*);
  val rule_RENAME_oracle_speed = ref true; (* TODO: oracle switch unused, remove later *)
  fun birs_sound_symb_rename_RULE symb_symb_map thm =
    (*if !rule_RENAME_oracle_speed then
      birs_sound_symb_basic_subst_oracle (List.map (fn (bv_symb,bv_symb') => (bv_symb, bslSyntax.bden bv_symb')) symb_symb_map) thm
    else*)
      let
        val _ = birs_check_norm_thm ("birs_sound_symb_rename_RULE", "") thm;
        fun birs_sound_symb_rename1 (alpha1_tm, alpha2_tm) thm =
          if identical alpha1_tm alpha2_tm then (print "warning: trying to rename to itself - "; print_term alpha1_tm; print "\n"; thm) else
          let
            open bir_envSyntax;
            open bir_vars_ofLib;
            open aux_setLib;
            open birs_utilsLib;
            fun symb_assump_conv errstr conv =
              NEG_CONV (
                RAND_CONV (conv) THENC
                pred_setLib.IN_CONV bir_var_EQ_CONV
              ) THENC (
                fn tm =>
                  if identical T tm then
                    ALL_CONV tm
                  else
                    (print ("birs_sound_symb_rename1: symbol check failed, "^errstr^", "^(term_to_string alpha1_tm)^", "^(term_to_string alpha2_tm)^"\n"); ALL_CONV tm)
              );

            val bty_tm = mk_eq (mk_bir_var_type alpha1_tm, mk_bir_var_type alpha2_tm);
            val type_thm = prove(bty_tm, CONV_TAC bir_var_type_EQ_CONV)
              handle e => (print "\n\nrule_RENAME type_thm failed:\n"; print_term (bty_tm); print "\n\n\n"; raise e);
            (*val _ = print_thm type_thm;*)
            val thm1 = MATCH_MP (MATCH_MP birs_rulesTheory.birs_rule_RENAME1_spec_thm thm) type_thm
              handle e => (print "\n\nrule_RENAME thm1 failed:\n"; print_thm thm; print "\n\n\n"; raise e);
            (*val _ = print_thm thm1;*)
            val thm2 = MP (CONV_RULE (LAND_CONV (symb_assump_conv "birs" birs_symb_symbols_DIRECT_CONV)) thm1) TRUTH
              handle e => (print "\n\nrule_RENAME thm2 failed:\n"; print_thm thm1; print "\n\n\n"; raise e);
            (*val _ = print_thm thm2;*)
            val thm3 = MP (CONV_RULE (LAND_CONV (symb_assump_conv "birs_set" birs_symb_symbols_set_DIRECT_CONV)) thm2) TRUTH
              handle e => (print "\n\nrule_RENAME thm3 failed:\n"; print_thm thm2; print "\n\n\n"; raise e);
            (*val _ = print_thm thm3;*)
            val thm4 =
              CONV_RULE (
                birs_sys_CONV (birs_symb_subst1_CONV) THENC
                birs_Pi_CONV (pred_setLib.IMAGE_CONV (birs_symb_subst1_CONV) (birs_state_EQ_CONV))
              ) thm3
              handle e => (print "\n\nrule_RENAME thm4 failed:\n"; print_thm thm3; print "\n\n\n"; raise e);
          in
            thm4
          end;
      in
        List.foldr (fn (s,t) => birs_sound_symb_rename1 s t) thm symb_symb_map
      end;
  val birs_sound_symb_rename_RULE = fn x => Profile.profile "1_birs_sound_symb_rename_RULE" (birs_sound_symb_rename_RULE x);

  fun birs_sound_symb_rename_free_RULE symb_symb_map thm =
    (*if !rule_RENAME_oracle_speed then
      birs_sound_symb_basic_subst_oracle (List.map (fn (bv_symb,bv_symb') => (bv_symb, bslSyntax.bden bv_symb')) symb_symb_map) thm
    else*)
      let
        val _ = birs_check_norm_thm ("birs_sound_symb_rename_free_RULE", "") thm;
        fun birs_sound_symb_rename1_free (alpha1_tm, alpha2_tm) thm =
          if identical alpha1_tm alpha2_tm then (print "warning: trying to rename to itself - "; print_term alpha1_tm; print "\n"; thm) else
          let
            open bir_envSyntax;
            open bir_vars_ofLib;
            open aux_setLib;
            open birs_utilsLib;
            fun symb_assump_conv errstr conv =
              NEG_CONV (
                RAND_CONV (conv) THENC
                pred_setLib.IN_CONV bir_var_EQ_CONV
              ) THENC (
                fn tm =>
                  if identical T tm then
                    ALL_CONV tm
                  else
                    (print ("birs_sound_symb_rename1_free: symbol check failed, "^errstr^", "^(term_to_string alpha1_tm)^", "^(term_to_string alpha2_tm)^"\n"); ALL_CONV tm)
              );

            val bty_tm = mk_eq (mk_bir_var_type alpha1_tm, mk_bir_var_type alpha2_tm);
            val type_thm = prove(bty_tm, CONV_TAC bir_var_type_EQ_CONV)
              handle e => (print "\n\nrule_RENAME_FREE type_thm failed:\n"; print_term (bty_tm); print "\n\n\n"; raise e);
            (*val _ = print_thm type_thm;*)
            val thm1 = MATCH_MP (MATCH_MP birs_rulesTheory.birs_rule_RENAME1_FREE_spec_thm thm) type_thm
              handle e => (print "\n\nrule_RENAME_FREE thm1 failed:\n"; print_thm thm; print "\n\n\n"; raise e);
            (*val _ = print_thm thm1;*)
            val thm2 = MP (CONV_RULE (LAND_CONV (symb_assump_conv "birs1" birs_symb_symbols_DIRECT_CONV)) thm1) TRUTH
              handle e => (print "\n\nrule_RENAME_FREE thm2 failed:\n"; print_thm thm1; print "\n\n\n"; raise e);
            (*val _ = print_thm thm2;*)
            val thm3 = MP (CONV_RULE (LAND_CONV (symb_assump_conv "birs2" birs_symb_symbols_DIRECT_CONV)) thm2) TRUTH
              handle e => (print "\n\nrule_RENAME_FREE thm3 failed:\n"; print_thm thm1; print "\n\n\n"; raise e);
            (*val _ = print_thm thm3;*)
            val thm4 =
              CONV_RULE (
                birs_Pi_CONV (LAND_CONV (birs_symb_subst1_CONV))
              ) thm3
              handle e => (print "\n\nrule_RENAME_FREE thm4 failed:\n"; print_thm thm3; print "\n\n\n"; raise e);
          in
            thm4
          end;
      in
        List.foldr (fn (s,t) => birs_sound_symb_rename1_free s t) thm symb_symb_map
      end;
  val birs_sound_symb_rename_free_RULE = fn x => Profile.profile "1_birs_sound_symb_rename_free_RULE" (birs_sound_symb_rename_free_RULE x);

  val rule_INST_oracle_speed = ref true;
  fun birs_sound_symb_inst_RULE symb_exp_map thm =
    (* TODO: remove option here to avoid missing checks *)
    if !rule_INST_oracle_speed then
      birs_sound_symb_basic_subst_oracle symb_exp_map thm
    else
      let
        val _ = birs_check_norm_thm ("birs_sound_symb_inst_RULE", "") thm;
        fun birs_sound_symb_inst1 (alpha_tm, bexp_tm) thm =
          let
            open bir_envSyntax;
            open bir_typing_expSyntax;
            open bir_vars_ofLib;
            open aux_setLib;
            open birs_utilsLib;
            fun symb_assump_conv conv =
              (
                RAND_CONV (conv) THENC
                pred_setLib.IN_CONV bir_var_EQ_CONV
              );
            
            val bty_conv =
              LAND_CONV bir_exp_typecheckLib.type_of_bir_exp_DIRECT_CONV THENC
              RAND_CONV (RAND_CONV (REWR_CONV bir_envTheory.bir_var_type_def)) THENC
              REWR_CONV boolTheory.REFL_CLAUSE
              (*IFC
                (REWR_CONV optionTheory.SOME_11)
                (aux_setLib.bir_type_EQ_CONV)
                (REWRITE_CONV [GSYM optionTheory.NOT_SOME_NONE])*);
            val bty_tm = mk_eq (mk_type_of_bir_exp bexp_tm, optionSyntax.mk_some (mk_bir_var_type alpha_tm));
            val type_thm = prove(bty_tm, CONV_TAC (bty_conv))
              handle e => (print "\n\nrule_INST type_thm failed:\n"; print_term (bty_tm); print "\n\n\n"; raise e);
            (*val _ = print_thm type_thm;*)
            val thm1 = MATCH_MP (MATCH_MP birs_rulesTheory.birs_rule_INST1_thm thm) type_thm
              handle e => (print "\n\nrule_INST thm1 failed:\n"; print_thm thm; print "\n\n\n"; raise e);
            (*val _ = print_thm thm1;*)
            val thm2 = MP (CONV_RULE (LAND_CONV (symb_assump_conv birs_symb_symbols_DIRECT_CONV)) thm1) TRUTH
              handle e => (print "\n\nrule_INST thm2 failed:\n"; print_term alpha_tm;(* print_thm thm1;*) print "\n\n\n"; raise e);
            (*val _ = print_thm thm2;*)
            val thm3 = MP (CONV_RULE (LAND_CONV (birs_freesymbs_gen_CONV bir_vars_ofLib.bir_vars_of_exp_DIRECT_CONV)) thm2) TRUTH
              handle e => (print "\n\nrule_INST thm3 failed:\n"; print_term alpha_tm;(* print_thm thm2;*) print "\n\n\n"; raise e);
            (*val _ = print_thm thm3;*)
            val thm4 =
              CONV_RULE (
                birs_sys_CONV (birs_symb_subst1_CONV) THENC
                birs_Pi_CONV (pred_setLib.IMAGE_CONV (birs_symb_subst1_CONV) (birs_state_EQ_CONV))
              ) thm3
              handle e => (print "\n\nrule_INST thm4 failed:\n"; print_thm thm3; print "\n\n\n"; raise e);
          in
            thm4
          end;

        (* NOTE: since we rename one by one, order of instantiation matters, etc. *)
        (* solution: rename all symbols that get instantiated at first
           - TODO: make renaming first an option
           - maybe not necessary with current applications *)
        val symb_symb_exp_map = List.map (fn (s,e) => (s, snd (symb_to_rename_map s), e)) symb_exp_map;
        val symb_symb_map = List.map (fn (s1,s2,_) => (s1, s2)) symb_symb_exp_map;
        val symb_exp_map_ren = List.map (fn (_,s2,e) => (s2, e)) symb_symb_exp_map;
        val thm_ren = birs_sound_symb_rename_RULE symb_symb_map thm;

        val thm_ = List.foldr (fn (s,t) => birs_sound_symb_inst1 s t) thm_ren symb_exp_map_ren;
      in
        thm_
      end;
  val birs_sound_symb_inst_RULE = fn x => Profile.profile "1_birs_sound_symb_inst_RULE" (birs_sound_symb_inst_RULE x);

  (*
  instantiation for state
  *)
  fun birs_sound_inst_RULE bv_syp_gen state B_thm =
    let
      val (_,_,_,A_pcond) = dest_birs_state state;

      val _ = print ("applying instantiation\n");
      val timer = holba_miscLib.timer_start 0;

      open birs_auxTheory;

      (* identify instantiation needed for B, assumes to take the first state in Pi of A,
          - environment mappings
          - the generic path condition symbol bv_syp_gen
          - renaming of all free symbols for good measure (must be done first) *)
      val (symb_symb_map,symb_exp_map) = birs_find_symb_exp_map bv_syp_gen state B_thm;
      (*val _ = List.map (fn (bv_symb,exp) => (print_term bv_symb; print "|->\n"; print_term exp; print "\n")) symb_exp_map;
      val _ = print "\n";
      val _ = print_term state;
      val _ = print "\n";*)

      (* rename all *)
      val B_thm_rename = birs_sound_symb_rename_RULE symb_symb_map B_thm;
      (* instantiate all *)
      val B_thm_inst = birs_sound_symb_inst_RULE symb_exp_map B_thm_rename;

      (* take care of path conditions (after instantiating bv_syp_gen) *)
      (* ------- *)
      (* use path condition implication with z3 to remove the summary conjuncts from sys
         (only keep the conjunct corresponding to the original path condition symbol
            NOTE: to be sound and possible, this conjunct must be stronger than what was there already) *)
        (* take first Pi state of A, env and pcond *)
      val B_thm_inst_sys = birs_sys_pcond_RULE A_pcond B_thm_inst;

      (* TODO: can only handle one Pi state, for now *)
      val _ = if len_of_thm_Pi B_thm_inst_sys = 1 then () else
        raise ERR "birs_sound_inst_RULE" "summaries can only contain 1 state currently";
      (* cleanup Pi path conditions (probably only need to consider one for starters) to only preserve non-summary conjunct (as the step before), but preserve also the intervals *)
      val B_Pi_pcond = (get_birs_Pi_first_pcond o concl) B_thm_inst_sys;
      val B_Pi_pcond_intervals = List.filter (is_BExp_IntervalPred) (dest_bandl B_Pi_pcond);
      val B_pcondl_new = B_Pi_pcond_intervals@(list_minus term_id_eq (dest_bandl A_pcond) B_Pi_pcond_intervals);
      val B_Pi_pcond_new = mk_bandl (B_pcondl_new);
      (*
      val _ = print_term (mk_bandl B_Pi_pcond_intervals_);
      val _ = print_term B_Pi_pcond_new;
      val _ = print_thm B_thm_inst_sys;
      *)
      val B_thm_inst_sys_Pi = birs_Pi_first_pcond_RULE B_Pi_pcond_new B_thm_inst_sys;

      (* fix env mapping order *)
      val B_thm_inst_fixed = CONV_RULE (birs_sys_CONV (birs_env_set_order_CONV (birs_env_varnames state))) B_thm_inst_sys_Pi;

      (* check that the initial state of B_thm_inst_fixed is indeed what we intended to get *)
      val _ = if identical state ((get_birs_sys o concl) B_thm_inst_fixed) then () else
        raise ERR "birs_sound_inst_RULE" "instantiation failed, initial state of instantiated theorem not identical with target state";

      val _ = holba_miscLib.timer_stop
        (fn delta_s => print ("  applying instantiation took " ^ delta_s ^ "\n")) timer;
    in
      B_thm_inst_fixed
    end;
  val birs_sound_inst_RULE = fn x => fn y => Profile.profile "birs_sound_inst_RULE" (birs_sound_inst_RULE x y);

  (*
  instantiation process (including sequential composition)
  *)
  fun birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm bv_syp_gen A_thm B_thm =
    let
      val _ = birs_check_compatible A_thm B_thm;

      val A_Pi_sys_tm = (get_birs_Pi_first o concl) A_thm;

      val B_inst_thm = birs_sound_inst_RULE bv_syp_gen A_Pi_sys_tm B_thm;

      (* sequential composition of the two theorems *)
      val seq_thm = birs_composeLib.birs_rule_SEQ_fun birs_rule_SEQ_thm A_thm B_inst_thm;
    in
      seq_thm
    end;

end (* local *)

end (* struct *)
