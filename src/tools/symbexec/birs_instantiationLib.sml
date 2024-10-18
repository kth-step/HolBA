structure birs_instantiationLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;

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
    fun birs_find_symb_exp_map bv_syp_gen A_thm B_thm =
      let
        (* take first Pi state of A, env and pcond *)
        val A_Pi_sys_tm = (get_birs_Pi_first o concl) A_thm;
        val (_,A_env,_,A_pcond) = dest_birs_state A_Pi_sys_tm;

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
        fun symb_to_rename_map bv_symb =
          let
            val rename_vn = get_renamesymb_name ();
            val ty = (snd o bir_envSyntax.dest_BVar) bv_symb;
          in
            (bv_symb, bslSyntax.bden (bir_envSyntax.mk_BVar_string (rename_vn, ty)))
          end;
      in
        (List.map symb_to_rename_map freesymbs_in_B)@symb_exp_map
      end;
  end

  (* the instantiation function *)
  fun birs_sound_symb_inst_RULE symb_exp_map thm =
    let
      val _ = birs_check_norm_thm ("birs_sound_symb_inst_RULE", "") thm;

      (* for now a function that does all at once and cheats, either sml substitution (for simplicity and speed, double-check the documentation to make sure that it is an "all-at-once substitution") or bir expression substitution and EVAL *)
      val s = List.map (fn (bv_symb,exp) => ((bslSyntax.bden bv_symb) |-> exp)) symb_exp_map;
      val thm2_tm = (subst s o concl) thm;
      (* TODO: later have a subfunction that does one by one (hopefully not too slow)
               rename all symbols before instantiating to avoid capturing some! (birs_sound_rename_all_RULE), NOTE: only need this if rename one by one *)
    in
      mk_oracle_thm "BIRS_SYMB_INST_RENAME" ([], thm2_tm)
    end;

  (*
  instantiation process (including sequential composition)
  *)
  fun birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm bv_syp_gen A_thm B_thm =
    let
      val _ = birs_check_compatible A_thm B_thm;
      val A_Pi_sys_tm = (get_birs_Pi_first o concl) A_thm;
      val (_,_,_,A_pcond) = dest_birs_state A_Pi_sys_tm;
      val len_of_thm_Pi = get_birs_Pi_length o concl;

      open birs_auxTheory;

      (* identify instantiation needed for B, assumes to take the first state in Pi of A,
          - environment mappings
          - the generic path condition symbol bv_syp_gen
          - renaming of all free symbols for good measure *)
      val symb_exp_map = birs_find_symb_exp_map bv_syp_gen A_thm B_thm;
      (*val _ = List.map (fn (bv_symb,exp) => (print_term bv_symb; print "|->\n"; print_term exp; print "\n")) symb_exp_map;*)

      (* instantiate all *)
      val B_thm_inst = birs_sound_symb_inst_RULE symb_exp_map B_thm;

      (* take care of path conditions (after instantiating bv_syp_gen) *)
      (* ------- *)
      (* use path condition implication with z3 to remove the summary conjuncts from sys
         (only keep the conjunct corresponding to the original path condition symbol
            NOTE: to be sound and possible, this conjunct must be stronger than what was there already) *)
        (* take first Pi state of A, env and pcond *)
      val B_thm_inst_sys = birs_sys_pcond_RULE A_pcond B_thm_inst;

      (* TODO: can only handle one Pi state, for now *)
      val _ = if len_of_thm_Pi B_thm_inst_sys = 1 then () else
        raise ERR "birs_sound_inst_SEQ_RULE" "summaries can only contain 1 state currently";
      (* cleanup Pi path conditions (probably only need to consider one for starters) to only preserve non-summary conjunct (as the step before), but preserve also the intervals *)
      val B_Pi_pcond = (get_birs_Pi_first_pcond o concl) B_thm_inst_sys;
      val B_Pi_pcond_intervals = List.filter (is_BExp_IntervalPred) (dest_bandl B_Pi_pcond);
      val B_pcondl_new = B_Pi_pcond_intervals@(list_minus term_id_eq (dest_bandl A_pcond) B_Pi_pcond_intervals);
      val B_Pi_pcond_new = bslSyntax.bandl (B_pcondl_new);
      (*
      val _ = print_term (bslSyntax.bandl B_Pi_pcond_intervals_);
      val _ = print_term B_Pi_pcond_new;
      val _ = print_thm B_thm_inst_sys;
      *)
      val B_thm_inst_sys_Pi = birs_Pi_first_pcond_RULE B_Pi_pcond_new B_thm_inst_sys;

      (* sequential composition of the two theorems *)
      val seq_thm = birs_composeLib.birs_rule_SEQ_fun birs_rule_SEQ_thm A_thm B_thm_inst_sys_Pi;

      (* check that the resulting Pi set cardinality is A - 1 + B *)
      val _ = if len_of_thm_Pi A_thm - 1 + len_of_thm_Pi B_thm_inst_sys_Pi = len_of_thm_Pi seq_thm then () else
        raise ERR "birs_sound_inst_SEQ_RULE" "somehow the states did not merge in Pi";
    in
      seq_thm
    end;

end (* local *)

end (* struct *)
