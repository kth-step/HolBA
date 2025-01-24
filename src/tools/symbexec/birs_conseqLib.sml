structure birs_conseqLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;
  open birs_utilsLib;
  open aux_setLib;

  open bir_vars_ofLib;

  (* error handling *)
  val libname = "birs_conseqLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  val birs_state_acc_CONV = REWRITE_CONV [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM];

in (* local *)

  val rule_CONSEQ_oracle_speed = ref true;

  (* TODO: update the one in composeLib with this *)
  fun birs_freesymbs_gen_CONV conv =
      LAND_CONV (LAND_CONV (conv)) THENC
      LAND_CONV (RAND_CONV (birs_freesymbs_DIRECT_CONV)) THENC
      LAND_CONV (varset_INTER_CONV) THENC
      REWRITE_CONV [pred_setTheory.EMPTY_SUBSET];

  val birs_freesymbs_CONV = birs_freesymbs_gen_CONV birs_symb_symbols_DIRECT_CONV;

(* ---------------------------------------------------------------------------------------- *)

  (*
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
      val pcond1l = dest_bandl pcond1;
      val pcond2l = dest_bandl pcond2;

      (* find the common conjuncts by greedily collecting what is identical in both *)
      val imp_is_ok = list_inclusion term_id_eq pcond2l pcond1l;
    in
      if imp_is_ok then
        SOME (mk_oracle_thm "BIRS_CONJ_INCL_IMP" ([], imp_tm))
      else
        NONE
    end;
    *)

(* ---------------------------------------------------------------------------------------- *)

  (* general path condition weakening with z3 (to throw away path condition conjuncts (to remove branch path condition conjuncts)) *)
  fun birs_Pi_first_pcond_RULE pcond_new thm =
    if !rule_CONSEQ_oracle_speed then
      let
        val _ = birs_check_norm_thm ("birs_Pi_first_pcond_RULE", "") thm;

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
        (*
        val pcond_drop_ok = isSome (is_DROP_R_imp imp_tm) orelse
                            isSome (is_DROP_L_imp imp_tm) orelse
                            isSome (is_conjunct_inclusion_imp imp_tm);
        *)
        val pcond_imp_ok = (*pcond_drop_ok orelse*)
                           isSome (check_imp_tm imp_tm
                           handle e => (print "smt query failed:\n"; print_term imp_tm; print "\n"; raise e));
        val _ = if pcond_imp_ok then () else
                (print "widening failed, path condition is not weaker\n";
                raise ERR "birs_Pi_first_pcond_RULE" "the supplied path condition is not weaker");
      in
        aux_moveawayLib.mk_oracle_preserve_tags [thm] "BIRS_WIDEN_PCOND" (mk_birs_symb_exec (p_tm, mk_sysLPi (sys_tm,L_tm,Pi_new_tm)))
      end
      handle e => (print "birs_Pi_first_pcond_RULE_oracle :: widening failed\n"; raise e)
    else
      let
        val _ = birs_check_norm_thm ("birs_Pi_first_pcond_RULE", "") thm;

        val thm1 = Profile.profile "zzz_1_matchmp" (MATCH_MP birs_rulesTheory.birs_rule_WIDEN_spec_thm2) thm;
        val thm11 = Profile.profile "zzz_2_stateacc" (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV birs_state_acc_CONV))) thm1;
        (*val _ = print_thm thm11;*)
        val imp_tm_land = (rand o rator o fst o dest_imp o snd o strip_forall o concl) thm11;
        (*val _ = print_term imp_tm_land;*)
        (*val imp_tm_land_thm = Profile.profile "zzz_2_stateacc" birs_state_acc_CONV imp_tm_land;*)
        (*val _ = print_thm imp_tm_land_thm;*)

        val imp_tm = mk_birs_exp_imp (imp_tm_land, pcond_new);
        (*
        val _ = print_term imp_tm;
        val _ = holba_z3Lib.debug_print := true;
        val _ = print "sending a z3 query\n";
        *)
        val imp_thm_o = check_imp_tm imp_tm
                           handle e => (print "smt query failed:\n"; print_term imp_tm; print "\n"; raise e);
        val pcond_imp_ok = isSome (imp_thm_o);
        val _ = if pcond_imp_ok then () else
                (print "widening failed, path condition is not weaker\n";
                raise ERR "birs_Pi_first_pcond_RULE" "the supplied path condition is not weaker");
        (* use the bir implication theorem to justify the new theorem *)
        val imp_thm = (*CONV_RULE (LAND_CONV (K (GSYM imp_tm_land_thm)))*) (valOf imp_thm_o);
        (*val _ = print_thm imp_thm;*)
        val thm2 = Profile.profile "zzz_4_mp" (MP (Profile.profile "zzz_3_spec" (SPEC pcond_new) thm11)) imp_thm;
        (*val _ = print_thm thm2;
        val _ = print "\n\n\n\n";*)
        (*val thm3 = Profile.profile "zzz_4_delete" (CONV_RULE (birs_Pi_CONV (RAND_CONV aux_setLib.birs_state_DELETE_CONV))) thm2;*)
        val thm3 = Profile.profile "zzz_5_stateacc" (CONV_RULE (birs_Pi_CONV (LAND_CONV birs_state_acc_CONV))) thm2;
        (*CONV_RULE (birs_Pi_CONV ((LAND_CONV birs_state_acc_CONV) THENC
          (*cannot do this, merging relies on unchanged Pi: aux_setLib.birs_state_INSERT_DELETE_CONV*)
          RAND_CONV aux_setLib.birs_state_DELETE_CONV)) thm2;*)
        (*val _ = print_thm thm3;*)
      in
        thm3
      end
      handle e => (print "birs_Pi_first_pcond_RULE_prove :: widening failed\n"; raise e);
  val birs_Pi_first_pcond_RULE = fn x => Profile.profile "rule_CONS_WIDEN" (birs_Pi_first_pcond_RULE x);

  fun birs_Pi_first_pcond_drop drop_right thm =
    let
      open bir_expSyntax;
      open bir_exp_immSyntax;
      val Pi_sys_tm = (get_birs_Pi_first o concl) thm;
      val pcond = dest_birs_state_pcond Pi_sys_tm;
      val _ = if is_BExp_BinExp pcond then () else
              raise ERR "birs_Pi_first_pcond_drop" "pcond must be a BinExp";
      val (bop,be1,be2) = dest_BExp_BinExp pcond;
      val _ = if is_BIExp_And bop then () else
              raise ERR "birs_Pi_first_pcond_drop" "pcond must be an And";
      val pcond_new =
        if drop_right then
          be1
        else
          be2;
    in
      birs_Pi_first_pcond_RULE pcond_new thm
    end
    handle e => (print "birs_Pi_first_pcond_drop failed\n"; raise e);

(* ---------------------------------------------------------------------------------------- *)

  (* general path condition strengthening with z3 *)
  fun birs_sys_pcond_RULE pcond_new thm =
    if !rule_CONSEQ_oracle_speed then
      let
        val _ = birs_check_norm_thm ("birs_sys_pcond_RULE", "") thm;

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
        val pcond_imp_ok = isSome (check_imp_tm imp_tm);
        val _ = if pcond_imp_ok then () else
                (print "narrowing failed, path condition is not stronger\n";
                raise ERR "birs_sys_pcond_RULE" "the supplied path condition is not stronger");
      in
        aux_moveawayLib.mk_oracle_preserve_tags [thm] "BIRS_NARROW_PCOND" (mk_birs_symb_exec (p_tm, mk_sysLPi (sys_new_tm,L_tm,Pi_tm)))
      end
    else
      let
        val _ = birs_check_norm_thm ("birs_sys_pcond_RULE", "") thm;

        (*
        val (p_tm, tri_tm) = (dest_birs_symb_exec o concl) thm;
        val (sys_old_tm,L_tm,Pi_tm) = dest_sysLPi tri_tm;

        val (pc, env, status, pcond_old) = dest_birs_state sys_old_tm;
        val sys_new_tm = mk_birs_state (pc, env, status, pcond_new);
        *)

        val thm1 = CONV_RULE birs_state_acc_CONV (MATCH_MP birs_rulesTheory.birs_rule_NARROW_spec_thm2 thm);
        val imp_tm_rand = (rand o fst o dest_imp o snd o strip_forall o concl) thm1;
        (*val _ = print_term imp_tm_rator;*)
        (*val imp_tm_rand_thm = birs_state_acc_CONV imp_tm_rand;*)
        (*val _ = print_thm imp_tm_rator_thm;*)

        val imp_tm = mk_birs_exp_imp (pcond_new, imp_tm_rand(*(rhs o concl) imp_tm_rand_thm*));
        (*val _ = print_term imp_tm;*)

        (*
        val _ = print_term imp_tm;
        val _ = holba_z3Lib.debug_print := true;
        val _ = print "sending a z3 query\n";
        *)
        val imp_thm_o = check_imp_tm imp_tm;
        val pcond_imp_ok = isSome (imp_thm_o);
        val _ = if pcond_imp_ok then () else
                (print "narrowing failed, path condition is not stronger\n";
                raise ERR "birs_sys_pcond_RULE" "the supplied path condition is not stronger");
        val imp_thm = (*CONV_RULE (RAND_CONV (K (GSYM imp_tm_rand_thm)))*) (valOf imp_thm_o);
        (*val _ = print_thm imp_thm;*)
        val thm2 = MATCH_MP thm1 imp_thm;
        (*val _ = print_thm thm2;
        val _ = print "\n\n\n\n";*)
        val thm3 = MP (CONV_RULE (LAND_CONV birs_freesymbs_CONV) thm2) TRUTH
          handle e => (print "birs_sys_pcond_RULE :: freesymbol proof failed\n"; raise e);
        (*val _ = print_thm thm3;*)
      in
        thm3
      end
      handle e => (print "birs_sys_pcond_RULE :: narrowing failed\n"; raise e);
  val birs_sys_pcond_RULE = fn x => Profile.profile "rule_CONS_NARROW" (birs_sys_pcond_RULE x);

end (* local *)

end (* struct *)
