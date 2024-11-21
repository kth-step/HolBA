structure birs_execLib =
struct

local
  open HolKernel Parse boolLib bossLib;

  open birsSyntax;
  open birs_utilsLib;
  open birs_stepLib;

  (* error handling *)
  val libname = "bir_execLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

  (* halt free programs *)
  (* ----------------------------------------------- *)
  fun bir_prog_has_no_halt_fun bprog_tm =
    prove(``bir_prog_has_no_halt ^bprog_tm``, EVAL_TAC);

  fun birs_rule_STEP_prog_fun no_halt_thm =
    MATCH_MP birs_rulesTheory.birs_rule_STEP_gen2_thm no_halt_thm;

  (* plugging in the execution of steps to obtain sound structure *)
  (* ----------------------------------------------- *)
  local
    open birs_auxTheory;

    val exec_step_postproc_fun =
      CONV_RULE (birs_L_CONV (LAND_CONV(
        REWRITE_CONV
          [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM]
      )));
  in
    fun birs_rule_STEP_fun birs_rule_STEP_thm bstate_tm =
      let
        val step1_thm = SPEC bstate_tm birs_rule_STEP_thm;
        val (step2_thm, extra_info) = birs_exec_step_CONV_fun (concl step1_thm);
        val birs_exec_thm = EQ_MP step2_thm step1_thm;

        val single_step_prog_thm = exec_step_postproc_fun birs_exec_thm;

        (*val _ = print_thm single_step_prog_thm;*)
        val _ = birs_check_norm_thm ("birs_rule_STEP_fun", "") single_step_prog_thm
          handle e => (print_term (concl single_step_prog_thm); raise e);
      in
        (single_step_prog_thm, extra_info)
      end;
    val birs_rule_STEP_fun = fn x => Profile.profile "birs_rule_STEP_fun" (birs_rule_STEP_fun x);

    (* optimization: take steps if Pi is a singleton set,
        this way we save to compute free symbols and operate on
        Pi sets over and over for the non-branching sequences *)
    (* ----------------------------------------------- *)
    fun birs_rule_STEP_SEQ_fun STEP_SEQ_thm symbex_A_thm =
      let
        val step1_thm = MATCH_MP STEP_SEQ_thm symbex_A_thm;
        val step2_thm = exec_step_postproc_fun step1_thm;

        val (step3_conv_thm, extra_info) = birs_exec_step_CONV_fun (concl step2_thm);
        val step3_thm = EQ_MP step3_conv_thm step2_thm;
      in
        (step3_thm, extra_info)
      end;
    val birs_rule_STEP_SEQ_fun = fn x => Profile.profile "birs_rule_STEP_SEQ_fun" (birs_rule_STEP_SEQ_fun x);
  end

  (* ============================================================================ *)

  (* try to prune, or remove assert branching and the associated pathcondition blowup *)
  (* ----------------------------------------------- *)
  fun birs_try_prune opstring failaction prune_thm assumpt_conv single_step_prog_thm =
    let
      val continue_thm_o_1 =
        SOME (MATCH_MP prune_thm single_step_prog_thm)
        handle _ => NONE;
      val continue_thm_o_2 =
        Option.mapPartial (prove_assumptions false assumpt_conv) continue_thm_o_1
        handle _ => NONE;
    in
      case continue_thm_o_2 of
        SOME continue_thm =>
          let
            val pcondinf_tm = (fst o dest_imp o concl) continue_thm;
            val timer_exec_step_p3 = holba_miscLib.timer_start 0;
            val pcond_thm_o = check_pcondinf_tm pcondinf_tm;
            val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> " ^ opstring ^ " in " ^ delta_s ^ "\n")) timer_exec_step_p3;
            (* val _ = print_term pcondinf_tm; *)
            val pcond_is_contr = isSome pcond_thm_o;
            val _ = if (not (isSome failaction)) orelse pcond_is_contr then () else
              (valOf failaction) ();
          in
            case pcond_thm_o of
              SOME pcond_thm => MP continue_thm pcond_thm
            | _ => single_step_prog_thm
          end
      | _ => single_step_prog_thm
    end;

  fun birs_rule_tryjustassert_fun force thm =
    birs_try_prune
      "tryassert"
      (if force then
        SOME (fn () => (
          print "\n\n\n<<<<<<<<<<<< ASSERTION MAY FAIL <<<<<<<<<<<< \n";
          print_thm thm;
          print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";
          raise ERR "birs_rule_tryjustassert_fun" "can't prove assertion to hold"))
        else
        NONE)
      birs_rulesTheory.assert_spec_thm
      (aux_setLib.DISJR_CONV
        (aux_setLib.NEG_CONV aux_setLib.bir_pc_EQ_CONV)
        (aux_setLib.NEG_CONV aux_setLib.bir_status_EQ_CONV))
      thm;
  val birs_rule_tryjustassert_fun = fn x => Profile.profile "birs_rule_tryjustassert_fun" (birs_rule_tryjustassert_fun x);

  fun birs_rule_tryprune_fun prune_thm =
    birs_try_prune
      "tryprune"
      NONE
      prune_thm
      (aux_setLib.DISJL_CONV
        (aux_setLib.NEG_CONV aux_setLib.bir_pc_EQ_CONV)
        (aux_setLib.NEG_CONV aux_setLib.bir_status_EQ_CONV));
  val birs_rule_tryprune_fun = fn x => Profile.profile "birs_rule_tryprune_fun" (birs_rule_tryprune_fun x);

  (* ============================================================================ *)

  (* mapped environment expression simplifications (for example after assignments)
      NOTE: it is faster to run the simplification function on theorems with singleton Pi
        (because then there is no need to run set operations afterwards) *)
  (* ----------------------------------------------- *)
  (* first prepare the SUBST rule for prog *)
  fun birs_rule_SUBST_prog_fun bprog_tm =
    let
      open pred_setSyntax;
      open birs_rulesTheory;
      val inst_thm1 = SIMP_RULE std_ss [boolTheory.RIGHT_FORALL_IMP_THM] (ISPEC bprog_tm birs_rule_SUBST_thm);
      val inst_thm2 = SIMP_RULE std_ss [boolTheory.RIGHT_FORALL_IMP_THM] (ISPEC bprog_tm birs_rule_SUBST_spec_thm);

      fun assignment_thm_f assignment_thm thm =
        SOME (MATCH_MP assignment_thm thm)
        handle _ => NONE;
      
      fun assignment_thm_spec_f thm =
        let
          val (sys_tm, L_tm, Pi_tm) = (get_birs_sysLPi o concl) thm;
          val (sysPi_tm, remPi_tm) = dest_insert Pi_tm;
          val (pc, env, status, pcond) = dest_birs_state sysPi_tm;
          val envl = dest_birs_gen_env env;
          val (mapping, envl) = listSyntax.dest_cons envl;
          val (vn, symbexp) = pairSyntax.dest_pair mapping;

          val spec_list = [sys_tm, L_tm, pc, status, pcond, envl, vn, symbexp];
          val spec_thm =
            if is_empty remPi_tm then
              Profile.profile "assignment_thm_f_inst1" (SPECL spec_list) inst_thm2
            else
              Profile.profile "assignment_thm_f_inst2" (SPECL (spec_list@[remPi_tm])) inst_thm1;
          val res = MP spec_thm thm;
        in
          SOME res
        end
        handle _ => NONE;
      fun exp_fun v1 v2 x =
        let
          val r1 = Profile.profile "birs_rule_SUBST_prog_fun_v1" v1 x;
          val r2 = Profile.profile "birs_rule_SUBST_prog_fun_v2" v2 x;
          val _ = if option_eq (fn x => fn y => identical (concl x) (concl y)) r1 r2 then ()
            else raise (Profile.profile "birs_rule_SUBST_prog_fun_v_mismatch" print "birs_rule_SUBST_prog_fun::results don't match\n"; ERR "birs_rule_SUBST_prog_fun" "results don't match");
        in
          r1
        end;
    in
      (*assignment_thm_f inst_thm1, assignment_thm_f inst_thm2*)
      (*assignment_thm_spec_f, assignment_thm_spec_f*)
      (exp_fun
        (assignment_thm_f inst_thm1)
        assignment_thm_spec_f,
       exp_fun
        (assignment_thm_f inst_thm2)
        assignment_thm_spec_f)
    end;

  local
    (* Pi is "bs2' INSERT (Pi DELETE bs2)"*)
    val cleanup_Pi_conv =
      let
        open pred_setLib;
        open aux_setLib;
      in
        RAND_CONV (DELETE_CONV birs_state_EQ_CONV)
      end;
    val cleanup_RULE = CONV_RULE (birs_Pi_CONV cleanup_Pi_conv);
    fun combine_simp_t assignment_thm simp_t =
      MP (SPEC ((snd o dest_comb o concl) simp_t) assignment_thm) simp_t;
    fun birs_rule_SUBST_trysimp_first_fun (*assignment_thm_f*)(SUBST_thm_f, SUBST_SING_thm_f) birs_simp_fun thm =
      let
        val is_sing = (aux_setLib.is_sing o get_birs_Pi o concl) thm;
        val assignment_thm_f = if is_sing then SUBST_SING_thm_f else SUBST_thm_f;
        val postproc = if is_sing then I else cleanup_RULE;

        val assignment_thm_o = assignment_thm_f thm;

        val simp_t_o = Option.map (fn assignment_thm =>
          let
            val simp_tm = (fst o dest_imp o snd o dest_forall o concl) assignment_thm;
            val simp_t = birs_simp_fun simp_tm;
          in
            postproc (combine_simp_t assignment_thm simp_t)
          end) assignment_thm_o;
      in
        Option.getOpt(simp_t_o, thm)
      end;
    val birs_rule_SUBST_trysimp_first_fun = fn x => fn y => Profile.profile "birs_rule_SUBST_trysimp_first_fun" (birs_rule_SUBST_trysimp_first_fun x y);
  in
    fun birs_rule_SUBST_trysimp_fun x y = birs_Pi_each_RULE (birs_rule_SUBST_trysimp_first_fun x y);
  end

end (* local *)

end (* struct *)
