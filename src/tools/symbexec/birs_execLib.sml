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
      REWRITE_RULE
          [bir_symbTheory.recordtype_birs_state_t_seldef_bsst_pc_def,
          (*bir_symbTheory.birs_state_t_accessors,*)
          bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM];
  in
    fun birs_rule_STEP_fun birs_rule_STEP_thm bstate_tm =
      let
        val step1_thm = SPEC bstate_tm birs_rule_STEP_thm;
        val (step2_thm, extra_info) = birs_exec_step_CONV_fun (concl step1_thm);
        val birs_exec_thm = EQ_MP step2_thm step1_thm;

        val single_step_prog_thm = Profile.profile "birs_rule_STEP_fun_overhead" exec_step_postproc_fun birs_exec_thm;

        (*val _ = print_thm single_step_prog_thm;*)
        val _ = if symb_sound_struct_is_normform (concl single_step_prog_thm) then () else
                (print_term (concl single_step_prog_thm);
                raise ERR "birs_rule_STEP_fun" "something is not right, the produced theorem is not evaluated enough");
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
        val step2_thm = Profile.profile "birs_rule_STEP_SEQ_fun_overhead" exec_step_postproc_fun step1_thm;

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
  fun birs_try_prune opstring failaction prune_thm single_step_prog_thm =
    let
      val continue_thm_o_1 =
        SOME (MATCH_MP prune_thm single_step_prog_thm)
        handle _ => NONE;
      val continue_thm_o_2 =
        Option.mapPartial (prove_assumptions false EVAL) continue_thm_o_1
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
      thm;
  val birs_rule_tryjustassert_fun = fn x => Profile.profile "birs_rule_tryjustassert_fun" (birs_rule_tryjustassert_fun x);

  fun birs_rule_tryprune_fun prune_thm thm =
    birs_try_prune "tryprune" NONE prune_thm thm;
  val birs_rule_tryprune_fun = fn x => Profile.profile "birs_rule_tryprune_fun" (birs_rule_tryprune_fun x);

  (* ============================================================================ *)

  (* mapped environment expression simplifications (for example after assignments)
      NOTE: it is faster to run the simplification function on theorems with singleton Pi
        (because then there is no need to run set operations afterwards) *)
  (* ----------------------------------------------- *)
  (* first prepare the SUBST rule for prog *)
  fun birs_rule_SUBST_prog_fun bprog_tm =
    let
      open birs_rulesTheory;
      val inst_thm1 = SIMP_RULE std_ss [] (ISPEC bprog_tm birs_rule_SUBST_thm);
      val inst_thm2 = SIMP_RULE std_ss [] (ISPEC bprog_tm birs_rule_SUBST_spec_thm);
    in
      (inst_thm1, inst_thm2)
    end;

  local
    val symbexp_prim_tm = ``symbexp':bir_exp_t``;
    (* Pi is "bs2' INSERT (Pi DELETE bs2)"*)
    val cleanup_Pi_conv =
      let
        open pred_setLib;
        open aux_setLib;
      in
        RAND_CONV (DELETE_CONV birs_state_EQ_CONV)
      end;
    val cleanup_RULE = CONV_RULE (birs_Pi_CONV cleanup_Pi_conv);
    fun birs_rule_SUBST_trysimp_first_fun (SUBST_thm,SUBST_SING_thm) birs_simp_fun thm =
      let
        val is_sing = (get_birs_Pi_length o concl) thm = 1;
        val birs_rule_SUBST_thm = if is_sing then SUBST_SING_thm else SUBST_thm;
        val postproc = if is_sing then I else cleanup_RULE;

        val assignment_thm_o =
          SOME (MATCH_MP birs_rule_SUBST_thm thm)
          handle _ => NONE;

        val simp_t_o = Option.mapPartial (fn assignment_thm =>
          let
            val simp_tm = (fst o dest_imp o concl o SPEC symbexp_prim_tm) assignment_thm;
            (*val timer_exec_step_p3 = holba_miscLib.timer_start 0;*)
            val simp_t = birs_simp_fun simp_tm;
            (*val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> SUBST in " ^ delta_s ^ "\n")) timer_exec_step_p3;*)
          in
            SOME (simp_t, assignment_thm)
          end) assignment_thm_o;
      in
        case simp_t_o of
          SOME (simp_t, assignment_thm) =>
            postproc (MATCH_MP assignment_thm simp_t)
        | NONE => thm
      end;
    val birs_rule_SUBST_trysimp_first_fun = fn x => fn y => Profile.profile "birs_rule_SUBST_trysimp_first_fun" (birs_rule_SUBST_trysimp_first_fun x y);
  in
    fun birs_rule_SUBST_trysimp_fun x y = birs_Pi_each_RULE (birs_rule_SUBST_trysimp_first_fun x y);
  end

end (* local *)

end (* struct *)
