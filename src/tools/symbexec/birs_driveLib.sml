structure birs_driveLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;
  open birs_composeLib;

  (* error handling *)
  val libname = "birs_driveLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  datatype symbexec_tree_t =
    Symb_Node of (thm  * (symbexec_tree_t list));

  fun reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm, [])) = symbex_A_thm
    | reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm, (symbex_B_subtree::symbex_B_subtrees))) =
        let
          val symbex_B_thm = reduce_tree SEQ_fun_spec symbex_B_subtree;
          val symbex_A_thm_new = SEQ_fun_spec symbex_A_thm symbex_B_thm
              handle ex =>
                (print "\n=========================\n\n";
                (print_term o concl) symbex_A_thm;
                print "\n\n";
                (print_term o concl) symbex_B_thm;
                print "\n\n=========================\n";
                raise ex);
        in
          reduce_tree SEQ_fun_spec (Symb_Node (symbex_A_thm_new, symbex_B_subtrees))
        end;

  fun take_step exec_funs st =
    let
      (*val _ = print ("Executing one more step @(" ^ (term_to_string (dest_birs_state_pc st)) ^ ")\n");*)
      val (fetch, _, step, _) = exec_funs;
    in
      case fetch st of
          SOME x => (print "fetched a theorem\n"; x)
        | NONE => step st
    end
    handle ex => (print_term st; raise ex);

  fun take_step_SING exec_funs contfun (st, thm) =
    let
      (*val _ = print ("START sequential composition with singleton mid_state set\n");*)
      val (fetch, step_SING, _, _) = exec_funs;
      fun fetch_w tm =
        fetch tm
        handle ex => (print_term tm; raise ex);
      fun step_SING_w t =
        step_SING t
        handle ex => (print_thm t; raise ex);
    in
      case fetch_w st of
          SOME x => (print "fetched a theorem\n"; Symb_Node (thm, [contfun x]))
        | NONE => contfun (step_SING_w thm)
    end;

  (* PROCESS: give first thm, filter Pi with stop function, first try fetch for all Pi,
          if something is left and it is the only state in Pi overall just step with SING_Pi,
          otherwise go over the rest with step from term
      NOTE: function is not end-recursive (this is to avoid needing to apply the expensive composition right away; and to reiterate the tree)! *)
  fun build_tree_rec exec_funs thm =
    let
      val _ = print ("\n");

      val (_, _, _, is_continue) = exec_funs;
      fun is_executable st =
        birs_state_is_running st andalso
        is_continue st;

      val sts = (get_birs_Pi_list o concl) thm;
      val sts_exec = List.filter is_executable sts;
      (*
      val _ = print ("- have " ^ (Int.toString (length sts)) ^ " states\n");
      val _ = print ("    (" ^ (Int.toString (length sts_exec)) ^ " executable)\n");
      *)

    in
      (* stop condition (no more running states, or reached the stop_lbls) *)
      if List.null sts_exec then
        (print "no executable states left, terminating here\n";
        (Symb_Node (thm,[])))
      else
        (* safety check *)
        if List.null sts then
          raise ERR "build_tree_rec" "this can't happen"
        (* carry out a sequential composition with singleton mid_state set *)
        else if List.length sts = 1 then
          take_step_SING exec_funs (build_tree_rec exec_funs) (hd sts, thm)
        (* continue with executing one step on each branch point... *)
        else
          let
            val _ = print ("continuing only with the executable states\n");
            fun buildsubtree st =
              (print ("starting a branch\n");
              build_tree_rec exec_funs (take_step exec_funs st));
          in
            Symb_Node (thm, List.map buildsubtree sts_exec)
          end
    end;

  fun build_tree exec_funs st =
    (birs_check_state_norm ("build_tree", "") st;
     build_tree_rec exec_funs (take_step exec_funs st));
  (*
  val build_tree = fn (fetch, step_SING, step, is_continue) =>
    build_tree
      (Profile.profile "build_tree_fetch" fetch,
       Profile.profile "build_tree_step_SING" step_SING,
       Profile.profile "build_tree_step" step,
       is_continue);
  *)
    

  fun exec_until (exec_funs, comp_fun) =
    (Profile.profile "reduce_tree" (reduce_tree comp_fun)) o
    (Profile.profile "build_tree" (build_tree exec_funs));

(* ----------------------------------------------------------------------------- *)
  
  fun prep_exec bprog_tm post_step_fun fetch is_continue =
    let
      open birs_execLib;

      val has_no_halt_thm =
        birs_auxLib.get_prog_no_halt_thm bprog_tm;

      val (birs_rule_STEP_thms, birs_rule_STEP_SEQ_thms) =
        birs_rule_STEP_prog_fun has_no_halt_thm;
      val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
      val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;

      val step =
        (post_step_fun (birs_rule_SUBST_thm) o
          birs_rule_STEP_fun birs_rule_STEP_thms);
      val comp_fun = birs_rule_SEQ_fun birs_rule_SEQ_thm;
      val step_SING =
        (post_step_fun (birs_rule_SUBST_thm) o
        birs_rule_STEP_SEQ_fun birs_rule_STEP_SEQ_thms);
      (*
      val fetch = fn _ => NONE;
      (*val fetch = fn x => SOME (step x);*)
      val is_continue = not_stop_lbl birs_end_lbls;
      *)
    in
      ((fetch, step_SING, step, is_continue),
       comp_fun)
    end;

  fun birs_exec_to bprog_tm post_step_fun fetch is_continue birs_state =
    let
      val _ = birs_check_state_norm ("birs_exec_to", "") birs_state;

      val exec_params = prep_exec bprog_tm post_step_fun fetch is_continue;
      val _ = print "now reducing it to one sound structure\n";
      val timer = holba_miscLib.timer_start 0;
      val result = exec_until exec_params birs_state
        handle e => (Profile.print_profile_results (Profile.results ()); raise e);
      val _ = holba_miscLib.timer_stop
        (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;

        (*
        Profile.reset_all ()
        Profile.print_profile_results (Profile.results ())
        Profile.output_profile_results (iostream) (Profile.results ())
        *)
      (*val _ = Profile.print_profile_results (Profile.results ());*)
    in
      result
    end;
  val birs_exec_to = fn x1 => fn x2 => fn x3 => fn x4 => Profile.profile "birs_exec_to" (birs_exec_to x1 x2 x3 x4);

(* ----------------------------------------------------------------------------- *)

  val pcond_gen_symb = ``BVar "syp_gen" (BType_Imm Bit1)``;
  fun mk_pcond_gen pcond =
    let
      (* TODO: check that pcond_gen_symb does not appear in pcond *)
    in
      ``BExp_BinExp BIExp_And (^pcond) (BExp_Den (^pcond_gen_symb))``
    end;

  fun birs_init env pcond init_lbl =
    let
      val _ = birs_check_env_norm ("birs_init", "") env;

      val pcond_is_sat = bir_smtLib.bir_smt_check_sat false pcond;
      val _ = if pcond_is_sat then () else
        raise ERR "birs_init" "initial pathcondition is not satisfiable; it seems to contain a contradiction";

      val st = ``<|
        bsst_pc       := ^init_lbl;
        bsst_environ  := ^env;
        bsst_status   := BST_Running;
        bsst_pcond    := ^(mk_pcond_gen pcond)
      |>``;
    in
      st
    end;

(* ----------------------------------------------------------------------------- *)

  fun gen_birs_env_thm birenvtyl_def =
    let
      open birs_auxTheory;

      val bprog_envtyl_tm = (fst o dest_eq o concl) birenvtyl_def;
    in
      (REWRITE_CONV [birenvtyl_def] THENC
       EVAL THENC
       REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm]) (mk_bir_senv_GEN_list bprog_envtyl_tm)
    end;
  val gen_birs_env = (rhs o concl o gen_birs_env_thm);
  
  fun gen_birs_pcond_thm birenvtyl_def bpre =
    let
      open birs_auxTheory;
      val bprog_envtyl_tm = (fst o dest_eq o concl) birenvtyl_def;

      val mk_bsysprecond_pcond_thm =
        (computeLib.RESTR_EVAL_CONV [birs_eval_exp_tm, birs_gen_env_tm] THENC
         REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm] THENC
         birs_auxLib.GEN_match_conv is_birs_eval_exp birs_stepLib.birs_eval_exp_CONV THENC
         EVAL (*FST (THE (...))*))
        (mk_mk_bsysprecond (bpre, bprog_envtyl_tm));
    in
      mk_bsysprecond_pcond_thm
    end;
  fun gen_birs_pcond birenvtyl_def = (rhs o concl o gen_birs_pcond_thm birenvtyl_def);

  fun birs_analysis_init birenvtyl_def bpre init_lbl =
    birs_init (gen_birs_env birenvtyl_def) (gen_birs_pcond birenvtyl_def bpre) init_lbl;

  (* ----------------------------------------------------------------------------- *)

end (* local *)

end (* struct *)
