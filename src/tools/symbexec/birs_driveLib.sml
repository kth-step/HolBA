structure birs_driveLib =
struct

local

open HolKernel Parse boolLib bossLib;

open birsSyntax;
open birs_stepLib;
open birs_composeLib;
open birs_auxTheory;

  (* error handling *)
  val libname = "birs_driveLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(*
val tm = ``<|bsst_pc := a;
             bsst_environ :=b;
             bsst_status := BST_AssertionViolated;
             bsst_pcond := c|>``;
val tm = ``<|bsst_pc := a;
             bsst_environ :=b;
             bsst_status := BST_Running;
             bsst_pcond := c|>``;
*)
fun birs_get_pc tm =
  let
    val (pc, _, _, _) = dest_birs_state tm;
  in
    pc
  end;
fun birs_is_running tm =
  let
    val (_, _, status, _) = dest_birs_state tm;
  in
    identical status bir_programSyntax.BST_Running_tm
  end;

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



(*
val SUBST_thm = birs_rule_SUBST_thm;
val STEP_SEQ_thm = birs_rule_STEP_SEQ_thm;
val symbex_A_thm = single_step_A_thm;
*)
fun birs_rule_STEP_SEQ_fun STEP_SEQ_thm symbex_A_thm =
  let
    val step1_thm = MATCH_MP STEP_SEQ_thm symbex_A_thm;
    val step2_thm = REWRITE_RULE [bir_symbTheory.birs_state_t_accessors, bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM] step1_thm;

    (*
    val timer_exec_step_p3 = holba_miscLib.timer_start 0;
    *)

    val (step3_conv_thm, extra_info) = birs_exec_step_CONV_fun (concl step2_thm);
    val step3_thm = EQ_MP step3_conv_thm step2_thm;

    (*
    val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> STEP_SEQ in " ^ delta_s ^ "\n")) timer_exec_step_p3;
    *)
    val step4_thm = (* (birs_rule_SUBST_trysimp_fun SUBST_thm o birs_rule_tryjustassert_fun true) *) step3_thm;
  in
    (step4_thm, extra_info)
  end;
val birs_rule_STEP_SEQ_fun = fn x => Profile.profile "birs_rule_STEP_SEQ_fun" (birs_rule_STEP_SEQ_fun x);


(*
val STEP_fun_spec = birs_rule_STEP_fun_spec;
val SEQ_fun_spec = birs_rule_SEQ_fun_spec;
val STEP_SEQ_fun_spec = birs_rule_STEP_SEQ_fun_spec;

val symbex_A_thm = single_step_A_thm;
val stop_lbls = birs_stop_lbls;
*)
fun build_tree (STEP_fun_spec, SEQ_fun_spec, STEP_SEQ_fun_spec) symbex_A_thm stop_lbls =
  let
    val _ = print ("\n");
    val (_, _, Pi_A_tm) = (symb_sound_struct_get_sysLPi_fun o concl) symbex_A_thm;

    fun is_executable st =
      birs_is_running st andalso (not (List.exists (identical (birs_get_pc st)) stop_lbls));

    val birs_states_mid = symb_sound_struct_Pi_to_birstatelist_fun Pi_A_tm;
    (*
    val birs_states_mid_running = List.filter birs_is_running birs_states_mid;
    *)
    val birs_states_mid_executable = List.filter is_executable birs_states_mid;
    (*
    val _ = print ("- have " ^ (Int.toString (length birs_states_mid)) ^ " states\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_running)) ^ " running)\n");
    val _ = print ("    (" ^ (Int.toString (length birs_states_mid_executable)) ^ " executable)\n");
    *)

    fun take_step birs_state_mid =
      let
        val _ = print ("Executing one more step @(" ^ (term_to_string (birs_get_pc birs_state_mid)) ^ ")\n");
        val single_step_B_thm = STEP_fun_spec birs_state_mid;
      in
        single_step_B_thm
      end
      handle ex => (print_term birs_state_mid; raise ex);
  in
    (* stop condition (no more running states, or reached the stop_lbls) *)
    if List.length birs_states_mid_executable = 0 then
      (print "no executable states left, terminating here\n";
       (Symb_Node (symbex_A_thm,[])))
    else
      (* safety check *)
      if List.length birs_states_mid < 1 then
        raise Fail "build_tree_until_branch::this can't happen"
      (* carry out a sequential composition with singleton mid_state set *)
      else if List.length birs_states_mid = 1 then
        let

          val _ = print ("START sequential composition with singleton mid_state set\n");

          (*
          val birs_state_mid = hd birs_states_mid;
          val timer_exec_step_P1 = holba_miscLib.timer_start 0;
          val single_step_B_thm = take_step birs_state_mid;
          val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>> executed a whole step in " ^ delta_s ^ "\n")) timer_exec_step_P1;
          *)
          val timer_exec_step_P2 = holba_miscLib.timer_start 0;
          val bprog_composed_thm = STEP_SEQ_fun_spec symbex_A_thm;
          val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>> FINISH took and sequentially composed a step in " ^ delta_s ^ "\n")) timer_exec_step_P2;

        in
          build_tree (STEP_fun_spec, SEQ_fun_spec, STEP_SEQ_fun_spec) bprog_composed_thm stop_lbls
        end
      (* continue with executing one step on each branch point... *)
      else
        let
          val _ = print ("continuing only with the executable states\n");
          (*
          val birs_state_mid = hd birs_states_mid_executable;
          *)
          fun buildsubtree birs_state_mid =
            let
              val _ = print ("starting a branch\n");
              val single_step_B_thm = take_step birs_state_mid;
            in
              build_tree (STEP_fun_spec, SEQ_fun_spec, STEP_SEQ_fun_spec) single_step_B_thm stop_lbls
            end
        in
          Symb_Node (symbex_A_thm, List.map buildsubtree birs_states_mid_executable)
        end
  end;

fun exec_until (STEP_fun_spec, SEQ_fun_spec, STEP_SEQ_fun_spec) symbex_A_thm stop_lbls =
  let
    val tree = Profile.profile "build_tree" (build_tree (STEP_fun_spec, SEQ_fun_spec, STEP_SEQ_fun_spec) symbex_A_thm) stop_lbls;
  in
    Profile.profile "reduce_tree" (reduce_tree SEQ_fun_spec) tree
  end;

fun bir_symb_exec_to (bprog_tm, birs_post_step_fun) birs_end_lbls birs_state =
  let
   val _ = if birs_state_is_normform_gen false birs_state then () else
           raise ERR "bir_symb_exec_to" "state is not in standard form with birs_gen_env";

   open birs_execLib;

   val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_STEP_fun_spec =
     (birs_post_step_fun o
      birs_rule_STEP_fun birs_rule_STEP_thm);
   (* now the composition *)
   val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
   val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
   val single_step_A_thm = birs_rule_STEP_fun_spec birs_state;
   (*val _ = print_thm single_step_A_thm;*)
   (* and also the sequential composition *)
   val birs_rule_STEP_SEQ_thm = MATCH_MP
    birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm
    (bir_prog_has_no_halt_fun bprog_tm);
   val birs_rule_STEP_SEQ_fun_spec =
    (birs_post_step_fun o
     birs_rule_STEP_SEQ_fun birs_rule_STEP_SEQ_thm);

   val _ = print "now reducing it to one sound structure\n";
   val timer = holba_miscLib.timer_start 0;
   val result = exec_until
     (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec)
     single_step_A_thm birs_end_lbls
     handle e => (Profile.print_profile_results (Profile.results ()); raise e);
   val _ = holba_miscLib.timer_stop
    (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;

    (*
    Profile.reset_all ()
    Profile.print_profile_results (Profile.results ())
    Profile.output_profile_results (iostream) (Profile.results ())
    *)
   val _ = Profile.print_profile_results (Profile.results ());
  in
   result
  end;

end (* local *)

end (* struct *)
