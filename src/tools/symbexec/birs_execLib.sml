structure birs_execLib =
struct

local
  open HolKernel Parse boolLib bossLib;

  open birsSyntax;
  open birs_stepLib;


  (* error handling *)
  val libname = "bir_execLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in


(* halt free programs *)
(* ----------------------------------------------- *)
(*
val bprog_tm = bprog;
*)
fun bir_prog_has_no_halt_fun bprog_tm =
  let
    (* prep step rule to be used *)
    (*
    val bir_prog_has_no_halt_prog_thm = store_thm(
       "bir_prog_has_no_halt_prog_thm", *)
    val bir_prog_has_no_halt_prog_thm = prove(``
      bir_prog_has_no_halt ^bprog_tm
    ``,
      EVAL_TAC
    );
  in
    bir_prog_has_no_halt_prog_thm
  end;

(*
val bprog_tm = bprog;
val no_halt_thm = (bir_prog_has_no_halt_fun bprog_tm)
*)
fun birs_rule_STEP_prog_fun no_halt_thm =
  let
    val prep_thm = 
      MATCH_MP birs_rulesTheory.birs_rule_STEP_gen2_thm no_halt_thm;
(*
    val _ = (print_term o concl) prep_thm;
*)
  in
    prep_thm
  end;

(* plugging in the execution of steps to obtain sound structure *)
(* ----------------------------------------------- *)
local
  open birs_auxTheory;
in
fun birs_rule_STEP_fun birs_rule_STEP_thm bstate_tm =
  let
    val step1_thm = SPEC bstate_tm birs_rule_STEP_thm;
    val (step2_thm, extra_info) = birs_exec_step_CONV_fun (concl step1_thm);
    val birs_exec_thm = EQ_MP step2_thm step1_thm;

    val timer_exec_step_p3 = holba_miscLib.timer_start 0;
    (* TODO: optimize *)
    val single_step_prog_thm =
      REWRITE_RULE
        [bir_symbTheory.recordtype_birs_state_t_seldef_bsst_pc_def,
         bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM]
        birs_exec_thm;

    val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> STEP in " ^ delta_s ^ "\n")) timer_exec_step_p3;

    (*val _ = print_thm single_step_prog_thm;*)
    val _ = if symb_sound_struct_is_normform (concl single_step_prog_thm) then () else
            (print_term (concl single_step_prog_thm);
             raise ERR "birs_rule_STEP_fun" "something is not right, the produced theorem is not evaluated enough");
  in
    (single_step_prog_thm, extra_info)
  end;
end;
val birs_rule_STEP_fun = fn x => Profile.profile "birs_rule_STEP_fun" (birs_rule_STEP_fun x);



(* TODO: justify the second branch of assert is infeasible (need precondition for this) *)
(* TODO: simplify path condition in poststate to get rid of the implied and not accumulate it *)
(* TODO: clean up environment after assignment to not accumulate useless mappings *)
(* TODO: maybe have a specialized assert/assignment step function? (optimization to detect this situation directly, maybe better as separate function?) *)

(*
val pcond_tm = ``
               BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
                 (BExp_UnaryExp BIExp_Not
                    (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))))
``;
*)

(* stepping a sound structure, try to justify assert *)
(* ----------------------------------------------- *)
(*
val bstate_tm = birs_state_init_tm;
*)
local
  open birs_auxTheory;

  open birs_rulesTheory;

  open bir_smtLib;

  fun justify_assumption_EVAL t =
    if (not o is_imp o concl) t then
      raise ERR "justify_assumption_EVAL" "not an implication"
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm = (EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "justify_assumption_EVAL" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "justify_assumption_EVAL" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        (REWRITE_RULE [assmpt_thm] t)
      end;

  val birs_pcondinf_tm = ``birs_pcondinf``;
in
fun birs_rule_tryjustassert_fun force_assert_justify single_step_prog_thm =
  let
    (*
    val single_step_prog_thm = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm;
    *)
    val continue_thm_o_1 =
      SOME (MATCH_MP assert_spec_thm single_step_prog_thm)
      handle _ => NONE;
    val continue_thm_o_2 =
      Option.map (justify_assumption_EVAL) continue_thm_o_1
      handle _ => NONE;
  in
    (* val SOME continue_thm = continue_thm_o; *)
    case continue_thm_o_2 of
       SOME continue_thm =>
        let
    val timer_exec_step_p3 = holba_miscLib.timer_start 0;
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (*val _ = print_term pcond_tm;*)
          val pcond_is_contr = bir_smt_check_unsat false pcond_tm;
          val _ = if (not force_assert_justify) orelse pcond_is_contr then () else
            (print "\n\n\n<<<<<<<<<<<< ASSERTION MAY FAIL <<<<<<<<<<<< \n";
             print_term (concl single_step_prog_thm);
             print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";
             raise ERR "birs_rule_tryjustassert_fun" "can't prove assertion to hold");
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], mk_comb (birs_pcondinf_tm, pcond_tm)))
            else
              NONE;
    val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> tryassert in " ^ delta_s ^ "\n")) timer_exec_step_p3;
        in
          (* val SOME pcond_thm = pcond_thm_o; *)
          case pcond_thm_o of
             SOME pcond_thm => MP continue_thm pcond_thm
           | _ => single_step_prog_thm
        end
     | _ => single_step_prog_thm
  end;
val birs_rule_tryjustassert_fun = fn x => Profile.profile "birs_rule_tryjustassert_fun" (birs_rule_tryjustassert_fun x);

fun birs_rule_tryprune_fun prune_thm single_step_prog_thm =
  let
    (* val _ = print "try prune now \n"; *)
    val continue_thm_o_1 =
      SOME (MATCH_MP prune_thm single_step_prog_thm)
      handle _ => NONE;
    val continue_thm_o_2 =
      Option.map (fn t => (print "going into pruning\n"; (*print_thm t; *)justify_assumption_EVAL t)) continue_thm_o_1
      handle _ => NONE;
  in
    case continue_thm_o_2 of
       SOME continue_thm =>
        let
    val timer_exec_step_p3 = holba_miscLib.timer_start 0;
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (* val _ = print_term pcond_tm; *)
          val pcond_is_contr = bir_smt_check_unsat false pcond_tm;
	  val _ = if pcond_is_contr then print "can prune" else ();
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], mk_comb (birs_pcondinf_tm, pcond_tm)))
            else
              NONE;
    val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> tryprune2 in " ^ delta_s ^ "\n")) timer_exec_step_p3;
        in
          case pcond_thm_o of
             SOME pcond_thm =>
	     let
               val res = MP continue_thm pcond_thm;
               val _ = print "pruning finished\n";
               (*val _ = print_thm res;*)
	     in
	       res
	     end
           | _ => single_step_prog_thm
        end
     | _ => single_step_prog_thm
  end;
end;
val birs_rule_tryprune_fun = fn x => Profile.profile "birs_rule_tryprune_fun" (birs_rule_tryprune_fun x);


(* stepping a sound structure, try to simplify after assignment *)
(* ----------------------------------------------- *)
(* first prepare the SUBST rule for prog *)
fun birs_rule_SUBST_prog_fun bprog_tm =
  let
    open birs_rulesTheory;
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    (*
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
    val ARB_val_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_ARB_val_sound_thm;
    val birs_symb_ARB_val_sound_prog_thm =
      (SPEC (bprog_tm) ARB_val_sound_thm);

    val prep_thm =
      MATCH_MP
        (MATCH_MP symb_rule_SUBST_SING_thm birs_symb_symbols_f_sound_prog_thm)
        birs_symb_ARB_val_sound_prog_thm;

    val inst_thm = prove(``
         !sys L lbl envl status pcond vn symbexp symbexp'.
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>}) ==>
           birs_simplification pcond symbexp symbexp' ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>})
      ``,
        cheat (* TODO: connect this with prep_thm from above *)
      );*)
    val inst_thm = SIMP_RULE std_ss [] ((SPEC bprog_tm o INST_TYPE [Type.alpha |-> prog_type]) birs_rule_SUBST_spec_thm);
    (*val _ = (print_term o concl) inst_thm;*)
  in
    inst_thm
  end;


(*
val single_step_prog_thm = result;
*)
fun birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm birs_simp_fun single_step_prog_thm =
  let
    val assignment_thm_o =
      SOME (MATCH_MP birs_rule_SUBST_thm single_step_prog_thm)
      handle _ => NONE;

    val simp_t_o = Option.mapPartial (fn assignment_thm =>
      let
        val simp_tm = (fst o dest_imp o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl o Q.SPEC `symbexp'`) assignment_thm;
        (*val _ = print_term simp_tm;*)
    val timer_exec_step_p3 = holba_miscLib.timer_start 0;
        val simp_t = birs_simp_fun simp_tm;
        (* TODO: need to remove the following line later and enable the simp function above *)
        (*val simp_t_o = NONE;*)
    val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> SUBST in " ^ delta_s ^ "\n")) timer_exec_step_p3;
      in
        SOME (simp_t, assignment_thm)
      end) assignment_thm_o;
  in
    case simp_t_o of
       SOME (simp_t, assignment_thm) => MATCH_MP assignment_thm simp_t
     | NONE => single_step_prog_thm
  end;
val birs_rule_SUBST_trysimp_fun = fn x => Profile.profile "birs_rule_SUBST_trysimp_fun" (birs_rule_SUBST_trysimp_fun x);

end (* local *)

end (* struct *)
