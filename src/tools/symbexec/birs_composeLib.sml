structure birs_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open bir_vars_ofLib;

  open birsSyntax;
  open birs_auxTheory;
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "bir_symb_composeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

  (* first prepare the SEQ rule for prog *)
  fun birs_rule_SEQ_prog_fun bprog_tm =
    (ISPEC (bprog_tm) birs_rulesTheory.birs_rule_SEQ_gen_thm, bprog_tm);

  (* symbol freedom helper function *)
  (* has to solve this ((birs_symb_symbols bsys_A) INTER (birs_freesymbs bsys_B bPi_B) = EMPTY) *)
  val speedcheat_SEQ_freesymbcheck = ref false;
  fun birs_rule_SEQ_INTER_freesymbs_fun freesymbols_tm =
   let
    val freesymbols_thm = prove(freesymbols_tm,
      (if !speedcheat_SEQ_freesymbcheck then cheat else ALL_TAC) >> 

      CONV_TAC (LAND_CONV (LAND_CONV (birs_symb_symbols_DIRECT_CONV))) >>
      CONV_TAC (LAND_CONV (RAND_CONV (birs_freesymbs_DIRECT_CONV))) >>
      (* now have A INTER (B DIFF C) = EMPTY*)

      (*
      (fn (al,g) => (print_term g; ([(al,g)], fn ([t]) => t))) >>
      (fn x => (print "starting to compute concrete set of free symbols\n"; ALL_TAC x)) >>
      *)
      CONV_TAC (LAND_CONV (aux_setLib.varset_INTER_DIFF_CONV)) >>

      REWRITE_TAC [pred_setTheory.EMPTY_SUBSET]
    );
   in
    freesymbols_thm
   end;

  fun tidyup_birs_symb_exec_CONV stateset_conv labelset_conv =
    let
      val struct_CONV =
        RAND_CONV;
      fun Pi_CONV conv =
        RAND_CONV (RAND_CONV conv);
      fun L_CONV conv =
        RAND_CONV (LAND_CONV conv);
    in
      struct_CONV (Pi_CONV stateset_conv) THENC
      struct_CONV (L_CONV labelset_conv)
    end;

  (*
  val step_A_thm = single_step_A_thm;
  val step_B_thm = single_step_B_thm;
  *)
  fun birs_rule_SEQ_fun (birs_rule_SEQ_thm, bprog_tm) step_A_thm step_B_thm =
    let
      val (bprog_A_tm,_) = (dest_birs_symb_exec o concl) step_A_thm;
      val (bprog_B_tm,_) = (dest_birs_symb_exec o concl) step_B_thm;
      val _ = if identical bprog_tm bprog_A_tm andalso identical bprog_tm bprog_B_tm then () else
              raise Fail "birs_rule_SEQ_fun:: the programs have to match";

      val prep_thm =
        HO_MATCH_MP (HO_MATCH_MP birs_rule_SEQ_thm step_A_thm) step_B_thm;

      val freesymbols_tm = (fst o dest_imp o concl) prep_thm;
      val freesymbols_thm = birs_rule_SEQ_INTER_freesymbs_fun freesymbols_tm;
      val _ = print "finished to proof free symbols altogether\n";

      val bprog_composed_thm =
            (MP prep_thm freesymbols_thm);
      val _ = print "composed\n";

      (* tidy up set operations to not accumulate (in both, post state set and label set) *)
      val bprog_L_fixed_thm = CONV_RULE (tidyup_birs_symb_exec_CONV aux_setLib.birs_state_DIFF_UNION_CONV aux_setLib.labelset_UNION_CONV) bprog_composed_thm;

      val _ = if symb_sound_struct_is_normform (concl bprog_L_fixed_thm) then () else
              (print_term (concl bprog_L_fixed_thm);
              raise ERR "birs_rule_SEQ_fun" "something is not right, the produced theorem is not evaluated enough");
    in
      bprog_L_fixed_thm
    end;


end (* local *)

end (* struct *)
