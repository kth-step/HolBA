structure birs_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open bir_vars_ofLib;

  open birsSyntax;
  open birs_auxTheory;

  open aux_setLib;
  open birs_utilsLib;

  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "bir_symb_composeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

  (* first prepare the SEQ rule for prog *)
  fun birs_rule_SEQ_prog_fun bprog_tm =
    ISPEC (bprog_tm) birs_rulesTheory.birs_rule_SEQ_gen_thm;

  (* symbol freedom helper function *)
  (* has to solve this ((birs_symb_symbols bsys_A) INTER (birs_freesymbs bsys_B bPi_B) = EMPTY) *)
  val speedcheat_SEQ_freesymbcheck = ref false;
  fun birs_rule_SEQ_INTER_freesymbs_fun freesymbols_tm =
   let
    val freesymbols_thm = prove(freesymbols_tm,
      (if !speedcheat_SEQ_freesymbcheck then cheat else ALL_TAC) >> 

      (* REMARK: I have seen slightly faster computation when
             - reducing the formula to operations over ground variable sets in this shape: A INTER (B DIFF C)
             - then turning around the set operations like this: g INTER (s DIFF t) = s INTER (g DIFF t)
             - then applying the variable set operations *)
      CONV_TAC (LAND_CONV (LAND_CONV (birs_symb_symbols_DIRECT_CONV))) >>
      CONV_TAC (LAND_CONV (RAND_CONV (birs_freesymbs_DIRECT_CONV))) >>
      (* now have A INTER B = EMPTY*)

      (*
      (fn (al,g) => (print_term g; ([(al,g)], fn ([t]) => t))) >>
      (fn x => (print "starting to compute concrete set of free symbols\n"; ALL_TAC x)) >>
      *)
      CONV_TAC (LAND_CONV (varset_INTER_CONV)) >>

      REWRITE_TAC [pred_setTheory.EMPTY_SUBSET]
    );
   in
    freesymbols_thm
   end;

  (*
  val step_A_thm = single_step_A_thm;
  val step_B_thm = single_step_B_thm;
  *)
  fun birs_rule_SEQ_fun birs_rule_SEQ_thm step_A_thm step_B_thm =
    let
      val _ = birs_check_compatible step_A_thm step_B_thm;

      val prep_thm =
        Profile.profile "birs_rule_SEQ_fun_1_match" (HO_MATCH_MP (HO_MATCH_MP birs_rule_SEQ_thm step_A_thm)) step_B_thm;

      val freesymbols_tm = (fst o dest_imp o concl) prep_thm;
      val freesymbols_thm = Profile.profile "birs_rule_SEQ_fun_2_freesymbols" birs_rule_SEQ_INTER_freesymbs_fun freesymbols_tm;
      val _ = print "finished to proof free symbols altogether\n";

      val bprog_composed_thm =
            (MP prep_thm freesymbols_thm);
      val _ = print "composed\n";

      (* tidy up set operations to not accumulate (in both, post state set and label set) *)
      val bprog_fixed_thm =
        Profile.profile "birs_rule_SEQ_fun_3_tidyupsets" (CONV_RULE
         (birs_Pi_CONV birs_state_DIFF_UNION_CONV THENC
          birs_L_CONV labelset_UNION_CONV))
         bprog_composed_thm
        handle e => (print "\n\n"; print_thm bprog_composed_thm; print "tidy up Pi and labelset failed\n"; raise e);

      val _ = birs_check_norm_thm ("birs_rule_SEQ_fun", "") bprog_fixed_thm
        handle e => (print_term (concl bprog_fixed_thm); raise e);
    in
      bprog_fixed_thm
    end;
  val birs_rule_SEQ_fun = fn x => fn y => Profile.profile "birs_rule_SEQ_fun" (birs_rule_SEQ_fun x y);


end (* local *)

end (* struct *)
