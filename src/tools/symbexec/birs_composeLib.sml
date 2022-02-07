structure birs_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_composeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

(*
open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;
*)
  open birs_stepLib;
  open birs_auxTheory;
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in

(* first prepare the SEQ rule for prog *)
fun birs_rule_SEQ_prog_fun bprog_tm =
  let
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
  in
    (MATCH_MP symb_rulesTheory.symb_rule_SEQ_thm birs_symb_symbols_f_sound_prog_thm)
  end;

(* symbol freedom helper function *)
fun birs_rule_SEQ_free_symbols_fun bprog_tm (sys_A_tm, sys_B_tm, Pi_B_tm) =
  let
    (*
    val freesymbols_thm = store_thm(
       "freesymbols_thm", ``
    *)

(* ------------------------------------------------------------------------ *)
(* COPIED FROM TRANSFER-TEST (and modified) *)
(* ------------------------------------------------------------------------ *)
val debug_conv2 = (fn tm => (if true then print ".\n" else print_term tm; REFL tm));
           val birs_exps_of_senv_CONV = (
    debug_conv2 THENC
    REPEATC (CHANGED_CONV (
      (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (EVAL)))) THENC
      SIMP_CONV (std_ss) []
    ))
  );

           val birs_symb_symbols_CONV = (
    SIMP_CONV std_ss [birs_symb_symbols_thm] THENC
    SIMP_CONV (std_ss++birs_state_ss) [] THENC
    SIMP_CONV (std_ss) [birs_exps_of_senv_thm]
    (*(PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` birs_exps_of_senv_CONV)*)
  );
           val conv = birs_symb_symbols_CONV (*THENC EVAL*);
           val conv_ = computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv;

val debug_conv = (fn tm => (print_term tm; raise Fail "abcdE!!!"));
  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

    val freesymbols_thm = prove(``
    symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_A_tm INTER
      (symb_symbols_set (bir_symb_rec_sbir ^bprog_tm) ^Pi_B_tm DIFF
         symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_B_tm)
    = EMPTY
    ``,
      FULL_SIMP_TAC (std_ss) [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm, birs_symb_symbols_set_EQ_thm] >>

      (* TODO *)
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``, ``$BIGUNION``, ``$IMAGE``]) >>
      FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm] >>

      CONV_TAC (conv) >>
      REPEAT (
        CHANGED_TAC ( fn xyz =>
            REWRITE_TAC [Once (prove(``!x. (IMAGE bir_vars_of_exp x) = I (IMAGE bir_vars_of_exp x)``, REWRITE_TAC [combinTheory.I_THM]))]
            xyz
        ) >>
        CONV_TAC (GEN_match_conv combinSyntax.is_I (birs_exps_of_senv_CONV THENC EVAL))
      ) >>

      EVAL_TAC

(*
      CONV_TAC (conv)
      CONV_TAC (fn tm => (print_term tm; REFL tm))
      CONV_TAC (DEPTH_CONV (PAT_CONV ``\A. (I:((bir_var_t->bool)->bool)->((bir_var_t->bool)->bool)) A`` (fn tm => (print_term tm; raise Fail "abcdE!!!"))))



(combinSyntax.is_I o snd o dest_comb) tm





      CONV_TAC (ONCE_DEPTH_CONV (PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` (birs_exps_of_senv_CONV)))


FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
      EVAL_TAC

      CONV_TAC (PAT_CONV ``\A. (A DIFF C)`` (conv))





      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] >>

      EVAL_TAC
    (*
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.GSPECIFICATION]
    *)
*)
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
    val get_SEQ_thm_concl_symb_struct_fun = snd o strip_imp o snd o strip_binder (SOME boolSyntax.universal) o concl;
    val symb_struct_get_bprog_fun = snd o dest_comb o hd o snd o strip_comb;
    val bprog_tm   = (symb_struct_get_bprog_fun o get_SEQ_thm_concl_symb_struct_fun) birs_rule_SEQ_thm;
    val bprog_A_tm = (symb_struct_get_bprog_fun o concl) step_A_thm;
    val bprog_B_tm = (symb_struct_get_bprog_fun o concl) step_B_thm;
    val _ = if identical bprog_tm bprog_A_tm andalso identical bprog_tm bprog_B_tm then () else
            raise Fail "birs_rule_SEQ_fun:: the programs have to match";

    val (sys_A_tm, _, _)       = (symb_sound_struct_get_sysLPi_fun o concl) step_A_thm;
    val (sys_B_tm, _, Pi_B_tm) = (symb_sound_struct_get_sysLPi_fun o concl) step_B_thm;

    val freesymbols_thm = birs_rule_SEQ_free_symbols_fun bprog_tm (sys_A_tm, sys_B_tm, Pi_B_tm);
    (*
    val bprog_composed_thm = save_thm(
       "bprog_composed_thm",
    *)
    val bprog_composed_thm =
      MATCH_MP
        (MATCH_MP
           (MATCH_MP
              birs_rule_SEQ_thm
              freesymbols_thm)
        step_A_thm)
        step_B_thm;

    (* TODO: tidy up set operations to not accumulate (in both, post state set and label set) - does this simplification work well enough? *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] bprog_composed_thm; *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [pred_setTheory.INSERT_UNION] bprog_composed_thm; *)
    val bprog_composed_thm_1 =
      (SIMP_RULE
        (std_ss++HolBACoreSimps.holBACore_ss++birs_state_ss++pred_setLib.PRED_SET_ss)
        [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION]
        bprog_composed_thm);

    (* reconstruct IMAGE in the post state set *)
    val IMAGE_EMPTY_thm =
      Q.SPEC `birs_symb_to_symbst` (
        INST_TYPE [beta |-> Type`:(bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t`, alpha |-> Type`:birs_state_t`] 
        pred_setTheory.IMAGE_EMPTY
      );
    val bprog_composed_thm_2 =
      CONV_RULE
        (PAT_CONV ``\A. symb_hl_step_in_L_sound B (C, D, A)`` (REWRITE_CONV [GSYM IMAGE_EMPTY_thm, GSYM pred_setTheory.IMAGE_INSERT]))
        bprog_composed_thm_1
  in
    bprog_composed_thm_2
  end;


end (* local *)

end (* struct *)
