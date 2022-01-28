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
    val freesymbols_thm = prove(``
    symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_A_tm INTER
      (symb_symbols_set (bir_symb_rec_sbir ^bprog_tm) ^Pi_B_tm DIFF
         symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_B_tm)
    = EMPTY
    ``,
      FULL_SIMP_TAC (std_ss) [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm, birs_symb_symbols_set_EQ_thm] >>
      FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >>
      FULL_SIMP_TAC (std_ss) [birs_symb_symbols_thm] >>

      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] >>

      EVAL_TAC
    (*
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.GSPECIFICATION]
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

    (* TODO: tidy up set operations to not accumulate (in both, post state set and label set) - see trials above *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] bprog_composed_thm; *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [pred_setTheory.INSERT_UNION] bprog_composed_thm; *)
  in
    bprog_composed_thm
  end;


end (* local *)

end (* struct *)
