structure distribute_generic_stuffLib =
struct

open Abbrev;

local 
  open HolKernel Parse boolLib bossLib;
  
  open HolBACoreSimps;
  open bir_env_oldTheory;
  open bir_envTheory;
  open birs_auxTheory;
  open distribute_generic_stuffTheory;
  open bir_symb_sound_coreTheory;

  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in



(* TODO: MOVE AWAY !!!!! GENERIC DEFINITIONS AND THEOREMS *)
(*
val varset_thm = incr_prog_vars_thm;
*)
fun Q_bircont_SOLVE3CONJS_TAC varset_thm = (
    FULL_SIMP_TAC (std_ss) [Q_bircont_thm] >>
    (* pc *)
    CONJ_TAC >- (
      REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>
    (* status Running *)
    CONJ_TAC >- (
      REV_FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def]
    ) >>

    (* bir_env_vars_are_initialised *)
    CONJ_TAC >- (
      PAT_X_ASSUM ``A = B`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>
      PAT_X_ASSUM ``A = B`` (K ALL_TAC) >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def, varset_thm] >>

      IMP_RES_TAC birs_env_vars_are_initialised_IMP_thm >>
      POP_ASSUM (K ALL_TAC) >>
      PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o SPEC ((snd o dest_eq o concl) varset_thm)) >>
      POP_ASSUM (MATCH_MP_TAC) >>

      (* cleanup proof state *)
      REPEAT (POP_ASSUM (K ALL_TAC)) >>

      (* concretize and normalize *)
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm, birs_auxTheory.birs_exps_of_senv_thm] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_gen_env_def, birs_gen_env_fun_def, birs_gen_env_fun_def, bir_envTheory.bir_env_lookup_def] >>
      FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [birs_auxTheory.birs_exps_of_senv_COMP_thm] >>
      CONV_TAC (RATOR_CONV (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_exp``] THENC SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL))) >>
      (* TODO: improve this *)
      CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``bir_vars_of_program``] THENC SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss) [] THENC EVAL)) >>

      (* finish the proof *)
      REWRITE_TAC [birs_env_vars_are_initialised_INSERT_thm, birs_env_vars_are_initialised_EMPTY_thm, birs_env_var_is_initialised_def] >>
      EVAL_TAC >>
      SIMP_TAC (std_ss++holBACore_ss) [] >>
      EVAL_TAC
    )
);

end (* local *)

end (* structure *)

