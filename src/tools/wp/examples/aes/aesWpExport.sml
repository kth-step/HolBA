open aesWpTheory;

open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;
open bir_wp_simpTheory;

(* look at core/bir_expLib *)

val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = List.nth((snd o strip_comb o snd o dest_comb) prop, 1);
val cond = ``bir_exp_is_taut
   (bir_exp_imp (BExp_Const (Imm1 pre))
    (^wp))``;

val t1 = SIMP_CONV (std_ss) [bir_exp_tautologiesTheory.bir_exp_is_taut_def] cond;
val cnd2 = List.nth((strip_conj o snd o dest_eq o concl) t1, 2);
prove(``^cnd2``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def, bir_vars_of_exp_def,
		       bir_exp_imp_def, bir_exp_not_def, bir_exp_and_def, bir_exp_or_def] >> 
  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_eval_bin_exp_def, bir_eval_unary_exp_def, bir_eval_bin_pred_def, bir_env_read_def] >>
  FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def, bir_var_name_def] >>
  (`(bir_env_lookup
                (bir_var_name (BVar "SP_EL0" (BType_Imm Bit64))) env
   = SOME(bir_var_type (BVar "SP_EL0" (BType_Imm Bit64)),SOME v')) ∧
        (type_of_bir_val v' = SOME (bir_var_type (BVar "SP_EL0" (BType_Imm Bit64))))` by cheat) >>
  FULL_SIMP_TAC std_ss [bir_var_type_def] >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  (`v' = BVal_Imm (Imm64 v'')` by cheat) >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  EVAL_TAC >>
  (`pre = if ((v'' && 3w) = (0w:word64)) then 1w else 0w` by cheat) >>
  FULL_SIMP_TAC std_ss [] >>
  BBLAST_PROVE_TAC



open blastLib;
