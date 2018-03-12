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

open bir_exp_congruencesTheory;
open bir_exp_tautologiesTheory;

load "pairLib";

val _ = new_theory "bir_wp_simp";



val bir_var_ss = rewrites (type_rws ``:bir_var_t``);
val string_t_ss = rewrites (type_rws ``:string``);






(* TODO: memory load store updates *)







val bir_exp_and_def = Define `
      bir_exp_and e1 e2 = BExp_BinExp BIExp_And e1 e2
`;

val bir_exp_or_def = Define `
      bir_exp_or e1 e2 = BExp_BinExp BIExp_Or e1 e2
`;

val bir_exp_not_def = Define `
      bir_exp_not e = BExp_UnaryExp BIExp_Not e
`;

val bir_exp_imp_def = Define `
      bir_exp_imp e1 e2 = bir_exp_or (bir_exp_not e1) e2
`;

val bir_exp_imp_or_thm = store_thm("bir_exp_imp_or_thm", ``
     !e1 e2.
         bir_exp_imp e1 e2 = bir_exp_or (bir_exp_not e1) e2
``,

  REWRITE_TAC [bir_exp_imp_def]
);











(* !!!!!!!!!! this has to go somewhere else !!!!!!!!!!!!!!!!!!!!!!! *)
(* ---------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------- *)


val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_type_ss = rewrites (type_rws ``:bir_type_t``);
val bir_imm_ss = rewrites (type_rws ``:bir_imm_t``);
val bir_immtype_ss = rewrites (type_rws ``:bir_immtype_t``);
val bir_wp_simp_eval_binpred_eq_thm = prove(``
    !e1 e2 s.
      (bir_eval_exp (BExp_BinPred BIExp_Equal e1 e2) s = bir_val_true)
      <=>
      (
       (bir_val_is_Imm (bir_eval_exp e1 s)) /\
       (bir_val_is_Imm (bir_eval_exp e2 s)) /\
       (bir_eval_exp e1 s = bir_eval_exp e2 s)
      )
``,

  REWRITE_TAC [bir_eval_exp_def, bir_val_is_Imm_def] >>

  Cases_on `(bir_eval_exp e1 s)` >> (
    Cases_on `(bir_eval_exp e2 s)` >> (
      SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_pred_def, bir_val_true_def]
    )
  ) >>

  Cases_on `type_of_bir_imm b = type_of_bir_imm b'` >- (
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def, bir_imm_expTheory.bir_bin_pred_Equal_REWR] >>

    Cases_on `b = b'` >> (
      ASM_SIMP_TAC (srw_ss()) []
    )
  ) >>

  ASM_SIMP_TAC (std_ss++bir_val_ss) [] >>
  METIS_TAC []
);


val bir_wp_simp_eval_unary_Imm_s_match_thm = prove(``
    !et e env sz.
      (bir_val_is_Imm_s sz (bir_eval_exp (BExp_UnaryExp et e) env))
      <=>
      (bir_val_is_Imm_s sz (bir_eval_exp e env))
``,

  REWRITE_TAC [bir_eval_exp_def, bir_val_is_Imm_def] >>

  Cases_on `(bir_eval_exp e env)` >> (
    SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_unary_exp_def, bir_val_is_Imm_s_ALT_DEF]
  ) >>

  SIMP_TAC (std_ss) [bir_imm_expTheory.type_of_bir_unary_exp]
);


val bir_wp_simp_eval_bin_Imm_s_match_thm = prove(``
    !et e1 e2 env sz.
      (bir_val_is_Imm_s sz (bir_eval_exp (BExp_BinExp et e1 e2) env))
      <=>
      (
       (     bir_val_is_Imm_s sz (bir_eval_exp e1 env) /\
             bir_val_is_Imm_s sz (bir_eval_exp e2 env))
      )
``,

  REWRITE_TAC [bir_eval_exp_def, bir_val_is_Imm_def] >>

  Cases_on `(bir_eval_exp e1 env)` >> (
    Cases_on `(bir_eval_exp e2 env)` >> (
      SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_bin_exp_def, bir_val_is_Imm_s_ALT_DEF]
    )
  ) >>

  Cases_on `type_of_bir_imm b = type_of_bir_imm b'` >- (
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def, bir_imm_expTheory.type_of_bir_bin_exp]
  ) >>

  ASM_SIMP_TAC (std_ss++bir_val_ss) []
);


(* ---------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------- *)





























val bir_exp_bool_and_well_typed_vars_def = Define `
      bir_exp_bool_and_well_typed_vars e =
           bir_is_bool_exp e /\
           bir_var_set_is_well_typed (bir_vars_of_exp e)
`;


val bir_eval_exp_not_true_false_thm = store_thm("bir_eval_exp_not_true_false_thm", ``
    !e env.
     (bir_is_bool_exp e) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env <> bir_val_true)
      <=>
      (bir_eval_exp e env = bir_val_false)
     )
``,

  REPEAT STRIP_TAC >>

  subgoal `((bir_eval_exp e env) = bir_val_false) \/ ((bir_eval_exp e env) = bir_val_true)` >- (
    METIS_TAC [bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL, bir_val_is_Bool_ALT_DEF, GSYM bir_is_bool_exp_env_def]
  ) >> (
    FULL_SIMP_TAC (std_ss++bir_val_ss++wordsLib.WORD_ss) [bir_exp_bool_and_well_typed_vars_def, bir_val_true_def, bir_val_false_def, bir_immTheory.bir_imm_t_11]
  )
);

val bir_wp_simp_eval_not_true_exp_thm = store_thm("bir_wp_simp_eval_not_true_exp_thm", ``
    !e env.
     (bir_exp_bool_and_well_typed_vars e) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env <> bir_val_true)
      <=>
      (bir_eval_exp e env = bir_val_false)
     )
``,

  METIS_TAC [bir_exp_bool_and_well_typed_vars_def, bir_eval_exp_not_true_false_thm]
);


val bir_var_set_is_well_typed_UNION_initialised_thm = store_thm("bir_var_set_is_well_typed_UNION_initialised_thm", ``
    !e1vs e2vs env.
(*
TODO: the first two assumptions are not neccessary i believe
*)
     (bir_var_set_is_well_typed e1vs) ==>
     (bir_var_set_is_well_typed e2vs) ==>
     (bir_env_vars_are_initialised env (e1vs UNION e2vs)) ==>
     (bir_var_set_is_well_typed (e1vs UNION e2vs))
``,

  REPEAT STRIP_TAC >>

  ASM_REWRITE_TAC [bir_var_set_is_well_typed_UNION] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss) [bir_env_vars_are_initialised_UNION, bir_env_vars_are_initialised_def] >>

  subgoal `(bir_env_var_is_initialised env v1) /\ (bir_env_var_is_initialised env v2)` >- (
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC (std_ss) [bir_env_var_is_initialised_def] >>

  REV_FULL_SIMP_TAC (std_ss) []
);


val bir_wp_simp_eval_or_exp_thm = store_thm("bir_wp_simp_eval_or_exp_thm", ``
    !e e1 e2 env.
     (e = bir_exp_or e1 e2) ==>
     (bir_exp_bool_and_well_typed_vars e1) ==>
     (bir_exp_bool_and_well_typed_vars e2) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env = bir_val_true)
      <=>
      (
       (bir_eval_exp e1 env = bir_val_true)
       \/
       (bir_eval_exp e2 env = bir_val_true)
      )
     )
``,

  REPEAT STRIP_TAC >>

  subgoal `bir_exp_bool_and_well_typed_vars e` >- (
    REV_FULL_SIMP_TAC std_ss [bir_exp_or_def, bir_exp_bool_and_well_typed_vars_def, bir_is_bool_exp_REWRS, bir_vars_of_exp_def] >>
    METIS_TAC [bir_var_set_is_well_typed_UNION_initialised_thm]
  ) >>

  subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e1)) /\ (bir_env_vars_are_initialised env (bir_vars_of_exp e2))` >- (
    METIS_TAC [bir_exp_or_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
  ) >>

  Cases_on `bir_eval_exp e1 env = bir_val_true` >> Cases_on `bir_eval_exp e2 env = bir_val_true` >> (
    REV_FULL_SIMP_TAC std_ss [bir_exp_or_def, bir_wp_simp_eval_not_true_exp_thm] >>
    EVAL_TAC >>
    FULL_SIMP_TAC std_ss [] >>
    EVAL_TAC
  )
);


val bir_wp_simp_eval_and_exp_thm = store_thm("bir_wp_simp_eval_and_exp_thm", ``
    !e e1 e2 env.
     (e = bir_exp_and e1 e2) ==>
     (bir_exp_bool_and_well_typed_vars e1) ==>
     (bir_exp_bool_and_well_typed_vars e2) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env = bir_val_true)
      <=>
      (
       (bir_eval_exp e1 env = bir_val_true)
       /\
       (bir_eval_exp e2 env = bir_val_true)
      )
     )
``,

  REPEAT STRIP_TAC >>

  subgoal `bir_exp_bool_and_well_typed_vars e` >- (
    REV_FULL_SIMP_TAC std_ss [bir_exp_and_def, bir_exp_bool_and_well_typed_vars_def, bir_is_bool_exp_REWRS, bir_vars_of_exp_def] >>
    METIS_TAC [bir_var_set_is_well_typed_UNION_initialised_thm]
  ) >>

  subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e1)) /\ (bir_env_vars_are_initialised env (bir_vars_of_exp e2))` >- (
    METIS_TAC [bir_exp_and_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
  ) >>

  Cases_on `bir_eval_exp e1 env = bir_val_true` >> Cases_on `bir_eval_exp e2 env = bir_val_true` >> (
    REV_FULL_SIMP_TAC std_ss [bir_exp_and_def, bir_wp_simp_eval_not_true_exp_thm] >>
    EVAL_TAC >>
    FULL_SIMP_TAC std_ss [] >>
    EVAL_TAC
  )
);



(*
(* this does not work.... of course.... *)
val bir_wp_simp_eval_imp_exp_thm = store_thm("bir_wp_simp_eval_imp_exp_thm", ``
    !e e1 e2 env.
     (e = bir_exp_imp e1 e2) ==>
     (bir_exp_bool_and_well_typed_vars e1) ==>
     (bir_exp_bool_and_well_typed_vars e2) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env = bir_val_true)
      <=>
      (
       (bir_eval_exp e1 env = bir_val_true)
       ==>
       (bir_eval_exp e2 env = bir_val_true)
      )
     )
``,

  REPEAT STRIP_TAC >>

  subgoal `bir_exp_bool_and_well_typed_vars e` >- (
    REV_FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_bool_and_well_typed_vars_def, bir_is_bool_exp_REWRS, bir_vars_of_exp_def] >>
    METIS_TAC [bir_var_set_is_well_typed_UNION_initialised_thm]
  ) >>

  subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e1)) /\ (bir_env_vars_are_initialised env (bir_vars_of_exp e2))` >- (
    METIS_TAC [bir_exp_imp_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
  ) >>

  Cases_on `bir_eval_exp e1 env = bir_val_true` >> Cases_on `bir_eval_exp e2 env = bir_val_true` >> (
    REV_FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_wp_simp_eval_not_true_exp_thm] >>
    EVAL_TAC >>
    FULL_SIMP_TAC std_ss [] >>
    EVAL_TAC
  )
);
*)










(*
val bir_wp_simp_taut_and_thm = store_thm("bir_wp_simp_taut_and_thm", ``
    !prem e1 e2.
     (bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2))) ==>
     ( 
      (bir_exp_is_taut (bir_exp_imp prem (bir_exp_and e1 e2)))
      <=>
      (
       (bir_exp_is_taut (bir_exp_imp prem e1))
       /\
       (bir_exp_is_taut (bir_exp_imp prem e2))
      )
     )
``,

  REPEAT STRIP_TAC >>

  EQ_TAC >- (
    STRIP_TAC >>

    STRIP_TAC >> (
      REWRITE_TAC [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
      REPEAT STRIP_TAC >|
      [
        ALL_TAC
      ,
        ALL_TAC
      ,
        FULL_SIMP_TAC std_ss [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
        cheat (* extend environment by uninitialized variables of e2, and then use the theorems for bir_and and bir_imp *)
      ] >> (
        FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_and_def, bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_is_bool_exp_REWRS, bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION]
      )
    )
  ) >>

  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >|
  [
    FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_and_def, bir_exp_tautologiesTheory.bir_exp_is_taut_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_is_bool_exp_REWRS, bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION]
  ,
(*
    FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_and_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def] >>

    subgoal `(bir_var_set_is_well_typed (bir_vars_of_exp e1)) /\ (bir_var_set_is_well_typed (bir_vars_of_exp e2)) /\ (bir_var_set_is_well_typed (bir_vars_of_exp prem))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_var_set_is_well_typed_UNION]
    ) >>

    FULL_SIMP_TAC std_ss [bir_var_set_is_well_typed_UNION_initialised_thm]
*)
    cheat
  ,
    subgoal `(bir_eval_exp (bir_exp_imp prem e1) env = bir_val_true) /\ (bir_eval_exp (bir_exp_imp prem e2) env = bir_val_true)` >- (
      FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_and_def, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
    ) >>

    
    cheat
  ]
);

val bir_wp_simp_taut_imp_thm = store_thm("bir_wp_simp_taut_imp_thm", ``
    !prem e1 e2.
      (bir_exp_is_taut (bir_exp_imp prem (bir_exp_imp e1 e2)))
      <=>
      (bir_exp_is_taut (bir_exp_imp (bir_exp_and prem e1) e2)
``,

  REWRITE_TAC [bir_exp_imp_def, bir_exp_and_def] >>
  REPEAT STRIP_TAC >>
cheat
);
*)






(*
val bir_wp_simp_eval_and_thm = store_thm("bir_wp_simp_eval_and_thm", ``
    !prem e1 e2.
      (!s. (prem s) ==> (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s = bir_val_true))
      <=>
      (
       (!s. (prem s) ==> (bir_eval_exp e1 s = bir_val_true))
       /\
       (!s. (prem s) ==> (bir_eval_exp e2 s = bir_val_true))
      )
``,

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >> (
      Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
      REV_FULL_SIMP_TAC std_ss [] >>

      subgoal `bir_val_is_Imm (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s)` >- (
        ASM_SIMP_TAC std_ss [bir_val_true_def, bir_val_checker_REWRS]
      ) >>

      subgoal `?sz. bir_val_is_Imm_s sz (bir_eval_exp e1 s) /\ bir_val_is_Imm_s sz (bir_eval_exp e2 s)` >- (
        METIS_TAC [bir_val_is_Imm_s_IMPL, bir_wp_simp_eval_bin_is_Imm_thm]
      ) >>

      Cases_on `bir_eval_exp e1 s` >> (
        Cases_on `bir_eval_exp e2 s` >> (
          FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_val_checker_REWRS]
        )
      ) >>

      FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_exp_def, bir_eval_bin_exp_REWRS, bir_val_true_def] >>

      subgoal `sz = Bit1` >- (
        METIS_TAC [bir_imm_expTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_imm_expTheory.bir_bin_exp_def, bir_imm_expTheory.bir_bin_exp_GET_OPER_def] >>

      Q.PAT_X_ASSUM `A && B = C` (MP_TAC) >>
      blastLib.BBLAST_TAC
    )
  ) >>

  REPEAT STRIP_TAC >>

  REPEAT (Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm))) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  
  ASM_REWRITE_TAC [bir_eval_exp_def, bir_eval_bin_exp_REWRS] >>
  EVAL_TAC
);


bir_is_bool_exp_def
type_of_bir_exp_def
bir_eval_exp_def
bir_eval_bin_pred_def
val bir_wp_simp_eval_imp_thm = store_thm("bir_wp_simp_eval_imp_thm", ``
    !prem e1 e2.
      (bir_is_bool_exp e1) ==>
      (bir_is_bool_exp e2) ==>
      (
       (
        !s. (prem s) ==>
            (bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not e1) e2) s = bir_val_true)
       )
       <=>
       (
        !s. ((\s. (prem s) /\ (bir_eval_exp e1 s = bir_val_true)) s)
            ==>
            (bir_eval_exp e2 s = bir_val_true)
       )
      )
``,

  bir_is_bool_exp
);

(*
val bir_exp_and_bool_thm = store_thm ("bir_exp_and_bool_thm", ``
      bir_eval_exp (bir_exp_and e1 e2) s)
``,

bir_wp_simp_eval_bin_is_Imm_s_thm
  cheat
);
*)


val bir_wp_simp_eval_imp_thm = store_thm("bir_wp_simp_eval_imp_thm", ``
    !prem e1 e2.
      (!s. bir_eval_exp (bir_exp_imp prem (bir_exp_imp e1 e2)) s = bir_val_true)
      <=>
      (!s. bir_eval_exp (bir_exp_imp (bir_exp_and prem e1) e2) s = bir_val_true)
``,

  REPEAT STRIP_TAC >>

  EQ_TAC >- (
    REPEAT STRIP_TAC >>

    Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    subgoal `bir_val_is_Imm_s Bit1 (bir_eval_exp e1 s)` >- (
      METIS_TAC [bir_exp_imp_def, bir_val_true_def, bir_wp_simp_eval_bin_is_Imm_s_thm, bir_val_checker_REWRS, type_of_bir_imm_def, bir_imm_expTheory.type_of_bir_bin_exp]
    ) >>

    
  ) >>
);

val bir_wp_simp_eval_or_thm = store_thm("bir_wp_simp_eval_or_thm", ``
    !prem e1 e2.
      (
       !s. (prem s) ==>
           (bir_eval_exp (BExp_BinExp BIExp_Or e1 e2) s = bir_val_true)
      )
      <=>
      (
       !s. ((\s. (prem s) /\ (bir_eval_exp (BExp_UnaryExp BIExp_Not e1) s = bir_val_true)) s)
           ==>
           (bir_eval_exp e2 s = bir_val_true)
      )
``,

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

      Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
      REV_FULL_SIMP_TAC std_ss [] >>

      subgoal `bir_val_is_Imm (bir_eval_exp (BExp_BinExp BIExp_And e1 e2) s)` >- (
        ASM_SIMP_TAC std_ss [bir_val_true_def, bir_val_checker_REWRS]
      ) >>

      subgoal `?sz. bir_val_is_Imm_s sz (bir_eval_exp e1 s) /\ bir_val_is_Imm_s sz (bir_eval_exp e2 s)` >- (
        METIS_TAC [bir_val_is_Imm_s_IMPL, bir_wp_simp_eval_bin_is_Imm_thm]
      ) >>

      Cases_on `bir_eval_exp e1 s` >> (
        Cases_on `bir_eval_exp e2 s` >> (
          FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_val_checker_REWRS]
        )
      ) >>

      FULL_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bir_eval_exp_def, bir_eval_bin_exp_REWRS, bir_val_true_def] >>

      subgoal `sz = Bit1` >- (
        METIS_TAC [bir_imm_expTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_imm_expTheory.bir_bin_exp_def, bir_imm_expTheory.bir_bin_exp_GET_OPER_def] >>

      Q.PAT_X_ASSUM `A && B = C` (MP_TAC) >>
      blastLib.BBLAST_TAC


  ) >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  REPEAT (Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm))) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  subgoal `type_of_bir_imm (bir_eval_exp (BExp_UnaryExp BIExp_Not e1) s) = Bit1` >- (
    METIS_TAC
  )
  
  ASM_REWRITE_TAC [bir_eval_exp_def, bir_eval_bin_exp_REWRS] >>
  EVAL_TAC
);
*)









(* !!!!!!!!!!!!!! GOES SOMEWHERE ELSE !!!!!!!!!!!!!!!!!!!! *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)

val bir_eval_exp_indep_env_update_thm = store_thm("bir_eval_exp_indep_env_update_thm", ``
    !vn vt vo e sm.
      (~(vn IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp e (BEnv sm))
       =
       (bir_eval_exp e (BEnv (FUPDATE sm (vn, (vt, vo)))))
      )
``,

  REPEAT STRIP_TAC >>

  Induct_on `e` >> (
    ASM_SIMP_TAC std_ss [bir_eval_exp_def, bir_vars_of_exp_def, pred_setTheory.IMAGE_UNION] >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
  )
);



val bir_wp_simp_eval_subst1_lemma = store_thm("bir_wp_simp_eval_subst1_lemma", ``
    !v ve vn' vt' vo' e sm.
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst1 v ve e) (BEnv (FUPDATE sm (vn', (vt', vo')))))
      )
``,

  REPEAT STRIP_TAC >>

  subgoal `~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp (bir_exp_subst1 v ve e))))` >- (
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>

    Cases_on `v IN bir_vars_of_exp e` >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.IMAGE_UNION] >>
      METIS_TAC []
    )
  ) >>

  METIS_TAC [bir_eval_exp_indep_env_update_thm]
);

(* --------------------------------------------- more ------------------------------------------------ *)





val bir_exp_CONG_not_not_thm = store_thm("bir_exp_CONG_not_not_thm", ``
     !e ty.
         (type_of_bir_exp e = SOME ty) ==>
         (bir_type_is_Imm ty) ==>
         (bir_exp_CONG e (bir_exp_not (bir_exp_not e)))
``,

  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_exp_and_def, bir_exp_or_def, bir_exp_not_def, bir_exp_CONG_def] >>
  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def]
  ) >>

  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_type_is_Imm_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  IMP_RES_TAC type_of_bir_val_EQ_ELIMS >>

  Cases_on `i` >> (
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_GET_OPER_def] >>
    blastLib.BBLAST_TAC
  )
);


val bir_exp_CONG_de_morgan_and_thm = store_thm("bir_exp_CONG_de_morgan_and_thm", ``
     !e1 e2.
         (bir_exp_CONG (bir_exp_not (bir_exp_and e1 e2)) (bir_exp_or (bir_exp_not e1) (bir_exp_not e2)))
``,

  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_exp_and_def, bir_exp_or_def, bir_exp_not_def, bir_exp_CONG_def] >>
  REPEAT STRIP_TAC >|
  [
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def] >>

    Cases_on `type_of_bir_exp e1` >> Cases_on `type_of_bir_exp e2` >> (
      CASE_TAC >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss) [] >>
      Cases_on `bir_type_is_Imm x` >> (
        FULL_SIMP_TAC (std_ss) []
      ) >>
      Cases_on `bir_type_is_Imm x'` >> Cases_on `x' = x` >> (
        FULL_SIMP_TAC (std_ss) []
      )
    )
  ,
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def]
  ,
    ALL_TAC
  ] >>

  subgoal `(type_of_bir_exp e1 = SOME ty) /\ (type_of_bir_exp e2 = SOME ty) /\ (bir_type_is_Imm ty)` >- (
    METIS_TAC [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS]
  ) >>

  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_type_is_Imm_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  IMP_RES_TAC type_of_bir_val_EQ_ELIMS >>

  Cases_on `i` >> Cases_on `i'` >> (
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    blastLib.BBLAST_TAC >>

    FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS, type_of_bir_val_def, type_of_bir_imm_def] >>
    PAT_X_ASSUM ``(A:bir_immtype_t) = (s:bir_immtype_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++bir_immtype_ss) []
  )
);

(* TODO: simplify the following congruence proofs by introducing theorems to enable use of automation *)
val bir_exp_CONG_de_morgan_or_thm = store_thm("bir_exp_CONG_de_morgan_or_thm", ``
     !e1 e2.
         (bir_exp_CONG (bir_exp_not (bir_exp_or e1 e2)) (bir_exp_and (bir_exp_not e1) (bir_exp_not e2)))
``,

  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_exp_and_def, bir_exp_or_def, bir_exp_not_def, bir_exp_CONG_def] >>
  REPEAT STRIP_TAC >|
  [
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def] >>

    Cases_on `type_of_bir_exp e1` >> Cases_on `type_of_bir_exp e2` >> (
      CASE_TAC >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss) [] >>
      Cases_on `bir_type_is_Imm x` >> (
        FULL_SIMP_TAC (std_ss) []
      ) >>
      Cases_on `bir_type_is_Imm x'` >> Cases_on `x' = x` >> (
        FULL_SIMP_TAC (std_ss) []
      )
    )
  ,
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def]
  ,
    ALL_TAC
  ] >>

  subgoal `(type_of_bir_exp e1 = SOME ty) /\ (type_of_bir_exp e2 = SOME ty) /\ (bir_type_is_Imm ty)` >- (
    METIS_TAC [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS]
  ) >>

  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_type_is_Imm_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  IMP_RES_TAC type_of_bir_val_EQ_ELIMS >>

  Cases_on `i` >> Cases_on `i'` >> (
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    blastLib.BBLAST_TAC >>

    FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS, type_of_bir_val_def, type_of_bir_imm_def] >>
    PAT_X_ASSUM ``(A:bir_immtype_t) = (s:bir_immtype_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++bir_immtype_ss) []
  )
);

val bir_exp_CONG_or_assoc_thm = store_thm("bir_exp_CONG_or_assoc_thm", ``
     !e1 e2 e3.
         (bir_exp_CONG (bir_exp_or e1 (bir_exp_or e2 e3)) (bir_exp_or (bir_exp_or e1 e2) e3))
``,

  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_exp_or_def, bir_exp_CONG_def] >>
  REPEAT STRIP_TAC >|
  [
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def] >>

    Cases_on `type_of_bir_exp e1` >> Cases_on `type_of_bir_exp e2` >> Cases_on `type_of_bir_exp e3` >> (
      REPEAT (CASE_TAC >> POP_ASSUM (ASSUME_TAC o GSYM)) >>
      FULL_SIMP_TAC (std_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss) [] >>
      Cases_on `bir_type_is_Imm x` >> (
        FULL_SIMP_TAC (std_ss) []
      ) >>
      Cases_on `bir_type_is_Imm x'` >> Cases_on `x' = x` >> (
        FULL_SIMP_TAC (std_ss) []
      )
    )
  ,
    ASM_SIMP_TAC std_ss [type_of_bir_exp_def, bir_vars_of_exp_def, pred_setTheory.UNION_ASSOC]
  ,
    ALL_TAC
  ] >>

  subgoal `(type_of_bir_exp e1 = SOME ty) /\ (type_of_bir_exp e2 = SOME ty) /\ (type_of_bir_exp e3 = SOME ty) /\ (bir_type_is_Imm ty)` >- (
    METIS_TAC [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS]
  ) >>

  FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_type_is_Imm_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  IMP_RES_TAC type_of_bir_val_EQ_ELIMS >>

  Cases_on `i` >> Cases_on `i'` >> Cases_on `i''` >> (
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    blastLib.BBLAST_TAC >>

    FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.type_of_bir_exp_EQ_SOME_REWRS, type_of_bir_val_def, type_of_bir_imm_def] >>
    PAT_X_ASSUM ``(A:bir_immtype_t) = (s:bir_immtype_t)`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++bir_immtype_ss) []
  )
);

val bir_exp_CONG_imp_imp_thm = store_thm("bir_exp_CONG_imp_imp_thm", ``
     !e1 e2 e3 ty.
         (bir_exp_CONG (bir_exp_imp e1 (bir_exp_imp e2 e3)) (bir_exp_imp (bir_exp_and e1 e2) e3))
``,

  REWRITE_TAC [bir_exp_imp_or_thm] >>
  REPEAT STRIP_TAC >>

  subgoal `bir_exp_CONG (bir_exp_or (bir_exp_not e1) (bir_exp_or (bir_exp_not e2) e3))
                        (bir_exp_or (bir_exp_or (bir_exp_not e1) (bir_exp_not e2)) e3)` >- (
    METIS_TAC [bir_exp_CONG_or_assoc_thm, bir_exp_CONG_TRANS]
  ) >>

  subgoal `bir_exp_CONG (bir_exp_or (bir_exp_or (bir_exp_not e1) (bir_exp_not e2)) e3)
                        (bir_exp_or (bir_exp_not (bir_exp_and e1 e2)) e3)` >- (
    METIS_TAC [bir_exp_or_def, bir_exp_CONG_BASIC_CONG_RULES, bir_exp_CONG_REFL, bir_exp_CONG_SYM, bir_exp_CONG_de_morgan_and_thm]
  ) >>

  METIS_TAC [bir_exp_CONG_TRANS]
);


(* --------------------------------------------- more ------------------------------------------------ *)

val bir_wp_simp_taut_and_thm = store_thm("bir_wp_simp_taut_and_thm", ``
    !prem e1 e2.
      (bir_exp_is_taut (bir_exp_imp prem (bir_exp_and e1 e2)))
      <=>
      (
       (bir_exp_is_taut (bir_exp_imp prem e1))
       /\
       (bir_exp_is_taut (bir_exp_imp prem e2))
       /\
       (bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2)))
      )
``,

  REPEAT STRIP_TAC >>

  EQ_TAC >- (
    REPEAT STRIP_TAC >|
    [
      ALL_TAC
    ,
      ALL_TAC
    ,
      FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_and_def, bir_exp_is_taut_def, bir_vars_of_exp_def, pred_setTheory.UNION_ASSOC]
    ] >> (
      FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_and_def, bir_exp_is_taut_def] >>
      REPEAT STRIP_TAC >|
      [
        METIS_TAC [bir_is_bool_exp_REWRS]
      ,
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION]
      ,
        ALL_TAC
      ] >>

      (* now it's getting tricky, we have to initialize all vars of ((prem UNION (e1/e2)) DIFF e2/e1) in env to obtain env', then we can prove this *)
      cheat
    )
  ) >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_and_def, bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >|
  [
    METIS_TAC [bir_is_bool_exp_REWRS]
  ,
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pred_setTheory.UNION_ASSOC]
  ,
    ALL_TAC
  ] >>

  REPEAT (Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `env` thm))) >>
  REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pred_setTheory.UNION_ASSOC, bir_env_vars_are_initialised_UNION] >>

  FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>
  Cases_on `bir_eval_exp prem env = bir_val_true` >> Cases_on `bir_eval_exp e1 env = bir_val_true` >> Cases_on `bir_eval_exp e2 env = bir_val_true` >> (
    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm] >>
    FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_imm_expTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_imm_expTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_imm_expTheory.bir_unary_exp_GET_OPER_def, bir_imm_expTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
    blastLib.BBLAST_TAC >>
    EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
    FULL_SIMP_TAC std_ss []
  )  
);

(* --------------------------------------------- more ------------------------------------------------ *)

(* TODO: should be in bir_exp_substitutionsTheory *)

(*

val thm = SIMP_CONV (std_ss) [bir_exp_subst_update_REWRS] ``bir_exp_subst_update (FUPDATE (FUPDATE FEMPTY (BVar "h" (BType_Imm Bit8),BExp_Den (BVar "h1" (BType_Imm Bit8)))) (BVar "k" (BType_Imm Bit8),BExp_Den (BVar "k1" (BType_Imm Bit8)))) (FUPDATE FEMPTY (BVar "h1" (BType_Imm Bit8),BExp_Den (BVar "h1" (BType_Imm Bit16))))``;
val thm = TRANS thm ((EVAL o snd o dest_eq o concl) thm);


*)

val bir_exp_subst_update_def = Define `
  bir_exp_subst_update s f = FUN_FMAP (\x. f (FAPPLY s x)) (FDOM s)
`;

val bir_exp_subst_update_REWRS = store_thm("bir_exp_subst_update_REWRS",``
  (!f. bir_exp_subst_update FEMPTY f = FEMPTY) /\
  (!s v ve f. bir_exp_subst_update (FUPDATE s (v,ve)) f = FUPDATE (bir_exp_subst_update s f) (v, f ve))
``,

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_subst_update_def, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FUN_FMAP_EMPTY]
  ) >>

  REPEAT STRIP_TAC >>

  REWRITE_TAC [finite_mapTheory.fmap_EXT] >>

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_subst_update_def] >>
    METIS_TAC [finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FDOM_FUPDATE]
  ) >>

  SIMP_TAC std_ss [bir_exp_subst_update_def, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE] >>
  REWRITE_TAC [finite_mapTheory.FDOM_FUPDATE] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC std_ss [finite_mapTheory.FAPPLY_FUPDATE_THM, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE] >>
    Cases_on `x = v` >> (
      ASM_SIMP_TAC std_ss []
    )
  )
);

val bir_exp_varsubst_to_subst_def = Define `
  bir_exp_varsubst_to_subst vs = FUN_FMAP (\(x:bir_var_t). BExp_Den (FAPPLY vs x)) (FDOM vs)
`;

val bir_exp_varsubst_to_subst_REWRS = store_thm("bir_exp_subst_update_REWRS",``
  (bir_exp_varsubst_to_subst FEMPTY = FEMPTY) /\
  (!vs v v'. bir_exp_varsubst_to_subst (FUPDATE vs (v,v')) = FUPDATE (bir_exp_varsubst_to_subst vs) (v, BExp_Den v'))
``,

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_varsubst_to_subst_def, finite_mapTheory.FDOM_FEMPTY, finite_mapTheory.FUN_FMAP_EMPTY]
  ) >>

  REPEAT STRIP_TAC >>

  REWRITE_TAC [finite_mapTheory.fmap_EXT] >>

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_varsubst_to_subst_def] >>
    METIS_TAC [finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FDOM_FUPDATE]
  ) >>

  SIMP_TAC std_ss [bir_exp_varsubst_to_subst_def, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE] >>
  REWRITE_TAC [finite_mapTheory.FDOM_FUPDATE] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC std_ss [finite_mapTheory.FAPPLY_FUPDATE_THM, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE] >>
    Cases_on `x = v` >> (
      ASM_SIMP_TAC std_ss []
    )
  )
);

val bir_exp_varsubst_def = Define `
  bir_exp_varsubst vs = bir_exp_subst (bir_exp_varsubst_to_subst vs)
`;

val bir_exp_varsubst1_def = Define `
  bir_exp_varsubst1 v v' = bir_exp_varsubst (FUPDATE FEMPTY (v,v'))
`;

val bir_exp_varsubst1_REWR = store_thm("bir_exp_varsubst1_REWR", ``
  !v v'. bir_exp_varsubst1 v v' = bir_exp_subst1 v (BExp_Den v')
``,

  REWRITE_TAC [bir_exp_varsubst1_def, bir_exp_varsubst_def, bir_exp_varsubst_to_subst_REWRS, bir_exp_subst1_def]
);


(*
(* TODO, for doing this directly on expressions *)
val bir_exp_varsubst_REWRS = store_thm("bir_exp_varsubst_REWRS", ``

  (!e vs. bir_exp_varsubst (FUPDATE vs ) e = e)
``,

  cheat
);
*)



val bir_exp_subst_restrict_def = Define `
  bir_exp_subst_restrict s1 s2 = DRESTRICT s1 (COMPL (FDOM s2))
`;

val bir_exp_subst_restrict1_def = Define `
  bir_exp_subst_restrict1 s v = DRESTRICT s (COMPL {v})
`;

val bir_exp_subst_restrict1_REWRS = store_thm("bir_exp_subst_restrict1_REWRS",``
  (!v.            bir_exp_subst_restrict1 FEMPTY v = FEMPTY) /\
  (!s v1 ve1 v2. bir_exp_subst_restrict1 (FUPDATE s (v1,ve1)) v2 =
                     let s' = bir_exp_subst_restrict1 s v2 in
                     if v1 = v2 then s' else FUPDATE s' (v1,ve1)
  )
``,

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_subst_restrict1_def, finite_mapTheory.DRESTRICT_FEMPTY]
  ) >>

  REPEAT STRIP_TAC >>
  REWRITE_TAC [finite_mapTheory.fmap_EXT] >>

  CONJ_TAC >- (
    REWRITE_TAC [bir_exp_subst_restrict1_def, LET_DEF, finite_mapTheory.DRESTRICT_FUPDATE] >>
    SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ) >>

  SIMP_TAC std_ss [bir_exp_subst_restrict1_def, LET_DEF, finite_mapTheory.DRESTRICT_FUPDATE] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  METIS_TAC []
);

val bir_exp_subst_restrict_REWRS = store_thm("bir_exp_subst_restrict_REWRS",``
  (!s2.           bir_exp_subst_restrict FEMPTY s2 = FEMPTY) /\
  (!s1.           bir_exp_subst_restrict s1 FEMPTY = s1) /\
  (!s1 s2 v ve.   bir_exp_subst_restrict s1 (FUPDATE s2 (v,ve)) =
                     bir_exp_subst_restrict (bir_exp_subst_restrict1 s1 v) s2
  )
``,

  REPEAT (CONJ_TAC >- (
    REWRITE_TAC [bir_exp_subst_restrict_def, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FDOM_FEMPTY, pred_setTheory.COMPL_EMPTY, finite_mapTheory.DRESTRICT_UNIV]
  )) >>

  REPEAT STRIP_TAC >>
  REWRITE_TAC [finite_mapTheory.fmap_EXT] >>

  CONJ_TAC >> (
    REWRITE_TAC [bir_exp_subst_restrict_def, bir_exp_subst_restrict1_def, LET_DEF, finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.DRESTRICT_DRESTRICT, GSYM pred_setTheory.COMPL_UNION] >>
    METIS_TAC [pred_setTheory.INSERT_SING_UNION]
  )
);

val bir_exp_subst_subst_eq_restrict_thm = store_thm("bir_exp_subst_subst_eq_restrict_thm", ``
    !s1 s2 e.
      (!v. (v IN (FDOM s2)) ==> (FEVERY (\(_, ve). ~(v IN (bir_vars_of_exp ve))) s2)) ==>
      (
       bir_exp_subst s1 (bir_exp_subst s2 e)
       =
       bir_exp_subst (bir_exp_subst_restrict s1 s2) (bir_exp_subst s2 e)
      )
``,

  REWRITE_TAC [bir_exp_subst_restrict_def] >>

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    SIMP_TAC std_ss [bir_exp_subst_def]
  ) >- (
    Cases_on `b IN (FDOM s2)` >> (
      ASM_SIMP_TAC std_ss [bir_exp_subst_var_def, finite_mapTheory.FLOOKUP_DEF, bir_exp_subst_def, finite_mapTheory.FDOM_DRESTRICT, pred_setTheory.IN_INTER, pred_setTheory.IN_COMPL, finite_mapTheory.DRESTRICT_DEF]
    ) >>

    FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_DEF, boolTheory.PULL_FORALL] >>
    Q.PAT_X_ASSUM `!v. A` (ASSUME_TAC o (Q.GEN `v`) o (Q.SPECL [`v`, `b`])) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    FULL_SIMP_TAC std_ss [Once boolTheory.MONO_NOT_EQ] >>
    FULL_SIMP_TAC std_ss [GSYM pred_setTheory.IN_COMPL, GSYM pred_setTheory.SUBSET_DEF, bir_exp_subst_UNUSED_VARS_OVERAPPROX]
  ) >> (
    METIS_TAC []
  )
);

val bir_exp_subst_UNUSED_VARS_IMP = store_thm("bir_exp_subst_UNUSED_VARS_IMP", ``
  !s e.
    ((bir_vars_of_exp e) SUBSET (COMPL (FDOM s))) ==>
    (bir_exp_subst s e = e)
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_exp_subst_def, bir_exp_subst_var_def, bir_vars_of_exp_def, pred_setTheory.UNION_SUBSET]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [GSYM finite_mapTheory.flookup_thm]
);

val bir_exp_subst_subst_swap_thm = store_thm("bir_exp_subst_subst_swap_thm", ``
    !s1 s2 e.
      (!v. (v IN (FDOM s2)) ==> (FEVERY (\(_, ve). ~(v IN (bir_vars_of_exp ve))) s1)) ==>
      (
       bir_exp_subst s1 (bir_exp_subst s2 e)
       =
       bir_exp_subst (bir_exp_subst_update s2 (bir_exp_subst s1)) (bir_exp_subst (bir_exp_subst_restrict s1 s2) e)
      )
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_exp_subst_def, bir_exp_subst_update_def, bir_exp_subst_restrict_def, bir_exp_subst_var_def]
  ) >>

  Cases_on `b IN (FDOM s2)` >> (
    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DRESTRICT, pred_setTheory.IN_COMPL, finite_mapTheory.FLOOKUP_DEF, bir_exp_subst_def, bir_exp_subst_var_def, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE]
  ) >>

  Cases_on `b IN (FDOM s1)` >> (
    FULL_SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_DRESTRICT, pred_setTheory.IN_COMPL, finite_mapTheory.FLOOKUP_DEF, bir_exp_subst_def, bir_exp_subst_var_def, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE]
  ) >>

  FULL_SIMP_TAC std_ss [finite_mapTheory.FEVERY_DEF, boolTheory.PULL_FORALL] >>
  Q.PAT_X_ASSUM `!v. A` (ASSUME_TAC o (Q.GEN `v`) o (Q.SPECL [`v`, `b`])) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [Once boolTheory.MONO_NOT_EQ] >>
  FULL_SIMP_TAC std_ss [GSYM pred_setTheory.IN_COMPL, GSYM pred_setTheory.SUBSET_DEF, bir_exp_subst_UNUSED_VARS_OVERAPPROX] >>

  FULL_SIMP_TAC std_ss [bir_exp_subst_UNUSED_VARS_IMP, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE]
);

val bir_exp_varsubst_restrict_thm = store_thm("bir_exp_varsubst_restrict_thm", ``
    !vs s.
      bir_exp_varsubst (bir_exp_subst_restrict vs s) = bir_exp_subst (bir_exp_subst_restrict (bir_exp_varsubst_to_subst vs) s)
``,

  REWRITE_TAC [bir_exp_varsubst_def, bir_exp_subst_restrict_def, bir_exp_varsubst_to_subst_def] >>

  REPEAT STRIP_TAC >>
  AP_TERM_TAC >>

  SIMP_TAC std_ss [finite_mapTheory.fmap_EXT] >>
  CONJ_TAC >> (
    SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.DRESTRICT_DEF, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FDOM_DRESTRICT]
  )
);

val bir_exp_varsubst_subst_swap_thm = store_thm("bir_exp_varsubst_subst_swap_thm", ``
  !vs s e.
    (!v. (v IN (FDOM s)) ==> (FEVERY (\(_, v'). v <> v') vs)) ==>
    (
     bir_exp_varsubst vs (bir_exp_subst s e)
     =
     bir_exp_subst (bir_exp_subst_update s (bir_exp_varsubst vs)) (bir_exp_varsubst (bir_exp_subst_restrict vs s) e)
    )
``,

  REPEAT STRIP_TAC >>

  REWRITE_TAC [bir_exp_varsubst_restrict_thm, bir_exp_varsubst_def, bir_exp_varsubst_to_subst_def] >>

  subgoal `!v. (v IN (FDOM s)) ==> (FEVERY (\(_, ve). ~(v IN (bir_vars_of_exp ve))) ((FUN_FMAP (λx. BExp_Den (vs ' x)) (FDOM vs))))` >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FEVERY_DEF, finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, bir_vars_of_exp_def]
  ) >>

  ASM_SIMP_TAC std_ss [bir_exp_subst_subst_swap_thm]
);

val bir_exp_varsubst_subst1_swap_thm = store_thm("bir_exp_varsubst_subst1_swap_thm", ``
  !vs v ve e.
    (FEVERY (\(_, v'). v <> v') vs) ==>
    (
     bir_exp_varsubst vs (bir_exp_subst1 v ve e)
     =
     bir_exp_subst1 v (bir_exp_varsubst vs ve) (bir_exp_varsubst (bir_exp_subst_restrict1 vs v) e)
    )
``,

  REPEAT STRIP_TAC >>

  REWRITE_TAC [bir_exp_subst1_def, bir_exp_subst_restrict1_def] >>
  REWRITE_TAC [(GSYM o (SIMP_CONV std_ss [bir_exp_subst_update_REWRS])) ``bir_exp_subst_update (FEMPTY |+ (v,ve)) (bir_exp_varsubst vs)``] >>

  Q.ABBREV_TAC `s = (FEMPTY |+ (v,ve))` >>
  subgoal `{v} = FDOM s` >- (
    FULL_SIMP_TAC std_ss [Abbr `s`] >>
    EVAL_TAC
  ) >>
  ASM_SIMP_TAC std_ss [GSYM bir_exp_subst_restrict_def] >>

  subgoal `!v. (v IN (FDOM s)) ==> (FEVERY (\(_, v'). v <> v') vs)` >- (
    METIS_TAC [pred_setTheory.IN_SING]
  ) >>

  ASM_SIMP_TAC std_ss [bir_exp_varsubst_subst_swap_thm]
);

val bir_exp_varsubst1_varsubst_merge_thm = store_thm("bir_exp_varsubst1_varsubst_merge_thm", ``
  !v v' vs e.
    bir_exp_varsubst1 v v' (bir_exp_varsubst vs e) =
     let vs' = bir_exp_subst_update vs (\x. if x = v then v' else x) in
      bir_exp_varsubst (if v IN (FDOM vs') then vs' else FUPDATE (vs') (v,v')) e
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [LET_DEF, bir_exp_varsubst_def, bir_exp_varsubst1_REWR, bir_exp_varsubst_to_subst_def, bir_exp_subst_update_def, bir_exp_subst_def, bir_exp_subst1_def, bir_exp_subst_var_def]
  ) >>

  Cases_on `v IN (FDOM vs)` >> Cases_on `b IN (FDOM vs)` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FLOOKUP_FUN_FMAP, bir_exp_subst_def, bir_exp_subst1_def, bir_exp_subst_var_def, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >>
    CASE_TAC >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FUN_FMAP_DEF, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FAPPLY_FUPDATE, finite_mapTheory.FAPPLY_FUPDATE_THM]
    )
  ) >>

  subgoal `v <> b` >- (
    CCONTR_TAC >>
    FULL_SIMP_TAC std_ss []
  ) >>

  ASM_SIMP_TAC std_ss []
);



(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)


(*
val bir_wp_simp_prem_indep_def = Define `
      bir_wp_simp_prem_indep prem vn =
        !sm vt vo. prem (BEnv (FUPDATE sm (vn, (vt, vo)))) = prem (BEnv sm)
`;

val bir_wp_simp_eval_subst1_thm = store_thm("bir_wp_simp_eval_subst1_thm", ``
    !v ve v' e prem.
      (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
      (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (bir_wp_simp_prem_indep prem (bir_var_name v')) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst1 v ve e) s = bir_val_true))
       <=>
       (!s. ((prem s) /\
             (bir_eval_exp (BExp_Den v') s = bir_eval_exp ve s)
(*           (bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den v') ve) s = bir_val_true)*)
            )
            ==>
            (bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) s = bir_val_true)
       )
      )
``,


  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

    Q.PAT_X_ASSUM `!s.P s` (fn thm => ASSUME_TAC (Q.SPEC `s` thm)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

 (*   FULL_SIMP_TAC std_ss [bir_wp_simp_eval_binpred_eq_thm] >>*)
    METIS_TAC [bir_exp_subst1_EVAL_EQ_GEN]
  ) >>

  REPEAT STRIP_TAC >>

  Cases_on `s` >>
  Q.RENAME1_TAC `BEnv sm` >>

  Q.ABBREV_TAC `sm' = FUPDATE sm (bir_var_name v', (bir_var_type v', SOME (bir_eval_exp ve (BEnv sm))))` >>

  subgoal `prem (BEnv sm')` >- (
    METIS_TAC [bir_wp_simp_prem_indep_def]
  ) >>

  subgoal `bir_eval_exp (BExp_Den v') (BEnv sm') = bir_eval_exp ve (BEnv sm')` >- (
    SIMP_TAC std_ss [Abbr `sm'`, bir_eval_exp_def, bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    ASM_SIMP_TAC (srw_ss()) [bir_eval_exp_indep_env_update_thm]
  ) >>

  subgoal  `bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm') = bir_val_true` >- (
    METIS_TAC [bir_exp_subst1_EVAL_EQ_GEN]
  ) >>

  METIS_TAC [bir_wp_simp_eval_subst1_lemma]
);



val bir_wp_simp_eval_subst_lemma = store_thm("bir_wp_simp_eval_subst_lemma", ``
    !substs vn' vt' vo' e sm.
      (FEVERY (\(_, t). ~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp t)))) substs) ==>
      (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
      (
       (bir_eval_exp (bir_exp_subst substs e) (BEnv sm))
       =
       (bir_eval_exp (bir_exp_subst substs e) (BEnv (FUPDATE sm (vn', (vt', vo')))))
      )
``,

(*
  REPEAT STRIP_TAC >>
*)

  cheat
);


(* TODO: should probably be somewhere else *)
val bir_exp_conj_from_list_def = Define `
  bir_exp_conj_from_list = FOLDL (\expa. \exp. BExp_BinExp BIExp_And expa exp) (BExp_Const (Imm1 1w))
`;


val bir_wp_simp_eval_subst_thm = store_thm("bir_wp_simp_eval_subst_thm", ``
    !vvtl vtm vvm bconj e prem.
      (vtm = FUPDATE_LIST FEMPTY (MAP (\(v, _, t). (v, t)) vvtl)) ==>
      (vvm = FUPDATE_LIST FEMPTY (MAP (\(v, v', _). (v, v')) vvtl)) ==>
      (bconj = bir_exp_conj_from_list (MAP (\(_, v', t). BExp_BinPred BIExp_Equal (BExp_Den v') t) vvtl)) ==>
      (EVERY (\v'. ~(v' IN (bir_vars_of_exp e)) /\ EVERY (\t. ~(v' IN (bir_vars_of_exp t))) (MAP (\(_, _, t). t) vvtl))) (MAP (\(_, v', _). v') vvtl) ==>
      (
       (!s. (prem s) ==> (bir_eval_exp (bir_exp_subst vtm e) s = bir_val_true))
       <=>
       (!s. ((prem s) /\
             (bir_eval_exp bconj s = bir_val_true)
            )
            ==>
            (bir_eval_exp (bir_exp_subst (bir_exp_varsubst vvm) e) s = bir_val_true)
       )
      )
``,

(*
  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

  ) >>
*)
  cheat
);
*)
















val _ = export_theory();

