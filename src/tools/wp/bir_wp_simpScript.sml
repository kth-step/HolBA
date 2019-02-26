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
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>

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

  SIMP_TAC (std_ss) [bir_exp_immTheory.type_of_bir_unary_exp]
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
    ASM_SIMP_TAC (std_ss++bir_val_ss++bir_imm_ss) [bool2b_def, bool2w_def, bir_exp_immTheory.type_of_bir_bin_exp]
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

val bir_eval_exp_not_false_true_thm = store_thm("bir_eval_exp_not_false_true_thm", ``
    !e env.
     (bir_is_bool_exp e) ==>
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
     (
      (bir_eval_exp e env <> bir_val_false)
      <=>
      (bir_eval_exp e env = bir_val_true)
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
        METIS_TAC [bir_exp_immTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_exp_immTheory.bir_bin_exp_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] >>

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
      METIS_TAC [bir_exp_imp_def, bir_val_true_def, bir_wp_simp_eval_bin_is_Imm_s_thm, bir_val_checker_REWRS, type_of_bir_imm_def, bir_exp_immTheory.type_of_bir_bin_exp]
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
        METIS_TAC [bir_exp_immTheory.type_of_bir_bin_exp, type_of_bir_imm_def]
      ) >>

      Cases_on `b` >> Cases_on `b'` >> (
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_immTheory.type_of_bir_imm_def]
      ) >>

      FULL_SIMP_TAC (std_ss++bir_imm_ss) [bir_exp_immTheory.bir_bin_exp_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] >>

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
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_GET_OPER_def] >>
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
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
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
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
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
    FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
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

val bir_vars_of_exp_FINITE_thm = store_thm("bir_vars_of_exp_FINITE_thm", ``
  !e. FINITE (bir_vars_of_exp e)
``,

  Induct_on `e` >> (
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pred_setTheory.FINITE_EMPTY, pred_setTheory.FINITE_SING, pred_setTheory.FINITE_UNION]
  )
);

val UNION_DIFF_same_thm = prove(``
  !a b. (a UNION (b DIFF a)) = (a UNION b)
``,

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.DIFF_DEF, pred_setTheory.UNION_DEF, prove(``!a b. a \/ (b /\ (~a)) = a \/ b``, METIS_TAC[])]  
);

(*
val bir_env_initialise_vars_def = Define `
      bir_env_initialise_vars (BEnv sm) vs = BEnv (FMERGE (K)
              (FUN_FMAP (\x. case (CHOICE ({ v | ?xt. (v IN vs) /\ (v = BVar x xt) })) of
			       | (BVar _ vt) => (vt, SOME (bir_default_value_of_type vt)))
                        ({ vn | ?vt. (BVar vn vt) IN vs }))
	      sm)
`;

val bir_env_initialise_vars_EMPTY_thm = store_thm("bir_env_initialise_vars_EMPTY_thm", ``
      !env.
        ((bir_env_initialise_vars env EMPTY) = env)
``,

  Cases_on `env` >>

  REWRITE_TAC [bir_env_initialise_vars_def] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [finite_mapTheory.FUN_FMAP_EMPTY, finite_mapTheory.FMERGE_FEMPTY]
);

(*
val bir_env_initialise_vars_UNION_thm = store_thm("bir_env_initialise_vars_UNION_thm", ``
      !vs1 vs2 env.
        () ==>
        (
         (bir_env_initialise_vars env (vs1 UNION vs2)) =
         (bir_env_initialise_vars (bir_env_initialise_vars env vs1) vs2)
        )
``,

  Cases_on `env` >>
  REWRITE_TAC [bir_env_initialise_vars_def] >>


(*
finite_mapTheory.FMERGE_DEF
K_DEF
*)
);
*)

val bir_env_initialise_vars_ORDER_thm = store_thm("bir_env_initialise_vars_ORDER_thm", ``
      !vs env.
        (bir_env_order env (bir_env_initialise_vars env vs))
``,

  cheat
(*
bir_env_order_def
*)
);


(*
!!!!!!!!!!!!!!!!

!!!!!!!!!!!!!!!!
*)

(* ======================= *)

val bir_env_initialise_vars_inited1_thm = store_thm("bir_env_initialise_vars_inited1_thm", ``
      !vs1 vs2 env.
        (FINITE vs2) ==>
        (bir_var_set_is_well_typed vs2) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env vs2) vs2)
``,

  REWRITE_TAC [bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>

  Cases_on `env` >>
  Q.RENAME1_TAC `BEnv sm` >>

  REWRITE_TAC [bir_env_initialise_vars_def] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []



  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) []


bir_var_set_is_well_typed_def
bir_env_var_is_initialised_def
);



val bir_env_initialise_vars_inited_thm = store_thm("bir_env_initialise_vars_inited_thm", ``
      !vs1 vs2 env.
        (bir_env_vars_are_initialised env vs1) ==>
        (FINITE vs2) ==>
        (bir_var_set_is_well_typed (vs1 UNION vs2)) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env vs2)
                                      (vs1 UNION vs2))
``,

  REPEAT STRIP_TAC >>

  SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>

  CONJ_TAC >- (
    METIS_TAC [bir_env_vars_are_initialised_ORDER, bir_env_initialise_vars_ORDER_thm]
  ) >>

  METIS_TAC [bir_env_initialise_vars_inited1_thm, bir_var_set_is_well_typed_UNION]
);

(*
(*
this is a special case of the one above
*)
val bir_env_initialise_vars_inited_thm = store_thm("bir_env_initialise_vars_inited_thm", ``
      !vs env.
        (bir_var_set_is_well_typed vs) ==>
        (FINITE vs) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env vs) vs)
``,

  cheat
);
*)

(*
this is a special case as well
*)
val bir_env_initialise_vars_inited_DIFF_thm = store_thm("bir_env_initialise_vars_inited_DIFF_thm", ``
      !vs1 vs2 env.
        (bir_env_vars_are_initialised env vs1) ==>
        (FINITE vs2) ==>
        (bir_var_set_is_well_typed (vs1 UNION vs2)) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env (vs2 DIFF vs1))
                                      (vs1 UNION vs2))
``,

  REPEAT STRIP_TAC >>
  ASSUME_TAC (Q.SPECL [`vs1`, `vs2 DIFF vs1`, `env`] bir_env_initialise_vars_inited_thm) >>
  METIS_TAC [UNION_DIFF_same_thm, pred_setTheory.FINITE_DIFF]
);

(*
this is a special case as well
*)
val bir_env_initialise_vars_inited_DIFF2_thm = store_thm("bir_env_initialise_vars_inited_DIFF2_thm", ``
      !vs vs1 env.
        (bir_env_vars_are_initialised env vs1) ==>
        (vs1 SUBSET vs) ==>
        (FINITE vs) ==>
        (bir_var_set_is_well_typed vs) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env (vs DIFF vs1))
                                      (vs))
``,

  REPEAT STRIP_TAC >>
  ASSUME_TAC (Q.SPECL [`vs1`, `vs DIFF vs1`, `env`] bir_env_initialise_vars_inited_thm) >>
  METIS_TAC [pred_setTheory.UNION_DIFF, pred_setTheory.FINITE_DIFF]
);

(*
this is a special case as well
*)
val bir_env_initialise_vars_inited_exp_thm = store_thm("bir_env_initialise_vars_inited_exp_thm", ``
      !vs1 e2 env.
        (bir_env_vars_are_initialised env vs1) ==>
        (bir_var_set_is_well_typed (vs1 UNION (bir_vars_of_exp e2))) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env (bir_vars_of_exp e2))
                                      (vs1 UNION (bir_vars_of_exp e2)))
``,

  METIS_TAC [bir_env_initialise_vars_inited_thm, bir_vars_of_exp_FINITE_thm]
);

(*
this is a special case as well
*)
val bir_env_initialise_vars_inited_DIFF_exp_thm = store_thm("bir_env_initialise_vars_inited_DIFF_exp_thm", ``
      !vs1 e2 env.
        (bir_env_vars_are_initialised env vs1) ==>
        (bir_var_set_is_well_typed (vs1 UNION (bir_vars_of_exp e2))) ==>
        (bir_env_vars_are_initialised (bir_env_initialise_vars env ((bir_vars_of_exp e2) DIFF vs1))
                                      (vs1 UNION (bir_vars_of_exp e2)))
``,

  METIS_TAC [bir_env_initialise_vars_inited_DIFF_thm, bir_vars_of_exp_FINITE_thm]
);


(*
bir_env_initialise_vars_INTER_EMPTY_thm
*)

(* ======================= *)
(*
bir_typing_expTheory.bir_var_set_is_well_typed_SUBSET
bir_env_vars_are_initialised_UNION
*)
(*
val bir_env_initialise_vars_DIFF_eval_eq_thm = store_thm("bir_env_initialise_vars_DIFF_eval_eq_thm", ``
      !vs1 vs2 env env'.
        (FINITE vs2) ==>
        (env' = (bir_env_initialise_vars env (vs2 DIFF vs1))) ==>
        (
         (!v. (v IN vs1) ==> (bir_env_lookup (bir_var_name v) env' = bir_env_lookup (bir_var_name v) env)) /\
         (!v. (v IN (vs2 DIFF vs1)) ==> (bir_env_lookup (bir_var_name v) env' = SOME (bir_var_type v, SOME (bir_default_value_of_type (bir_var_type v)))))
        )
``,

  cheat
);
*)

val bir_env_initialise_vars_DIFF_eval_exp_thm = store_thm("bir_env_initialise_vars_DIFF_eval_exp_thm", ``
      !e vs1 e2 env.
        ((bir_vars_of_exp e) SUBSET vs1) ==>
        (bir_eval_exp e (bir_env_initialise_vars env ((bir_vars_of_exp e2) DIFF vs1)) = bir_eval_exp e env)
``,

  cheat
);
*)


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
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]

    ) >| [
(*
      Q.ABBREV_TAC `env' = bir_env_initialise_vars env ((bir_vars_of_exp e2) DIFF ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1)))`
*)
      Q.ABBREV_TAC `vs = (bir_vars_of_exp prem) UNION (bir_vars_of_exp e1)` >>
      Q.ABBREV_TAC `e = (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e1)`
    ,
      Q.ABBREV_TAC `vs = (bir_vars_of_exp prem) UNION (bir_vars_of_exp e2)` >>
      Q.ABBREV_TAC `e = (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e2)`
    ] >> (

      REV_FULL_SIMP_TAC std_ss [pred_setTheory.UNION_ASSOC] >>
      Q.ABBREV_TAC `vs2 = (bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2)` >>

      ASSUME_TAC (Q.SPECL [`vs`, `vs2`, `env`] bir_env_vars_are_initialised_ENV_EXISTS_EXTENSION) >>

      subgoal `FINITE vs2` >- (
        METIS_TAC [bir_vars_of_exp_FINITE_thm, pred_setTheory.FINITE_UNION]
      ) >>

      subgoal `vs SUBSET vs2` >- (
        METIS_TAC [pred_setTheory.SUBSET_UNION, pred_setTheory.UNION_ASSOC, pred_setTheory.UNION_COMM]
      ) >>

      subgoal `bir_env_vars_are_initialised env vs` >- (
        METIS_TAC [bir_env_vars_are_initialised_UNION]
      ) >>

      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [] >>

(*
      Cases_on `env'` >>
      Q.RENAME1_TAC `BEnv sm' ` >>
      Cases_on `env` >>
      Q.RENAME1_TAC `BEnv sm` >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
*)
(*
      subgoal `(bir_env_vars_are_initialised env' (bir_vars_of_exp prem)) /\
               (bir_env_vars_are_initialised env' (bir_vars_of_exp e1)) /\
               (bir_env_vars_are_initialised env' (bir_vars_of_exp e2))` >- (

(*
        subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1))` >- (
          METIS_TAC [bir_env_vars_are_initialised_UNION]
        ) >>
*)

(*
        subgoal `bir_var_set_is_well_typed (((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1)) UNION bir_vars_of_exp e2)` >- (
          METIS_TAC [pred_setTheory.UNION_ASSOC]
        ) >>

        subgoal `bir_env_vars_are_initialised env' (((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1)) UNION bir_vars_of_exp e2)` >- (
          METIS_TAC [bir_env_initialise_vars_inited_DIFF_exp_thm, Abbr `env'`]
        ) >>
*)

        METIS_TAC [Abbr `env'`, bir_env_initialise_vars_inited_DIFF_exp_thm, bir_env_vars_are_initialised_UNION, pred_setTheory.UNION_ASSOC]
(*, pred_setTheory.UNION_COMM*)
(*bir_env_initialise_vars_init_exp_thm*)
(*bir_env_initialise_vars_inited_thm, *)

(* uncheat *)
(*cheat*)
(*
FULL_SIMP_TAC std_ss [bir_env_initialise_vars_init_exp_thm]
*)
      ) >>
*)

      subgoal `(bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) (BExp_BinExp BIExp_And e1 e2)) env2 = bir_val_true)` >- (
        METIS_TAC [bir_env_vars_are_initialised_UNION]
      ) >>
      Q.PAT_X_ASSUM `!env. A` (K ALL_TAC) >>

      REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pred_setTheory.UNION_ASSOC, bir_env_vars_are_initialised_UNION] >>
      FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

      subgoal `bir_eval_exp e env = bir_eval_exp e env2` >- (

        subgoal `bir_vars_of_exp e = vs` >- (
          METIS_TAC [bir_vars_of_exp_def]
        ) >>

        METIS_TAC [bir_typing_expTheory.bir_vars_of_exp_THM_EQ_FOR_VARS]
      ) >>

(*
    ) >| [
(*
bir_env_EQ_FOR_VARS_def

        subgoal `bir_vars_of_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e1) SUBSET ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1))` >- (
          METIS_TAC [bir_vars_of_exp_def, pred_setTheory.SUBSET_REFL]
        ) >>

        METIS_TAC [GSYM bir_env_initialise_vars_DIFF_eval_exp_thm, Abbr `env'`]
      
*)
    ,
      subgoal `bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e2) env = bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e2) env'` >- (

(* uncheated, see above *)
        subgoal `bir_vars_of_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem) e2) SUBSET ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e2))` >- (
          METIS_TAC [bir_vars_of_exp_def, pred_setTheory.SUBSET_REFL]
        ) >>

        METIS_TAC [GSYM bir_env_initialise_vars_DIFF_eval_exp_thm, Abbr `env'`]

      )
    ] >> (
*)

      FULL_SIMP_TAC std_ss [Abbr `e`, Abbr `vs`, Abbr `vs2`, bir_env_vars_are_initialised_UNION] >>

      Cases_on `bir_eval_exp prem env2 = bir_val_true` >> Cases_on `bir_eval_exp e1 env2 = bir_val_true` >> Cases_on `bir_eval_exp e2 env2 = bir_val_true` >> (
        Q.PAT_X_ASSUM `bir_eval_exp (BExp_BinExp A B C) D = bir_val_true` ASSUME_TAC >>

        REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
        REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>

        blastLib.BBLAST_TAC >>
        POP_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

        blastLib.BBLAST_TAC >>
        FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
      )
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
    FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
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

val bir_exp_varsubst_to_subst_REWRS = store_thm("bir_exp_varsubst_to_subst_REWRS",``
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

val bir_exp_varsubst_var_def = Define `
  bir_exp_varsubst_var vs = bir_exp_subst_var (bir_exp_varsubst_to_subst vs)
`;

val bir_exp_varsubst_var_REWR = store_thm("bir_exp_varsubst_var_REWR", ``
  !vs v. bir_exp_varsubst_var vs v = case FLOOKUP vs v of NONE => BExp_Den v | SOME e => BExp_Den e
``,

  REWRITE_TAC [bir_exp_varsubst_var_def, bir_exp_varsubst_to_subst_def, bir_exp_subst_var_def] >>

  SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_FUN_FMAP, finite_mapTheory.FDOM_FINITE] >>

  REPEAT STRIP_TAC >>
  Cases_on `FLOOKUP vs v` >> (
    FULL_SIMP_TAC std_ss [finite_mapTheory.flookup_thm]
  )
);

(* rewrites for doing this directly on expressions *)
val bir_exp_varsubst_REWRS = store_thm("bir_exp_varsubst_REWRS", ``
  (!vs n. bir_exp_varsubst vs (BExp_Const n) = BExp_Const n) /\
  (!vs v. bir_exp_varsubst vs (BExp_Den v) = bir_exp_varsubst_var vs v) /\
  (!vs ct e ty.
      bir_exp_varsubst vs (BExp_Cast ct e ty) =
      BExp_Cast ct (bir_exp_varsubst vs e) ty) /\
  (!vs et e.
      bir_exp_varsubst vs (BExp_UnaryExp et e) =
      BExp_UnaryExp et (bir_exp_varsubst vs e)) /\
  (!vs et e1 e2.
      bir_exp_varsubst vs (BExp_BinExp et e1 e2) =
      BExp_BinExp et (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs pt e1 e2.
      bir_exp_varsubst vs (BExp_BinPred pt e1 e2) =
      BExp_BinPred pt (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs me1 me2.
      bir_exp_varsubst vs (BExp_MemEq me1 me2) =
      BExp_MemEq (bir_exp_varsubst vs me1) (bir_exp_varsubst vs me2)) /\
  (!vs c et ef.
      bir_exp_varsubst vs (BExp_IfThenElse c et ef) =
      BExp_IfThenElse (bir_exp_varsubst vs c) (bir_exp_varsubst vs et)
        (bir_exp_varsubst vs ef)) /\
  (!vs mem_e a_e en ty.
      bir_exp_varsubst vs (BExp_Load mem_e a_e en ty) =
      BExp_Load (bir_exp_varsubst vs mem_e) (bir_exp_varsubst vs a_e) en ty) /\
  (!vs mem_e a_e en v_e.
     bir_exp_varsubst vs (BExp_Store mem_e a_e en v_e) =
     BExp_Store (bir_exp_varsubst vs mem_e) (bir_exp_varsubst vs a_e) en
       (bir_exp_varsubst vs v_e))
``,

  REWRITE_TAC [bir_exp_varsubst_def, bir_exp_varsubst_to_subst_def, bir_exp_subst_def, bir_exp_varsubst_var_def]
);
val bir_exp_varsubst_REWRS_ALT = store_thm("bir_exp_varsubst_REWRS_ALT", ``
  (!vs e1 e2.
      bir_exp_varsubst vs (bir_exp_and e1 e2) =
      bir_exp_and (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs e1 e2.
      bir_exp_varsubst vs (bir_exp_imp e1 e2) =
      bir_exp_imp (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs e1 e2.
      bir_exp_varsubst vs (bir_exp_or e1 e2) =
      bir_exp_or (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs e.
      bir_exp_varsubst vs (bir_exp_not e) =
      bir_exp_not (bir_exp_varsubst vs e))
``,

  REWRITE_TAC [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_varsubst_REWRS]
);



val bir_exp_varsubst_and_imp_REWRS = store_thm("bir_exp_varsubst_and_imp_REWRS", ``
  (!vs et e1 e2.
      bir_exp_varsubst vs (bir_exp_and e1 e2) =
      bir_exp_and (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2)) /\
  (!vs et e1 e2.
      bir_exp_varsubst vs (bir_exp_imp e1 e2) =
      bir_exp_imp (bir_exp_varsubst vs e1) (bir_exp_varsubst vs e2))
``,

  REWRITE_TAC [bir_exp_and_def, bir_exp_or_def, bir_exp_not_def, bir_exp_imp_def, bir_exp_varsubst_REWRS]
);




val bir_exp_varsubst_introduced_vars_def = Define `
  bir_exp_varsubst_introduced_vars vs vset =
    {v' | ?v. (v IN vset) /\ (FLOOKUP vs v = SOME v')}
`;

val bir_exp_varsubst_USED_VARS = store_thm("bir_exp_varsubst_USED_VARS", ``
  !vs e.
     bir_vars_of_exp (bir_exp_varsubst vs e) =
     bir_vars_of_exp e DIFF FDOM vs UNION
       (bir_exp_varsubst_introduced_vars vs (bir_vars_of_exp e))
``,

REWRITE_TAC [bir_exp_varsubst_introduced_vars_def] >>
GEN_TAC >>
SIMP_TAC std_ss [pred_setTheory.EXTENSION] >>
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [PULL_EXISTS] >>
Induct_on `e` >> (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_varsubst_def, bir_exp_subst_def, bir_vars_of_exp_def] >>
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [RIGHT_AND_OVER_OR,
    LEFT_AND_OVER_OR, EXISTS_OR_THM, bir_exp_subst_var_def]
) >>
REPEAT STRIP_TAC >>
CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++boolSimps.EQUIV_EXTRACT_ss) [
    bir_exp_varsubst_to_subst_def , bir_vars_of_exp_def, finite_mapTheory.flookup_thm, finite_mapTheory.FDOM_FINITE, finite_mapTheory.FUN_FMAP_DEF] >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FDOM_FINITE, finite_mapTheory.FUN_FMAP_DEF, bir_vars_of_exp_def] >>
  METIS_TAC[]
));


val bir_exp_varsubst_introduced_vars_REWRS = store_thm("bir_exp_varsubst_introduced_vars_REWRS", ``
  (!vset. bir_exp_varsubst_introduced_vars FEMPTY vset = {}) /\
  (!vs v v' vset. bir_exp_varsubst_introduced_vars (FUPDATE vs (v,v')) vset =
     (if (v IN vset) then {v'} else EMPTY) UNION
        (bir_exp_varsubst_introduced_vars vs (vset DIFF {v})))
``,

  REWRITE_TAC [bir_exp_varsubst_introduced_vars_def] >>
  SIMP_TAC std_ss [finite_mapTheory.FLOOKUP_EMPTY, pred_setTheory.GSPEC_F] >>

  SIMP_TAC std_ss [pred_setTheory.EXTENSION] >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [PULL_EXISTS] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>
    Cases_on `v = v''` >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FLOOKUP_UPDATE] >>
      METIS_TAC []
    )
  ) >>

  REPEAT STRIP_TAC >- (
    Cases_on `v IN vset` >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      Q.EXISTS_TAC `v` >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [finite_mapTheory.FLOOKUP_UPDATE]
    )
  ) >>
  METIS_TAC [finite_mapTheory.FLOOKUP_UPDATE]
);



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

  subgoal `!v. (v IN (FDOM s)) ==> (FEVERY (\(_, ve). ~(v IN (bir_vars_of_exp ve))) ((FUN_FMAP (\x. BExp_Den (vs ' x)) (FDOM vs))))` >- (
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

(* --------------------------------------------- more ------------------------------------------------ *)


(*
bir_var_set_is_well_typed_def

bir_var_set_is_well_typed
    ({BVar "SP_EL0" (BType_Imm Bit64)} ∪
     ({BVar "SP_EL0" (BType_Imm Bit64)} ∪
      ({BVar "MEM" (BType_Mem Bit64 Bit8)} ∪
       {BVar "SP_EL0" (BType_Imm Bit64)})))
*)

val SET_TO_LIST_SINGLETON_thm = save_thm("SET_TO_LIST_SINGLETON_thm",
  ((REWRITE_RULE [CONJUNCT1 listTheory.LIST_TO_SET, pred_setTheory.UNION_EMPTY]) o (Q.SPEC `[]`) o (Q.GENL [`t`, `h`]) o CONJUNCT2 o (REWRITE_RULE [Q.SPECL [`set t`, `h`] pred_setTheory.INSERT_SING_UNION]))
  (GSYM listTheory.LIST_TO_SET));

val bir_var_set_is_well_typed_REWRS = store_thm("bir_var_set_is_well_typed_REWRS", ``
  (bir_var_set_is_well_typed (set [])) /\
  (!v vs. bir_var_set_is_well_typed (set (v::vs)) =
     EVERY (\v'. (bir_var_name v = bir_var_name v') ==> (bir_var_type v = bir_var_type v')) vs /\
     bir_var_set_is_well_typed (set vs)
     )
``,

  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [listTheory.LIST_TO_SET, bir_var_set_is_well_typed_def]
  ) >>
  FULL_SIMP_TAC std_ss [listTheory.LIST_TO_SET, bir_var_set_is_well_typed_INSERT, listTheory.EVERY_MEM] >>
  METIS_TAC []
);


(* --------------------------------------------- more ------------------------------------------------ *)





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


(* --------------------------------------------- more ------------------------------------------------ *)


val bir_wp_simp_varset_imp_thm = store_thm("bir_wp_simp_varset_imp_thm", ``
  !prem e1 e2.
    (bir_vars_of_exp (
      bir_exp_imp prem (bir_exp_imp e1 e2)))
    =
    (bir_vars_of_exp (
      bir_exp_imp (bir_exp_and prem e1) e2))
    
``,

  REWRITE_TAC [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_vars_of_exp_def] >>
  METIS_TAC [pred_setTheory.UNION_ASSOC]
);

val bir_wp_simp_varset_imp_wunions_thm = store_thm("bir_wp_simp_varset_imp_wunions_thm", ``
  !prem e1 e2 A.
    ((bir_vars_of_exp prem) UNION (bir_vars_of_exp (bir_exp_imp e1 e2)) UNION A)
    =
    ((bir_vars_of_exp (bir_exp_and prem e1)) UNION (bir_vars_of_exp e2) UNION A)
``,

  REWRITE_TAC [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_vars_of_exp_def] >>
  METIS_TAC [pred_setTheory.UNION_ASSOC]
);

val bir_wp_simp_varset_and_helper0_thm = store_thm("bir_wp_simp_varset_and_helper0_thm", ``
  !prem e1 e2 A.
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp (bir_exp_and e1 e2)) UNION A)
    =
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION ((bir_vars_of_exp e2) UNION A))
``,

  METIS_TAC [bir_vars_of_exp_def, bir_exp_and_def, pred_setTheory.UNION_ASSOC]
);

val bir_wp_simp_varset_and_helper1_thm = store_thm("bir_wp_simp_varset_and_helper1_thm", ``
  !prem e1 e2 A.
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION ((bir_vars_of_exp e2) UNION A))
    =
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e2) UNION ((bir_vars_of_exp e1) UNION A))
``,

  METIS_TAC [pred_setTheory.UNION_ASSOC, pred_setTheory.UNION_COMM]
);

val bir_wp_simp_varset_and_helper2_thm = store_thm("bir_wp_simp_varset_and_helper2_thm", ``
  !prem e1 e1' e2 e2' A.
    (bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION ((bir_vars_of_exp e2) UNION A)))
    ==>
    (bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1') UNION ((bir_vars_of_exp e2') UNION A)))
    ==>
    (
      bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2))
      =
      bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1') UNION (bir_vars_of_exp e2'))
    )
``,

  REPEAT STRIP_TAC >>
  METIS_TAC [bir_typing_expTheory.bir_var_set_is_well_typed_SUBSET, pred_setTheory.UNION_ASSOC, pred_setTheory.SUBSET_UNION]
);

val bir_wp_simp_varset_and_helper3_thm = store_thm("bir_wp_simp_varset_and_helper3_thm", ``
  !prem e1 e2 A.
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION ((bir_vars_of_exp e2) UNION A))
    =
    bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2) UNION A)
``,

  METIS_TAC [pred_setTheory.UNION_ASSOC]
);

val bir_wp_simp_welltypedset_subst1_not_thm = store_thm("bir_wp_simp_welltypedset_subst1_not_thm", ``
  !prem v ve e A.
    (~(v IN bir_vars_of_exp e))
    ==>
    (
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem e)) UNION A)
    )
``,

  METIS_TAC [bir_exp_substitutionsTheory.bir_exp_subst1_UNUSED_VAR]
);

(* bir_exp_is_taut_imp_imp_subst1_thm *)
val bir_wp_simp_welltypedset_subst1_thm = store_thm("bir_wp_simp_welltypedset_subst1_thm", ``
  !prem v v' ve e A vs.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (
      !v. v IN vs ==> (bir_var_name v <> bir_var_name v')
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem
          (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
             (bir_exp_varsubst1 v v' e))
      )) UNION A)
    )
``,

  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vs2 = (bir_vars_of_exp
     (bir_exp_imp prem
        (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
           (bir_exp_varsubst1 v v' e))) UNION A)` >>

  Q.PAT_X_ASSUM `B = C` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC std_ss [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_vars_of_exp_def] >>

  FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS, bir_exp_varsubst1_def, bir_exp_varsubst_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FDOM_FEMPTY] >>

  REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  subgoal `vs2 = {v'} UNION vs` >- (
    METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.UNION_ASSOC, pred_setTheory.UNION_IDEMPOT]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.INSERT_UNION_EQ] >>
  METIS_TAC [bir_var_set_is_well_typed_INSERT]
);
val bir_wp_simp_welltypedset_subst1_mem_thm = store_thm("bir_wp_simp_welltypedset_subst1_mem_thm", ``
  !prem v v' ve e A vs.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (
      !v. v IN vs ==> (bir_var_name v <> bir_var_name v')
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem
          (bir_exp_imp (BExp_MemEq (BExp_Den v') ve)
             (bir_exp_varsubst1 v v' e))
      )) UNION A)
    )
``,

  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vs2 = (bir_vars_of_exp
     (bir_exp_imp prem
        (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
           (bir_exp_varsubst1 v v' e))) UNION A)` >>

  Q.PAT_X_ASSUM `B = C` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC std_ss [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_vars_of_exp_def] >>

  FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS, bir_exp_varsubst1_def, bir_exp_varsubst_USED_VARS, bir_exp_varsubst_introduced_vars_REWRS, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FDOM_FEMPTY] >>

  REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  subgoal `vs2 = {v'} UNION vs` >- (
    METIS_TAC [pred_setTheory.UNION_COMM, pred_setTheory.UNION_ASSOC, pred_setTheory.UNION_IDEMPOT]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.INSERT_UNION_EQ] >>
  METIS_TAC [bir_var_set_is_well_typed_INSERT]
);


val bir_wp_simp_welltypedset_subst1_list_thm = store_thm("bir_wp_simp_welltypedset_subst1_list_thm", ``
  !prem v v' ve e A vs vsl.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (set vsl = vs)
    ==>
    (
      EVERY (\v. bir_var_name v <> bir_var_name v') vsl
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem
          (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
             (bir_exp_varsubst1 v v' e))
      )) UNION A)
    )
``,

  REPEAT STRIP_TAC >>

  subgoal `!v. v IN vs ==> (bir_var_name v <> bir_var_name v')` >- (
    Q.PAT_X_ASSUM `B = C UNION A` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `B = C` (ASSUME_TAC o GSYM) >>
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM]
  ) >>

  METIS_TAC [bir_wp_simp_welltypedset_subst1_thm]
);
val bir_wp_simp_welltypedset_subst1_mem_list_thm = store_thm("bir_wp_simp_welltypedset_subst1_mem_list_thm", ``
  !prem v v' ve e A vs vsl.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (set vsl = vs)
    ==>
    (
      EVERY (\v. bir_var_name v <> bir_var_name v') vsl
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp (
        bir_exp_imp prem
          (bir_exp_imp (BExp_MemEq (BExp_Den v') ve)
             (bir_exp_varsubst1 v v' e))
      )) UNION A)
    )
``,

  REPEAT STRIP_TAC >>

  subgoal `!v. v IN vs ==> (bir_var_name v <> bir_var_name v')` >- (
    Q.PAT_X_ASSUM `B = C UNION A` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `B = C` (ASSUME_TAC o GSYM) >>
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM]
  ) >>

  METIS_TAC [bir_wp_simp_welltypedset_subst1_mem_thm]
);

val bir_wp_simp_welltypedset_subst1_list_format_thm = store_thm("bir_wp_simp_welltypedset_subst1_list_format_thm", ``
  !prem v v' ve e A vs vsl.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (set vsl = vs)
    ==>
    (
      EVERY (\v. bir_var_name v <> bir_var_name v') vsl
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp
               (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
                            (bir_exp_varsubst1 v v' e)))
          
      UNION A)
    )
``,

  ASSUME_TAC bir_wp_simp_welltypedset_subst1_list_thm >>
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def] >>
  METIS_TAC []
);

val bir_wp_simp_welltypedset_subst1_mem_list_format_thm = store_thm("bir_wp_simp_welltypedset_subst1_mem_list_format_thm", ``
  !prem v v' ve e A vs vsl.
    (v IN bir_vars_of_exp e)
    ==>
    (vs = (bir_vars_of_exp (
        bir_exp_imp prem (bir_exp_subst1 v ve e))) UNION A)
    ==>
    (set vsl = vs)
    ==>
    (
      EVERY (\v. bir_var_name v <> bir_var_name v') vsl
    )
    ==>
    (
      bir_var_set_is_well_typed (vs)
      <=>
      bir_var_set_is_well_typed ((bir_vars_of_exp prem) UNION (bir_vars_of_exp
               (bir_exp_imp (BExp_MemEq (BExp_Den v') ve)
                            (bir_exp_varsubst1 v v' e)))
          
      UNION A)
    )
``,

  ASSUME_TAC bir_wp_simp_welltypedset_subst1_mem_list_thm >>
  FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def] >>
  METIS_TAC []
);


(* --------------------------------------------- more ------------------------------------------------ *)



val bir_exp_vartsubst1_intro_thm = store_thm("bir_exp_vartsubst1_intro_thm", ``
  !v' v ve e.
    (bir_var_type v = bir_var_type v') ==>
    (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
    (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
    ((bir_exp_subst1 v ve e) = (bir_exp_subst1 v' ve (bir_exp_varsubst1 v v' e)))
``,

  REPEAT STRIP_TAC >>
  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR, bir_exp_subst1_REWRS, bir_vars_of_exp_def, pred_setTheory.IMAGE_UNION, pred_setTheory.IN_UNION]
  ) >>

  CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_exp_subst1_REWRS]
  ) >>

  CASE_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
);


val bir_exp_is_taut_imp_subst1_varsubst1_thm = store_thm("bir_exp_is_taut_imp_subst1_varsubst1_thm",``
!v' prem v ve e.
  (bir_var_type v = bir_var_type v') ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp prem)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
  (
   (bir_exp_is_taut (bir_exp_imp prem (bir_exp_subst1 v ve e)))
   <=>
   (bir_exp_is_taut (bir_exp_imp prem (bir_exp_subst1 v' ve (bir_exp_varsubst1 v v' e))))
  )
``,

  METIS_TAC [bir_exp_vartsubst1_intro_thm]
);











val bir_env_vars_are_initialised_FUPDATE_thm = store_thm ("bir_env_vars_are_initialised_FUPDATE_thm", ``
  !sm vs vn vt vv.
(*  (bir_env_lookup vn (BEnv sm) = NONE) ==>*)
    (~(vn IN (IMAGE bir_var_name vs))) ==>
    (bir_env_vars_are_initialised (BEnv sm) vs) ==>
    (bir_env_vars_are_initialised (BEnv (FUPDATE sm (vn, vt, SOME vv))) vs)
``,

  REWRITE_TAC [bir_env_vars_are_initialised_def] >>
  REPEAT STRIP_TAC >>

  Q.PAT_X_ASSUM `!v. A ==> B` (ASSUME_TAC o (Q.SPEC `v`)) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>
(*
  Q.EXISTS_TAC `if (bir_var_name v) = vn then vv else v'` >>
  CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
  )
*)
  Q.EXISTS_TAC `v'` >>
  FULL_SIMP_TAC std_ss [bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  CASE_TAC >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
);


val bir_eval_exp_env_FUPDATE_thm = store_thm ("bir_eval_exp_env_FUPDATE_thm", ``
  !e sm vn' vu'.
    (~(vn' IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
    (
     (bir_eval_exp e (BEnv sm))
     =
     (bir_eval_exp e (BEnv (FUPDATE sm (vn', vu'))))
    )
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_vars_of_exp_def, pred_setTheory.IMAGE_UNION, pred_setTheory.IN_UNION] >>
    TRY (METIS_TAC [])
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
);






(* is related to thomas' subst intro theorem, but cannot be used *)
(* bir_exp_tautologiesTheory.bir_exp_is_taut_INTRODUCE_FRESH_VAR_AS_ABBREV *)
val bir_exp_is_taut_imp_imp_subst1_thm = store_thm("bir_exp_is_taut_imp_imp_subst1_thm",``
!v' prem vs v ve e vty.
  (bir_type_is_Imm (bir_var_type v)) ==>
  (bir_var_type v' = bir_var_type v) ==>
  (type_of_bir_exp ve = SOME (bir_var_type v)) ==>
  (v IN (bir_vars_of_exp e)) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp prem)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
  (
   (bir_exp_is_taut (bir_exp_imp prem (bir_exp_subst1 v ve e)))
   <=>
   (bir_exp_is_taut (bir_exp_imp prem
                    (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)
                                 (bir_exp_varsubst1 v v' e)
                    ))
   )
  )
``,

  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPECL [`v'`, `prem`, `v`, `ve`, `e`] bir_exp_is_taut_imp_subst1_varsubst1_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  POP_ASSUM (K ALL_TAC) >>

  EQ_TAC >- (
    FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_is_taut_def] >>
    REPEAT STRIP_TAC >|
    [
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Imm_def] >>

      FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
      subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
        FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
      ) >>
      METIS_TAC [bir_exp_subst_TYPE_EQ]
    ,

      ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

      REPEAT STRIP_TAC >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_var_set_is_well_typed_def]
      ) >>
      METIS_TAC []
    ,
      ALL_TAC
    ] >>

    ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

    Q.PAT_X_ASSUM `!env.A` (ASSUME_TAC o (Q.SPEC `env`)) >>
    REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>

    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    subgoal `bir_is_bool_exp (BExp_BinPred BIExp_Equal (BExp_Den v') ve)` >- (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Imm_def]
    ) >>

    subgoal `bir_is_bool_exp (bir_exp_subst1 v (BExp_Den v') e)` >- (
      FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
      subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
        FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
      ) >>
      METIS_TAC [bir_exp_subst_TYPE_EQ]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (BExp_BinPred BIExp_Equal (BExp_Den v') ve))` >- (
      REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v (BExp_Den v') e))` >- (
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v ve e))` >- (
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION]
    ) >>


    Cases_on `bir_eval_exp prem env = bir_val_true` >> Cases_on `bir_eval_exp (BExp_BinPred BIExp_Equal (BExp_Den v') ve) env = bir_val_true` >> Cases_on `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) env = bir_val_false` >- (

      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      blastLib.BBLAST_TAC >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

      Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env = bir_val_false` >- (
        FULL_SIMP_TAC std_ss [bir_val_false_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>

        ASSUME_TAC (computeLib.EVAL_CONV ``(word_or (~(1w:word1)) 0w)``) >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
      ) >>
      REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm] >>

(*
      FULL_SIMP_TAC std_ss [bir_eval_bin_pred_def, bir_env_read_def, bir_env_lookup_def] >>
      Cases_on `bir_env_lookup (bir_var_name v') env` >- (
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_REWRS]
      ) >>

      Cases_on `x` >>
      Cases_on `r` >- (
        FULL_SIMP_TAC (srw_ss()) [bir_eval_bin_pred_REWRS]
      ) >>

      FULL_SIMP_TAC (srw_ss()) [bir_eval_bin_pred_REWRS] >>
      FULL_SIMP_TAC std_ss [bir_eval_bin_pred_def, bir_env_read_def, bir_env_lookup_def, bir_env_vars_are_initialised_def] >>
*)
      subgoal `bir_env_var_is_initialised env v'` >- (
        FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_def, pred_setTheory.IN_SING]
      ) >>
      FULL_SIMP_TAC std_ss [bir_env_var_is_initialised_def] >>

      FULL_SIMP_TAC std_ss [bir_eval_bin_pred_def, bir_env_read_def] >>
      FULL_SIMP_TAC (srw_ss()) [bir_eval_bin_pred_REWRS] >>

      REV_FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >>
      REV_FULL_SIMP_TAC std_ss [] >>

      FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [] >>

      subgoal `(type_of_bir_val (bir_eval_exp ve env)) = SOME (bir_var_type v)` >- (
        FULL_SIMP_TAC std_ss [bir_is_bool_exp_def, type_of_bir_exp_THM_with_init_vars]
      ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>

      subgoal `bir_eval_exp (BExp_Den v') env = BVal_Imm i` >- (
        FULL_SIMP_TAC std_ss [bir_eval_exp_def, bir_env_read_def] >>
        FULL_SIMP_TAC (srw_ss()) []
      ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>

      subgoal `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) env = bir_eval_exp (bir_exp_subst1 v ve e) env` >- (
        FULL_SIMP_TAC (std_ss) [bir_val_true_def, GSYM bir_exp_subst1_EVAL_EQ_GEN]
      ) >>
      REV_FULL_SIMP_TAC std_ss [bir_val_true_def] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      POP_ASSUM (ASSUME_TAC o blastLib.BBLAST_RULE) >>
      FULL_SIMP_TAC std_ss []

    ) >> (
      REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm] >>

      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
      blastLib.BBLAST_TAC >>
      EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      blastLib.BBLAST_TAC
    )
  ) >>

  (* the other implication direction *)
  FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >|
  [
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Imm_def] >>

    FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
    subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
      FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
    ) >>
    METIS_TAC [bir_exp_subst_TYPE_EQ]
  ,

    ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_var_set_is_well_typed_def]
    ) >>
    METIS_TAC []
  ,
    ALL_TAC
  ] >>


  ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>
  POP_ASSUM (K ALL_TAC) >>

  subgoal `(bir_is_bool_exp (bir_exp_subst1 v ve e)) /\
           (bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v ve e)))` >- (
    REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>
    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS, bir_is_bool_exp_def] >>
    METIS_TAC [bir_exp_subst1_TYPE_EQ_GEN]
  ) >>

  Cases_on `bir_eval_exp prem env = bir_val_true` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env = bir_val_false` >- (
    subgoal `bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem)
                          (bir_exp_subst1 v ve e)) env = bir_val_false` >- (
      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      blastLib.BBLAST_TAC >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      EVAL_TAC
    ) >>
    ASM_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_val_true_def, bir_val_false_def] >>
    EVAL_TAC >>

    Cases_on `env` >>
    Q.RENAME1_TAC `BEnv sm` >>

    ASSUME_TAC (Q.SPECL [`v`, `ve`, `bir_var_name v'`, `bir_var_type v'`, `SOME (bir_eval_exp ve (BEnv sm))`, `e`, `sm`] bir_wp_simp_eval_subst1_lemma) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    Q.ABBREV_TAC `sm' = (FUPDATE sm (bir_var_name v',bir_var_type v,SOME (bir_eval_exp ve (BEnv sm))))` >>
    Q.PAT_X_ASSUM `!env. A ==> B` (ASSUME_TAC o (Q.SPEC `BEnv sm'`)) >>

    subgoal `(bir_eval_bin_exp BIExp_Or
          (bir_eval_unary_exp BIExp_Not (bir_eval_exp prem (BEnv sm')))
          (bir_eval_bin_exp BIExp_Or
             (bir_eval_unary_exp BIExp_Not
                (bir_eval_bin_pred BIExp_Equal
                   (bir_env_read v' (BEnv sm'))
                   (bir_eval_exp ve (BEnv sm'))))
             (bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e)
                (BEnv sm'))) =
        BVal_Imm (Imm1 1w))` >- (
(*
bir_env_vars_are_initialised_FUPDATE_thm
*)
      subgoal `(bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp prem) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp prem)) /\
               (bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp ve) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp ve)) /\
               (bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp e DIFF {v}) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp e DIFF {v}))` >- (
        subgoal `~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e DIFF {v})))` >- (
          FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >> METIS_TAC []
        ) >>
        FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_FUPDATE_thm, Abbr `sm'`, pred_setTheory.DIFF_SUBSET, pred_setTheory.IMAGE_SUBSET]
      ) >>

      

      REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
      FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>
      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_FUPDATE_thm, Abbr `sm'`] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def, bir_env_var_is_initialised_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE, type_of_bir_exp_THM_with_init_vars]
    ) >>
    Q.PAT_X_ASSUM `A ==> B` (K ALL_TAC) >>

    subgoal `bir_eval_exp prem (BEnv sm') = bir_eval_exp prem (BEnv sm)` >- (
      FULL_SIMP_TAC std_ss [bir_eval_exp_env_FUPDATE_thm, Abbr `sm'`]
    ) >>
    subgoal `(bir_eval_exp ve (BEnv sm')) = (bir_eval_exp ve (BEnv sm))` >- (
      FULL_SIMP_TAC std_ss [bir_eval_exp_env_FUPDATE_thm, Abbr `sm'`]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>
    FULL_SIMP_TAC (std_ss) [] >>

(*
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [Abbr `sm'`] >>
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    REV_FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>


    subgoal `(type_of_bir_val (bir_eval_exp ve (BEnv sm))) = SOME (bir_var_type v)` >- (
      FULL_SIMP_TAC std_ss [bir_is_bool_exp_def, type_of_bir_exp_THM_with_init_vars]
    ) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>

    Q.PAT_X_ASSUM `BType_Imm it = bir_var_type v` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>
*)

    subgoal `(bir_env_read v' (BEnv sm')) = (bir_eval_exp ve (BEnv sm))` >- (
(*
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      ASM_REWRITE_TAC [] >>
*)
      ASM_SIMP_TAC (srw_ss()) [bir_env_read_def, Abbr `sm'`, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
    ) >>
    subgoal `(bir_eval_bin_pred BIExp_Equal (bir_eval_exp ve (BEnv sm)) (bir_eval_exp ve (BEnv sm))) = bir_val_true` >- (
      subgoal `bir_val_is_Imm (bir_eval_exp ve (BEnv sm))` >- (
        FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_exp_subst1_USED_VARS] >>
        REV_FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION, bir_val_checker_TO_type_of] >>
        FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars]
      ) >>
      FULL_SIMP_TAC std_ss [bir_val_is_Imm_def, bir_eval_bin_pred_def, bir_val_true_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR, bool2b_def, bool2w_def]
    ) >>

    Q.PAT_X_ASSUM `bir_val_false = A` (ASSUME_TAC o GSYM) >>

    subgoal `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) (BEnv sm') = bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm')` >- (
      FULL_SIMP_TAC (std_ss) [bir_val_true_def, bir_exp_subst1_EVAL_EQ_GEN, GSYM bir_eval_exp_def]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>
    FULL_SIMP_TAC (std_ss) [] >>


    REV_FULL_SIMP_TAC std_ss [bir_val_true_def, bir_val_false_def] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    Q.PAT_X_ASSUM `A = (1w:word1)` (ASSUME_TAC o blastLib.BBLAST_RULE) >>
    FULL_SIMP_TAC std_ss []

(*
    Cases_on `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) (BEnv (FUPDATE sm (bir_var_name v',BType_Imm it, SOME (BVal_Imm i))) ) = bir_val_false` >- (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_val_false_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bool2b_def, bool2w_def] >>

      EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    ) >>
    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm] >>





    subgoal `bir_env_vars_are_initialised (BEnv (FUPDATE sm (bir_var_name v',bir_var_type v,SOME (bir_eval_exp ve env)))) (bir_vars_of_exp prem)` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_FUPDATE_thm]
(*
      METIS_TAC [bir_env_vars_are_initialised_FUPDATE_thm]
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def, bir_env_var_is_initialised_def] >>
*)
    ) >>

    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def, ] >>
*)






  ) >> (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm, bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

    FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
    blastLib.BBLAST_TAC >>
    EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    blastLib.BBLAST_TAC
  )
);






(*
======================================================================
now substitution for memories
======================================================================
*)

(*
(* bir_exp_substitutionsTheory.bir_exp_subst1_EVAL_EQ_GEN *)
val bir_exp_subst1_TYPE_OF_EVAL_EQ_GEN = store_thm("bir_exp_subst1_TYPE_OF_EVAL_EQ_GEN", ``
  !env v ve ve' ty e ty'.
     (bir_var_type v = ty) ==>
     (type_of_bir_val (bir_eval_exp ve env) = SOME ty) ==>
     (type_of_bir_val (bir_eval_exp ve' env) = SOME ty) ==>
     (type_of_bir_exp e = SOME ty') ==>
     (
      (type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
       type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env))
      /\
      (type_of_bir_exp (bir_exp_subst1 v ve e) = SOME ty')
     )
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS]
  ) >- (
    Cases_on `v = b` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS]
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e') env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e') env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e') env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    ) >>

    Cases_on `type_of_bir_imm b' = type_of_bir_imm b'''` >> (
      ASM_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e') env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e') env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e') env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    ) >>

    Cases_on `type_of_bir_imm b' = type_of_bir_imm b'''` >> (
      ASM_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e') env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e') env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e') env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    ) >> (
      REWRITE_TAC [bir_eval_memeq_REWRS]
    ) >>

    Cases_on `b' <> b''' \/ b0' <> b0'''` >> (
      ASM_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    )
  ) >- (
    Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e) env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e'') env` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve' e'') env` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst1_REWRS, bir_eval_exp_def, bir_eval_cast_REWRS]
    ) >> (
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e) env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e) env)` >- (
        METIS_TAC []
      ) >>
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e') env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e') env)` >- (
        METIS_TAC []
      ) >>
      subgoal `type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve e'') env) =
               type_of_bir_val (bir_eval_exp (bir_exp_subst1 v ve' e'') env)` >- (
        METIS_TAC []
      ) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!x. P` (K ALL_TAC) >>
      REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_def]
    ) >> (
      Cases_on `type_of_bir_imm b' = Bit1` >> (
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
      )
    )
(*
    type_of_bir_exp_def
    bir_eval_exp_def
bir_eval_ifthenelse_def
*)

(* , type_of_bir_val_def *)

  )
);
*)

val bir_memeq_REFL = store_thm("bir_memeq_REFL", ``
  !at vt mmap.
     (bir_memeq at vt mmap mmap)
``,

  REWRITE_TAC [bir_exp_memTheory.bir_memeq_def]
);

val bir_memeq_SYMM = store_thm("bir_memeq_SYMM", ``
  !at vt mmap1 mmap2.
     (bir_memeq at vt mmap1 mmap2 = bir_memeq at vt mmap2 mmap1)
``,

  METIS_TAC [bir_exp_memTheory.bir_memeq_def]
);

val bir_memeq_TRANS = store_thm("bir_memeq_TRANS", ``
  !at vt mmap1 mmap2 mmap3.
     (bir_memeq at vt mmap1 mmap2) ==>
     (bir_memeq at vt mmap2 mmap3) ==>
     (bir_memeq at vt mmap1 mmap3)
``,

  METIS_TAC [bir_exp_memTheory.bir_memeq_def]
);

val bir_memeq_EQ_REPL = store_thm("bir_memeq_EQ_REPL", ``
  !at vt mmap1 mmap2 mmap3.
     (bir_memeq at vt mmap1 mmap2) ==>
     (bir_memeq at vt mmap1 mmap3 = bir_memeq at vt mmap2 mmap3)
``,

  METIS_TAC [bir_exp_memTheory.bir_memeq_def]
);

(*
val bir_eval_memeq_REFL = store_thm("bir_eval_memeq_REFL", ``
  !m.
     (bir_eval_memeq m m = bir_val_true)
``,

  cheat
);

val bir_eval_memeq_SYMM = store_thm("bir_eval_memeq_SYMM", ``
  !m1 m2.
     (bir_eval_memeq m1 m2) = (bir_eval_memeq m2 m1)
``,

  cheat
);

val bir_eval_memeq_TRANS = store_thm("bir_eval_memeq_TRANS", ``
  !m1 m2 m3.
     (bir_eval_memeq m1 m2 = bir_val_true) ==>
     (bir_eval_memeq m2 m3 = bir_val_true) ==>
     (bir_eval_memeq m1 m3 = bir_val_true)
``,

  cheat
);

val bir_eval_memeq_trans = store_thm("bir_eval_memeq_trans", ``
  !m1 m2 m3.
     (bir_eval_memeq m1 m2) ==>
     (bir_eval_memeq m1 m3 = bir_eval_memeq m2 m3)
``,

  cheat
);
*)


val bir_eval_exp_eq_def = Define `
  bir_eval_exp_eq e1 e2 env =
    ?ty. (type_of_bir_exp e1 = SOME ty) /\
         (type_of_bir_exp e2 = SOME ty) /\
         (bir_env_vars_are_initialised env (bir_vars_of_exp e1)) /\
         (bir_env_vars_are_initialised env (bir_vars_of_exp e2)) /\
         (
          (bir_type_is_Imm ty) ==>
          (bir_eval_exp e1 env = bir_eval_exp e2 env)
         )
         /\
         (
          (bir_type_is_Mem ty) ==>
          (?aty vty mmap1 mmap2.
             (bir_eval_exp e1 env = BVal_Mem aty vty mmap1) /\
             (bir_eval_exp e2 env = BVal_Mem aty vty mmap2) /\
             (bir_memeq aty vty mmap1 mmap2))
         )
`;



val n2bs_eq_bitstrings_thm = prove(``
  !vt x1 x2.
    (n2bs x1 vt = n2bs x2 vt) ==>
    (fixwidth (size_of_bir_immtype vt) (n2v x1) = fixwidth (size_of_bir_immtype vt) (n2v x2))
``,

  let
    val alpha = ``:'a``;
    val instance_thms = [
                          GSYM (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:1``] bitstringTheory.w2v_v2w)),
                          GSYM (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:8``] bitstringTheory.w2v_v2w)),
                          GSYM (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:16``] bitstringTheory.w2v_v2w)),
                          GSYM (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:32``] bitstringTheory.w2v_v2w)),
                          GSYM (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:64``] bitstringTheory.w2v_v2w))
                        ];
  in
    Cases_on `vt` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [n2bs_def] >>
      METIS_TAC (instance_thms@[GSYM bitstringTheory.v2w_n2v])
    )
  end
);



(*
(*

type_of_bir_imm i = rty

n2bs
  (bir_update_mmap at f' (b2n i')
     (bitstring_split (size_of_bir_immtype rty) (b2v i))
     (bir_mem_addr at a)) rty =
n2bs
  (bir_update_mmap at f (b2n i')
     (bitstring_split (size_of_bir_immtype rty) (b2v i))
     (bir_mem_addr at a)) rty
*)
val n2bs_bir_update_mmap_thm = prove(``
  !mmap1 mmap2 ra vt at av i rty x.
    (type_of_bir_imm i = rty) ==>
    (bir_number_of_mem_splits vt rty at = SOME x) ==>
    (n2bs (mmap1 ra) vt = n2bs (mmap2 ra) vt) ==>
    (n2bs (
        (bir_update_mmap at mmap1 av (bitstring_split (size_of_bir_immtype vt) (b2v i)))
        ra) vt =
     n2bs (
        (bir_update_mmap at mmap2 av (bitstring_split (size_of_bir_immtype vt) (b2v i)))
        ra) vt)
``,

  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vecval = b2v i` >>
  Q.ABBREV_TAC `updates = bitstring_split (size_of_bir_immtype vt) vecval` >>

  subgoal `LENGTH updates = (LENGTH vecval) DIV (size_of_bir_immtype vt)` >- (
    Cases_on `vt` >> Cases_on `rty` >> (
      Cases_on `i` >> FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [n2bs_def, Abbr `updates`, Abbr `vecval`, bir_exp_memTheory.bitstring_split_REWRS_LENGTH] >>

      EVAL_TAC >>

      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_memTheory.bitstring_split_def] >>
      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bitstring_split_REWRS_LENGTH]
    )
  ) >>

  Cases_on `vt` >> (
(*
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [n2bs_def] >>

    FULL_SIMP_TAC std_ss [Abbr `vecval`] >>
    Cases_on `i` >> FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    FULL_SIMP_TAC std_ss [bitstringTheory.length_w2v] >>
    POP_ASSUM MP_TAC >>
    EVAL_TAC >>
    STRIP_TAC >>
*)

(*
    Cases_on `updates` >- (
      FULL_SIMP_TAC list_ss []
    ) >>

    REPEAT (
      Cases_on `t` >> (
        FULL_SIMP_TAC list_ss []
      ) >>
      Cases_on `t'` >> (
        FULL_SIMP_TAC list_ss []
      )
    ) >>

    FULL_SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def] >>

    let
      fun case_fun AV_var goalandthm =
            (Cases_on `bir_mem_addr at ^AV_var = ra` >> (
               FULL_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
            ) >> 
            case_fun ``SUC (^AV_var)``
            ) goalandthm;
    in
      case_fun ``av:num``
    end
*)
    Q.RENAME1_TAC `LENGTH t` >>
    Q.ABBREV_TAC `av' = av` >>
    REPEAT (
      Cases_on `t` >> (
        FULL_SIMP_TAC list_ss []
      ) >>
      Cases_on `t'` >> (
        FULL_SIMP_TAC list_ss []
      ) >>

      FULL_SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def] >>

      Cases_on `ra = bir_mem_addr at av'` >> Cases_on `ra = bir_mem_addr at (SUC av')` >> (
        FULL_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
      ) >> 
    )
    end
  )
(*
open bir_exp_memTheory;
bir_exp_memTheory.bir_update_mmap_def
*)
(*    REPEAT STRIP_TAC >>*)

(*
    FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def] >>
*)
(*
    POP_ASSUM MP_TAC >>
    Q.ID_SPEC_TAC `mmap1` >>
    Q.ID_SPEC_TAC `mmap2` >>
    Q.ID_SPEC_TAC `ra` >>
    Q.ID_SPEC_TAC `av` >>
*)
(*
bir_exp_memTheory.bir_mem_addr_def
bir_exp_memTheory.bir_mem_addr_w2n_SIZES
bir_exp_liftingTheory.bir_update_mmap_words_INTRO
bir_exp_liftingTheory.bir_update_mmap_words_INTRO_w2n
bir_exp_liftingTheory.bir_update_mmap_words_def
*)
);

val n2bs_bir_update_mmap_REVERSE_thm = prove(``
  !mmap1 mmap2 ra vt at av i.
    (type_of_bir_imm i = vt) ==>
    (n2bs (mmap1 ra) vt = n2bs (mmap2 ra) vt) ==>
    (n2bs (
        (bir_update_mmap at mmap1 av (REVERSE (bitstring_split (size_of_bir_immtype vt) (b2v i))))
        ra) vt =
     n2bs (
        (bir_update_mmap at mmap2 av (REVERSE (bitstring_split (size_of_bir_immtype vt) (b2v i))))
        ra) vt)
``,

  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `vecval = b2v i` >>
  Q.ABBREV_TAC `updates = bitstring_split (size_of_bir_immtype vt) vecval` >>

  subgoal `LENGTH updates = (LENGTH vecval) DIV (size_of_bir_immtype vt)` >- (
    Cases_on `vt` >> (
      Cases_on `i` >> FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [n2bs_def, Abbr `updates`, Abbr `vecval`, bir_exp_memTheory.bitstring_split_REWRS_LENGTH] >>

      EVAL_TAC >>

      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_memTheory.bitstring_split_def] >>
      FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bitstring_split_REWRS_LENGTH]
    )
  ) >>

  Cases_on `vt` >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [n2bs_def] >>

    FULL_SIMP_TAC std_ss [Abbr `vecval`] >>
    Cases_on `i` >> FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    FULL_SIMP_TAC std_ss [bitstringTheory.length_w2v] >>
    POP_ASSUM MP_TAC >>
    EVAL_TAC >>
    STRIP_TAC >>

    Cases_on `updates` >- (
      FULL_SIMP_TAC list_ss []
    ) >>
    Cases_on `t` >> (
      FULL_SIMP_TAC list_ss [listTheory.REV_DEF]
    ) >>

    FULL_SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def] >>

    Cases_on `bir_mem_addr at av = ra` >> (
      FULL_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
    )    
  )
);
*)



(*
val bir_update_mmap_NO_ADDRESS_TWICE = store_thm ("bir_update_mmap_NO_ADDRESS_TWICE",
  ``!.
      () ==>
      () ==>
      (bir_update_mmap aty mmap a vs)
``,

cheat
);
*)


(*
bir_exp_memTheory.bir_update_mmap_UNCHANGED
*)
val bir_update_mmap_CHANGED = store_thm ("bir_update_mmap_CHANGED",
  ``!aty mmap a vs a' n.
      (LENGTH vs <= 2 ** (size_of_bir_immtype aty)) ==>
      (n < LENGTH vs) ==>
      (a' = bir_mem_addr aty (a+n)) ==>
      ((bir_update_mmap aty mmap a vs) a' = v2n (EL n vs) )``,

GEN_TAC >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def]
) >>
REPEAT STRIP_TAC >>

Cases_on `n` >- (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def] >>
  ASSUME_TAC (Q.SPECL [`aty`, `((bir_mem_addr aty a =+ v2n h) mmap)`, `(SUC a)`, `vs`, `(bir_mem_addr aty a)`] bir_exp_memTheory.bir_update_mmap_UNCHANGED) >>

  subgoal `(!n. n < LENGTH (vs:bitstring list) ==>
                bir_mem_addr aty a <> bir_mem_addr aty (SUC a + n))` >- (
    REPEAT STRIP_TAC >>
    REPEAT (Q.PAT_X_ASSUM `!n. A` (K ALL_TAC)) >>
    REPEAT (Q.PAT_X_ASSUM `A ==> B` (K ALL_TAC)) >>

    subgoal `SUC (n) < (2 ** size_of_bir_immtype aty)` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>

    FULL_SIMP_TAC arith_ss [bir_exp_memTheory.bir_mem_addr_def, bitTheory.MOD_2EXP_def] >>
    Q.ABBREV_TAC `sz = (size_of_bir_immtype aty)` >>

    subgoal `n + SUC a = SUC n + a` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>

    subgoal `0 + a = a` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>

    subgoal `0 < (2 ** sz)` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>

    subgoal `0 MOD (2 ** sz) <> (SUC n) MOD (2 ** sz)` >- (
      FULL_SIMP_TAC arith_ss []
    ) >>

    METIS_TAC [arithmeticTheory.ADD_MOD]
  ) >>

  FULL_SIMP_TAC list_ss [combinTheory.UPDATE_APPLY]
) >>

FULL_SIMP_TAC arith_ss [] >>
FULL_SIMP_TAC list_ss [] >>

subgoal `a + SUC n' = (SUC a) + n'` >- (
  METIS_TAC [arithmeticTheory.ADD_SUC, arithmeticTheory.ADD_COMM]
) >>
FULL_SIMP_TAC std_ss []
);



val bir_number_of_mem_splits_IMPL_size_thm = prove(
``
!vty rty aty x.
(bir_number_of_mem_splits vty rty aty = SOME x) ==>
(x <= 2 ** size_of_bir_immtype aty)
``,

REPEAT STRIP_TAC >>

Cases_on `vty` >> Cases_on `rty` >> Cases_on `aty` >> (
FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_REWRS] >>
POP_ASSUM (ASSUME_TAC o GSYM) >>
FULL_SIMP_TAC std_ss [] >>
EVAL_TAC
)
);






val bir_update_mmap_STAY_EQ = store_thm ("bir_update_mmap_STAY_EQ",
  ``!aty mmap1 mmap2 a vs addr.
      (mmap1 addr = mmap2 addr) ==>
      ((bir_update_mmap aty mmap1 a vs) addr = (bir_update_mmap aty mmap2 a vs) addr)``,

GEN_TAC >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def]
) >>

REPEAT STRIP_TAC >>

Q.ABBREV_TAC `mmap1' = ((bir_mem_addr aty a =+ v2n h) mmap1)` >>
Q.ABBREV_TAC `mmap2' = ((bir_mem_addr aty a =+ v2n h) mmap2)` >>

subgoal `mmap1' addr = mmap2' addr` >- (
  Cases_on `addr = bir_mem_addr aty a` >> (
    METIS_TAC [combinTheory.UPDATE_APPLY]
  )
) >>

METIS_TAC []
);




val bir_update_mmap_EQUAL_FOR = store_thm ("bir_update_mmap_EQUAL_FOR",
  ``!aty mmap1 mmap2 a vs a' n.
      (n < LENGTH vs) ==>
      (a' = bir_mem_addr aty (a+n)) ==>
      ((bir_update_mmap aty mmap1 a vs) a' = (bir_update_mmap aty mmap2 a vs) a')``,

GEN_TAC >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def]
) >>
REPEAT STRIP_TAC >>

Q.ABBREV_TAC `mmap1' = ((bir_mem_addr aty a =+ v2n h) mmap1)` >>
Q.ABBREV_TAC `mmap2' = ((bir_mem_addr aty a =+ v2n h) mmap2)` >>

Cases_on `n` >- (
  Q.ABBREV_TAC `addr = bir_mem_addr aty a` >>
  subgoal `mmap1' addr = mmap2' addr` >- (
    Cases_on `addr = bir_mem_addr aty a` >> (
      METIS_TAC [combinTheory.UPDATE_APPLY]
    )
  ) >>
  FULL_SIMP_TAC arith_ss [] >>
  METIS_TAC [bir_update_mmap_STAY_EQ]
) >>

subgoal `n' < LENGTH vs` >- (
  FULL_SIMP_TAC arith_ss []
) >>

subgoal `bir_update_mmap aty mmap1' (SUC a) vs (bir_mem_addr aty ((SUC a) + n')) = bir_update_mmap aty mmap2' (SUC a) vs (bir_mem_addr aty ((SUC a) + n'))` >- (
  METIS_TAC []
) >>

subgoal `a + SUC n' = (SUC a) + n'` >- (
  FULL_SIMP_TAC arith_ss []
) >>

METIS_TAC []
);



(*
(*
``
(addr IN (bir_store_in_mem_used_addrs vty i aty b2 a)) ==>
(addr = bir_mem_addr aty (a+n))
``
*)

(*bir_exp_memTheory.bir_mem_addr_def*)
val bir_update_mmap_update_index_def = Define `
  bir_update_mmap_update_index at vs n = (((LENGTH vs) DIV (2 ** (size_of_bir_immtype at)) - 1) * (2 ** (size_of_bir_immtype at))) + (bir_mem_addr at (LENGTH vs)) + (bir_mem_addr at (n + ((2 ** (size_of_bir_immtype at)) - (bir_mem_addr at (LENGTH vs)))))
`;
(*
(((LENGTH vs) DIV (size_of_bir_immtype aty) - 1) * (size_of_bir_immtype aty)) + (bir_mem_addr at (LENGTH vs)) + (bir_mem_addr at n)
((LENGTH vs) - (2 ** (size_of_bir_immtype aty)))

``(((LENGTH vs) DIV (2 ** (size_of_bir_immtype at)) - 1) * (2 ** (size_of_bir_immtype at))) + (bir_mem_addr at (LENGTH vs)) + (bir_mem_addr at (n + ((2 ** (size_of_bir_immtype at)) - (bir_mem_addr at (LENGTH vs)))))``

 (LENGTH vs) - (((LENGTH vs) DIV (size_of_bir_immtype aty)) * (size_of_bir_immtype aty)) n
*)

val bir_update_mmap_CHANGED_ALT = prove(
``
  !at mm a vs addr n.
    ((n < LENGTH vs) ==> (addr = bir_mem_addr at (a + n)) ==> (bir_update_mmap at mm a vs addr = v2n (EL (bir_update_mmap_update_index at vs n) vs)))
``,

GEN_TAC >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def]
) >>
REPEAT STRIP_TAC >>

Cases_on `n` >- (
  SIMP_TAC list_ss [bir_exp_memTheory.bir_update_mmap_def] >>
(*
  ASSUME_TAC (Q.SPECL [`aty`, `((bir_mem_addr aty a =+ v2n h) mmap)`, `(SUC a)`, `vs`, `(bir_mem_addr aty a)`] bir_exp_memTheory.bir_update_mmap_UNCHANGED) >>
*)
(*
  ASSUME_TAC (prove(``(!n.
          n < LENGTH (vs:bitstring list) ==>
          bir_mem_addr aty a <> bir_mem_addr aty (SUC a + n))``, 
cheat)) >>

  FULL_SIMP_TAC list_ss [combinTheory.UPDATE_APPLY]
*)

  FULL_SIMP_TAC arith_ss [bir_exp_memTheory.bir_mem_addr_def, bitTheory.MOD_2EXP_def] >>
  FULL_SIMP_TAC list_ss [] >>
  Q.ABBREV_TAC `addr = (a MOD 2 ** size_of_bir_immtype at)` >>
) >>

FULL_SIMP_TAC arith_ss [] >>
FULL_SIMP_TAC list_ss [bir_exp_memTheory.bir_mem_addr_def, bitTheory.MOD_2EXP_def] >>

subgoal `a + SUC n' = (SUC a) + n'` >- (
  METIS_TAC [arithmeticTheory.ADD_SUC, arithmeticTheory.ADD_COMM]
) >>
FULL_SIMP_TAC std_ss []
);

val bir_update_mmap_eq_MMAP_EQ = prove(
``
  !at mm1 mm2 mm3 mm4 a vs1 vs2 addr.
    (!addr. mm1 addr = mm2 addr) ==>
    (!addr. mm3 addr = mm4 addr) ==>
    (bir_update_mmap at mm1 a vs1 addr = bir_update_mmap at mm2 a vs1 addr) <=>
    (bir_update_mmap at mm3 a vs2 addr = bir_update_mmap at mm4 a vs2 addr)
``,

);

set (MAP (λn. bir_mem_addr ta (a + n)) (COUNT_LIST n)):


val bir_update_mmap_eq_LENGTH = prove(
``
  !at mm1 mm2 a vs1 vs2 addr.
    (LENGTH vs1 = LENGTH vs2) ==>
    (bir_update_mmap at mm1 a vs1 addr = bir_update_mmap at mm2 a vs1 addr) ==>
    (bir_update_mmap at mm1 a vs2 addr = bir_update_mmap at mm2 a vs2 addr)
``,

  Induct_on `vs2` >- (
    FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def]
  ) >>

  REPEAT STRIP_TAC >>

  Cases_on `vs1` >- (
    FULL_SIMP_TAC list_ss []
  ) >>

  Q.RENAME1_TAC `LENGTH (h1::vs1) = LENGTH (h2::vs2)` >>

  FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def] >>

(*
  subgoal `bir_update_mmap at ((bir_mem_addr at a =+ v2n h1) mm1) (SUC a) vs2 addr =
           bir_update_mmap at ((bir_mem_addr at a =+ v2n h1) mm2) (SUC a) vs2 addr` >- (
    METIS_TAC []
  ) >>
*)

  POP_ASSUM (fn thm1 => POP_ASSUM (fn thm2 => REPEAT (POP_ASSUM (K ALL_TAC)) >> ASSUME_TAC thm2 >> ASSUME_TAC thm1)) >>

  Cases_on `addr = bir_mem_addr at ((SUC a) + n)` >- (
    Cases_on `n < LENGTH vs1` >- (
      METIS_TAC [bir_update_mmap_EQUAL_FOR]
    ) >>

    subgoal `bir_update_mmap at ((bir_mem_addr at a =+ v2n h2) mm1) (SUC a) vs2 addr = ((bir_mem_addr at a =+ v2n h2) mm1) addr` >- (
      subgoal `!n. n < LENGTH vs1 ==> addr <> bir_mem_addr at ((SUC a) + n)` >- (
        REPEAT STRIP_TAC >>
        FULL_SIMP_TAC (list_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def] >>
      ) >>
      METIS_TAC [bir_exp_memTheory.bir_update_mmap_UNCHANGED]
    )

    Cases_on `addr = bir_mem_addr at a` >>
    METIS_TAC [bir_exp_memTheory.bir_update_mmap_UNCHANGED, combinTheory.UPDATE_APPLY]
  )

bir_exp_memTheory.bir_update_mmap_UNCHANGED
bir_update_mmap_EQUAL_FOR
  cheat
);
*)

(*
bir_update_mmap_EQUAL_FOR
bir_exp_memTheory.bir_update_mmap_UNCHANGED
val bir_update_mmap_eq_CONS = prove(
``
  !at mm1 mm2 a h vs addr.
    (bir_update_mmap at mm1 a vs addr = bir_update_mmap at mm2 a vs addr) ==>
    (bir_update_mmap at mm1 a (h::vs) addr = bir_update_mmap at mm2 a (h::vs) addr)
``,

bir_update_mmap_EQUAL_FOR

  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def] >>

  Cases_on `addr = bir_mem_addr at a` >- (
  ) >>

  REPEAT (POP_ASSUM MP_TAC) >>

  Q.ID_SPEC_TAC `mm1` >>
  Q.ID_SPEC_TAC `mm2` >>

  Induct_on `vs` >- (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_update_mmap_def] >>
    Cases_on `addr = bir_mem_addr at a` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [combinTheory.UPDATE_APPLY]
    )
  ) >>

  REPEAT STRIP_TAC >>
);
*)


(*
bir_exp_memTheory.bir_load_from_mem_used_addrs_def
bir_exp_memTheory.bir_store_in_mem_used_addrs_def
*)
val bir_update_mmap_eq_thm = prove (``
!addr at a n x vs mm1 mm2.
(MEM addr (MAP (λn. bir_mem_addr at (a + n)) (COUNT_LIST x))) ==>
(x ≤ 2 ** size_of_bir_immtype at) ==>
(LENGTH vs = x) ==>
(bir_update_mmap at mm1 a vs addr = bir_update_mmap at mm2 a vs addr)
``,

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [listTheory.MEM_MAP] >>

  METIS_TAC [rich_listTheory.MEM_COUNT_LIST, bir_update_mmap_EQUAL_FOR]
);


(*
  36.  bir_store_in_mem vt at i f b2 (b2n i') = SOME x
  37.  bir_store_in_mem vt at i f' b2 (b2n i') = SOME x'
  38.  bir_mem_addr at a IN 
       bir_store_in_mem_used_addrs vt i at b2 (b2n i')

n2bs (x' (bir_mem_addr at a)) vt = n2bs (x (bir_mem_addr at a)) vt
*)

val bir_store_in_mem_TO_used_addrs_thm = prove(``
  !vt at i mm1 mm2 b2 i' mm1' mm2' addr.
    (bir_store_in_mem vt at i mm1 b2 (b2n i') = SOME mm1') ==>
    (bir_store_in_mem vt at i mm2 b2 (b2n i') = SOME mm2') ==>
    (addr IN (bir_store_in_mem_used_addrs vt i at b2 (b2n i'))) ==>
    (mm1' addr = mm2' addr)
``,

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_store_in_mem_used_addrs_def, bir_exp_memTheory.bir_load_from_mem_used_addrs_def] >>

  Cases_on `bir_number_of_mem_splits vt (type_of_bir_imm i) at` >> (
    FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
  ) >>

  Cases_on `(~(x = 1)) /\ (b2 = BEnd_NoEndian)` >> (
    FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY] >>
    FULL_SIMP_TAC std_ss []
  ) >- (

    IMP_RES_TAC bir_number_of_mem_splits_IMPL_size_thm >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_store_in_mem_EQ_SOME] >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    ) >> (
      Q.PAT_X_ASSUM `T` (K ALL_TAC) >>

      LAST_ASSUM (fn thm => Q.ABBREV_TAC `vs = ^((snd o dest_eq o concl) thm)`) >>

      subgoal `LENGTH vs = x` >- (
        METIS_TAC [listTheory.LENGTH_REVERSE, bir_exp_memTheory.bitstring_split_LENGTHS_b2v, GSYM bir_exp_memTheory.bir_number_of_mem_splits_EQ_SOME1]
      )
    ) >> (
      METIS_TAC [bir_update_mmap_eq_thm]
    )

  ) >>

  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_store_in_mem_EQ_SOME] >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
  ) >> (
    POP_ASSUM (K ALL_TAC) >>
    Q.PAT_X_ASSUM `T` (K ALL_TAC) >>
    IMP_RES_TAC bir_number_of_mem_splits_IMPL_size_thm >>

    LAST_ASSUM (fn thm => Q.ABBREV_TAC `vs = ^((snd o dest_eq o concl) thm)`) >>

    subgoal `LENGTH vs = x` >- (
(*    REV_FULL_SIMP_TAC std_ss []*)
      METIS_TAC [listTheory.LENGTH_REVERSE, bir_exp_memTheory.bitstring_split_LENGTHS_b2v]
    ) >>

    POP_ASSUM (fn thm =>
      POP_ASSUM (K ALL_TAC) >>
      REPEAT (Q.PAT_X_ASSUM `A = B` (K ALL_TAC)) >>
      ASSUME_TAC thm
    )
  ) >> (
    METIS_TAC [bir_update_mmap_eq_thm]
  )
);


(*
  FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_store_in_mem_def, LET_DEF] >>
  Cases_on `b2` >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    POP_ASSUM (K ALL_TAC) >>
    IMP_RES_TAC bir_number_of_mem_splits_IMPL_size_thm >>
    Q.PAT_X_ASSUM `A = SOME B` (K ALL_TAC) >>

    Q.PAT_X_ASSUM `bir_update_mmap A B C D = E` (ASSUME_TAC o GSYM) >>
    Q.PAT_X_ASSUM `bir_update_mmap A B C D = E` (ASSUME_TAC o GSYM) >>

    FULL_SIMP_TAC std_ss [] >>
    Q.PAT_X_ASSUM `A = B` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `A = B` (K ALL_TAC) >>

    POP_ASSUM MP_TAC >>
    POP_ASSUM MP_TAC >>

    Q.ID_SPEC_TAC `addr` >>
    Q.ID_SPEC_TAC `x` >>
    Q.ID_SPEC_TAC `mm1` >>
    Q.ID_SPEC_TAC `mm2` >>

    Induct_on `x` >> (
      FULL_SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]
    ) >>

    REPEAT STRIP_TAC >>
  )


  Cases_on `vt` >> Cases_on `at` >> Cases_on `i` >> (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    Cases_on `b2` >> (
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [] >>
      POP_ASSUM (K ALL_TAC) >>

      POP_ASSUM MP_TAC >>
      EVAL_TAC >>
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_store_in_mem_REWRS, bir_exp_memTheory.bir_update_mmap_def] >>
      POP_ASSUM (K ALL_TAC) >>
      POP_ASSUM (fn thm1 => POP_ASSUM (fn thm2 => ASSUME_TAC (GSYM thm2) >> ASSUME_TAC (GSYM thm1))) >>
      FULL_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY] >>
    )
  ) >>



  Cases_on `b2` >> (
  )





    FULL_SIMP_TAC std_ss [bir_store_in_mem_EQ_SOME]





bir_exp_memTheory.bir_store_in_mem_used_addrs_THM
bir_exp_memTheory.bir_store_in_mem_used_addrs_def
bir_exp_memTheory.bir_load_from_mem_used_addrs_def



    REV_FULL_SIMP_TAC std_ss [bir_eval_store_def, bir_exp_memTheory.bir_store_in_mem_def, LET_DEF] >>
    Cases_on `bir_number_of_mem_splits vt rty at` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    ) >>

    Cases_on `b2` >> Cases_on `x = 1` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

      FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_memeq_def] >>

      GEN_TAC >>
(*      Q.PAT_X_ASSUM `!a. P` (fn thm => ASSUME_TAC (((Q.SPECL [`a`])) thm) >>
                                       ASSUME_TAC (((Q.SPECL [`a`])) thm)) >>
*)
      Q.PAT_X_ASSUM `!a. P` (ASSUME_TAC o (Q.SPEC `a`)) >>
(*      FULL_SIMP_TAC std_ss [] >>*)
      cheat >>
      METIS_TAC [n2bs_bir_update_mmap_REVERSE_thm, n2bs_bir_update_mmap_thm]
*)









(*bir_env_vars_are_initialised_UNION*)
val bir_memeq_eval_eq = store_thm("bir_memeq_eval_eq", ``
      !e1 e2 aty vty mmap1 mmap2 v e ty env.
        (type_of_bir_exp e1 = SOME (BType_Mem aty vty)) ==>
        (type_of_bir_exp e2 = SOME (BType_Mem aty vty)) ==>
        (type_of_bir_exp e = SOME ty) ==>
        (bir_var_type v = BType_Mem aty vty) ==>
        (bir_env_vars_are_initialised env (((bir_vars_of_exp e) DIFF {v}) UNION (bir_vars_of_exp e1) UNION (bir_vars_of_exp e2))) ==>
        (bir_eval_exp e1 env = BVal_Mem aty vty mmap1) ==>
        (bir_eval_exp e2 env = BVal_Mem aty vty mmap2) ==>
        (bir_memeq aty vty mmap1 mmap2) ==>
(*        (bir_eval_exp (BExp_MemEq e1 e2) env = bir_val_true) ==> *)
        (
         (
          (bir_type_is_Imm ty) ==>
          ((bir_eval_exp (bir_exp_subst1 v e1 e) env) = (bir_eval_exp (bir_exp_subst1 v e2 e) env))
         )
         /\
         (
          (bir_type_is_Mem ty) ==>
          (
(*
           (bir_eval_memeq (bir_exp_subst1 v e1 e) (bir_exp_subst1 v e2 e) = bir_val_true) \/
           (BVal_Unknown)
*)
           !aty vty mmap1 mmap2.
           (bir_eval_exp (bir_exp_subst1 v e1 e) env = BVal_Mem aty vty mmap1) ==>
           (bir_eval_exp (bir_exp_subst1 v e2 e) env = BVal_Mem aty vty mmap2) ==>
           (bir_memeq aty vty mmap1 mmap2)
          )
         )
        )
``,

  Induct_on `e` >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_exp_EQ_SOME_REWRS, bir_exp_subst1_def, bir_exp_subst_def, bir_type_is_Imm_def] >>
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_type_is_Mem_def, BType_Bool_def]
  ) >- (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst_var_def, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >>

    CASE_TAC >>
    Cases_on `v` >> Cases_on `b` >>
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
  ) >- (
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_subst_var_def, finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >>
    Cases_on `v = b` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_type_is_Mem_def, bir_exp_memTheory.bir_memeq_def]
    )
  ) >- (
    (* cast *)
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    METIS_TAC []
  ) >- (
    (* unary *)
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    METIS_TAC []
  ) >- (
    (* binary *)
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>
    METIS_TAC [bir_env_vars_are_initialised_UNION]
  ) >- (
    (* binpred *)
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>
    METIS_TAC [bir_env_vars_are_initialised_UNION]
  ) >- (
    (* memeq *)
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_subst1_def] >>

    Q.ABBREV_TAC `e_1 = bir_exp_subst1 v e1 e` >>
    Q.ABBREV_TAC `e_2 = bir_exp_subst1 v e2 e` >>
    Q.ABBREV_TAC `e_3 = bir_exp_subst1 v e1 e'` >>
    Q.ABBREV_TAC `e_4 = bir_exp_subst1 v e2 e'` >>

    subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp e_1) UNION (bir_vars_of_exp e_2) UNION (bir_vars_of_exp e_3) UNION (bir_vars_of_exp e_4))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [Abbr `e_1`, Abbr `e_2`, Abbr `e_3`, Abbr `e_4`] >>
      FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS] >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      Cases_on `v IN bir_vars_of_exp e` >> Cases_on `v IN bir_vars_of_exp e'` >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
      )
    ) >>

    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>

    subgoal `(type_of_bir_val (bir_eval_exp e_1 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_2 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_3 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_4 env) = (type_of_bir_exp e))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars, bir_exp_subst1_TYPE_EQ]
    ) >>

    REV_FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_EQ_ELIMS] >>

    subgoal `(bir_memeq at vt f''' f'') /\
             (bir_memeq at vt f' f)` >- (
(*
      Q.PAT_X_ASSUM `!e. P` (ASSUME_TAC o (Q.SPECL [`e1`, `e2`, `aty`, `vty`, `mmap1`, `mmap2`, `v`, `env`])) >>
      REV_FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION]
*)
      CONJ_TAC >> METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>

    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_memeq_def] >>

    METIS_TAC [bir_memeq_EQ_REPL, bir_memeq_SYMM]

  ) >- (
    (* ifthenelse1 *)
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e'' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>
    METIS_TAC [bir_env_vars_are_initialised_UNION]
  ) >- (
    (* ifthenelse2 *)
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_subst1_def] >>

    Q.ABBREV_TAC `e_1 = bir_exp_subst1 v e1 e` >>
    Q.ABBREV_TAC `e_2 = bir_exp_subst1 v e2 e` >>
    Q.ABBREV_TAC `e_3 = bir_exp_subst1 v e1 e'` >>
    Q.ABBREV_TAC `e_4 = bir_exp_subst1 v e2 e'` >>
    Q.ABBREV_TAC `e_5 = bir_exp_subst1 v e1 e''` >>
    Q.ABBREV_TAC `e_6 = bir_exp_subst1 v e2 e''` >>

    subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp e_1) UNION (bir_vars_of_exp e_3) UNION (bir_vars_of_exp e_4) UNION (bir_vars_of_exp e_5) UNION (bir_vars_of_exp e_6))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [Abbr `e_1`, Abbr `e_3`, Abbr `e_4`, Abbr `e_5`, Abbr `e_6`] >>
      FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS] >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      Cases_on `v IN bir_vars_of_exp e` >> Cases_on `v IN bir_vars_of_exp e'` >> Cases_on `v IN bir_vars_of_exp e''` >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
      )
    ) >>

    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e'' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>

    subgoal `bir_eval_exp e_2 env = bir_eval_exp e_1 env` >- (
      METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>

    subgoal `(type_of_bir_val (bir_eval_exp e_1 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_3 env) = (type_of_bir_exp e')) /\
             (type_of_bir_val (bir_eval_exp e_4 env) = (type_of_bir_exp e')) /\
             (type_of_bir_val (bir_eval_exp e_5 env) = (type_of_bir_exp e')) /\
             (type_of_bir_val (bir_eval_exp e_6 env) = (type_of_bir_exp e'))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars, bir_exp_subst1_TYPE_EQ]
    ) >>

    FULL_SIMP_TAC std_ss [] >>
    REV_FULL_SIMP_TAC std_ss [] >>

    REV_FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_EQ_ELIMS] >>

    subgoal `(bir_memeq at vt f''' f'') /\
             (bir_memeq at vt f' f)` >- (
(*
      Q.PAT_X_ASSUM `!e. P` (ASSUME_TAC o (Q.SPECL [`e1`, `e2`, `aty`, `vty`, `mmap1`, `mmap2`, `v`, `env`])) >>
      REV_FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION]
*)
      CONJ_TAC >> METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>

    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

    FULL_SIMP_TAC std_ss [bir_expTheory.bir_eval_ifthenelse_REWRS] >>
    Cases_on `i = Imm1 1w` >> (
      FULL_SIMP_TAC std_ss [bir_expTheory.bir_eval_ifthenelse_REWRS] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      METIS_TAC []
    )

  ) >- (
    (* load *)
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_subst1_def] >>

    Q.ABBREV_TAC `e_1 = bir_exp_subst1 v e1 e` >>
    Q.ABBREV_TAC `e_2 = bir_exp_subst1 v e2 e` >>
    Q.ABBREV_TAC `e_3 = bir_exp_subst1 v e1 e'` >>
    Q.ABBREV_TAC `e_4 = bir_exp_subst1 v e2 e'` >>

    subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp e_1) UNION (bir_vars_of_exp e_2) UNION (bir_vars_of_exp e_3))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [Abbr `e_1`, Abbr `e_2`, Abbr `e_3`] >>
      FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS] >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      Cases_on `v IN bir_vars_of_exp e` >> Cases_on `v IN bir_vars_of_exp e'` >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
      )
    ) >>

    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>

    subgoal `bir_eval_exp e_4 env = bir_eval_exp e_3 env` >- (
      METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

    subgoal `(type_of_bir_val (bir_eval_exp e_1 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_2 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_3 env) = (type_of_bir_exp e'))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars, bir_exp_subst1_TYPE_EQ]
    ) >>

    REV_FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_EQ_ELIMS] >>

    subgoal `(bir_memeq at vt f' f)` >- (
      METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>


    REWRITE_TAC [bir_expTheory.bir_eval_load_BASIC_REWR] >>
    FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_load_from_mem_def] >>

    Cases_on `bir_number_of_mem_splits vt s at` >- (
      FULL_SIMP_TAC std_ss []
    ) >>
    FULL_SIMP_TAC std_ss [LET_DEF] >>

    Cases_on `b2` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_exp_memTheory.bir_memeq_def, bir_exp_memTheory.bir_load_bitstring_from_mmap_def] >>
      Q.PAT_X_ASSUM `!a. P` (ASSUME_TAC o (Q.GEN `n`) o (MATCH_MP n2bs_eq_bitstrings_thm) o (Q.SPEC `(b2n i + n)`)) >>
      ASM_REWRITE_TAC [] >>

      Cases_on `x = 1` >> (
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
        REV_FULL_SIMP_TAC std_ss []
      )
    )

  ) >- (
    (* store *)
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [GSYM bir_exp_subst1_def] >>

    Q.ABBREV_TAC `e_1 = bir_exp_subst1 v e1 e` >>
    Q.ABBREV_TAC `e_2 = bir_exp_subst1 v e2 e` >>
    Q.ABBREV_TAC `e_3 = bir_exp_subst1 v e1 e'` >>
    Q.ABBREV_TAC `e_4 = bir_exp_subst1 v e2 e'` >>
    Q.ABBREV_TAC `e_5 = bir_exp_subst1 v e1 e''` >>
    Q.ABBREV_TAC `e_6 = bir_exp_subst1 v e2 e''` >>

    subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp e_1) UNION (bir_vars_of_exp e_2) UNION (bir_vars_of_exp e_3) UNION (bir_vars_of_exp e_5))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

      FULL_SIMP_TAC std_ss [Abbr `e_1`, Abbr `e_2`, Abbr `e_3`, Abbr `e_5`] >>
      FULL_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS] >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      Cases_on `v IN bir_vars_of_exp e` >> Cases_on `v IN bir_vars_of_exp e'` >> Cases_on `v IN bir_vars_of_exp e''` >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
      )
    ) >>

    subgoal `(bir_env_vars_are_initialised env (bir_vars_of_exp e DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e' DIFF {v})) /\
             (bir_env_vars_are_initialised env (bir_vars_of_exp e'' DIFF {v}))` >- (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def]
    ) >>

    subgoal `(bir_eval_exp e_4 env = bir_eval_exp e_3 env) /\ (bir_eval_exp e_6 env = bir_eval_exp e_5 env)` >- (
      METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

    subgoal `(type_of_bir_val (bir_eval_exp e_1 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_2 env) = (type_of_bir_exp e)) /\
             (type_of_bir_val (bir_eval_exp e_3 env) = (type_of_bir_exp e')) /\
             (type_of_bir_val (bir_eval_exp e_5 env) = (type_of_bir_exp e''))` >- (
      Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>
      FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION] >>
      METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars, bir_exp_subst1_TYPE_EQ]
    ) >>

    REV_FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_EQ_ELIMS] >>

    subgoal `(bir_memeq at vt f' f)` >- (
      METIS_TAC [bir_env_vars_are_initialised_UNION]
    ) >>
    Q.PAT_X_ASSUM `!e. P` (K ALL_TAC) >>

    Q.PAT_X_ASSUM `bir_eval_store A B C D = E` (ASSUME_TAC o GSYM) >>
    Q.PAT_X_ASSUM `bir_eval_store A B C D = E` (ASSUME_TAC o GSYM) >>



    REV_FULL_SIMP_TAC std_ss [bir_expTheory.bir_eval_store_BASIC_REWR] >>
    Cases_on `bir_store_in_mem vt at i f b2 (b2n i')` >> Cases_on `bir_store_in_mem vt at i f' b2 (b2n i')` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    ) >>

    FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_memeq_def] >>

    GEN_TAC >>
    Cases_on `~((bir_mem_addr at a) IN bir_store_in_mem_used_addrs vt i at b2 (b2n i'))` >- (
      subgoal `(x (bir_mem_addr at a) = f (bir_mem_addr at a)) /\ (x' (bir_mem_addr at a) = f' (bir_mem_addr at a))` >- (
        METIS_TAC [bir_exp_memTheory.bir_store_in_mem_used_addrs_THM]
      ) >>

      METIS_TAC []
    ) >>

    METIS_TAC [bir_store_in_mem_TO_used_addrs_thm]

(*
    FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_store_in_mem_used_addrs_def, bir_exp_memTheory.bir_load_from_mem_used_addrs_def] >>

    Cases_on `bir_number_of_mem_splits vt (type_of_bir_imm i) at` >> (
      FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
    ) >>

    Cases_on `(~(x'' = 1)) /\ (b2 = BEnd_NoEndian)` >> (
      FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
    ) >- (

      Q.PAT_X_ASSUM `MEM A B` (MP_TAC) >>
      EVAL_TAC >>
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss [GSYM bir_exp_memTheory.bir_mem_addr_def] >>

      IMP_RES_TAC bir_exp_memTheory.bir_store_load_mem_THM >>
      REV_FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_load_from_mem_def, LET_DEF] >>

      Cases_on `b2` >> (
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

        ASSUME_TAC (EVAL ``COUNT_LIST 1``) >>
        FULL_SIMP_TAC list_ss [bir_exp_memTheory.bir_mem_concat_def, bir_exp_memTheory.bir_load_bitstring_from_mmap_def]
      )

    ) >>

*)

(*
    cheat
    Cases_on `b2` >> (
    )





    FULL_SIMP_TAC std_ss [bir_store_in_mem_EQ_SOME]





bir_exp_memTheory.bir_store_in_mem_used_addrs_THM
bir_exp_memTheory.bir_store_in_mem_used_addrs_def
bir_exp_memTheory.bir_load_from_mem_used_addrs_def



    REV_FULL_SIMP_TAC std_ss [bir_eval_store_def, bir_exp_memTheory.bir_store_in_mem_def, LET_DEF] >>
    Cases_on `bir_number_of_mem_splits vt rty at` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
    ) >>

    Cases_on `b2` >> Cases_on `x = 1` >> (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

      FULL_SIMP_TAC std_ss [bir_exp_memTheory.bir_memeq_def] >>

      GEN_TAC >>
(*      Q.PAT_X_ASSUM `!a. P` (fn thm => ASSUME_TAC (((Q.SPECL [`a`])) thm) >>
                                       ASSUME_TAC (((Q.SPECL [`a`])) thm)) >>
*)
      Q.PAT_X_ASSUM `!a. P` (ASSUME_TAC o (Q.SPEC `a`)) >>
(*      FULL_SIMP_TAC std_ss [] >>*)
      cheat >>
      METIS_TAC [n2bs_bir_update_mmap_REVERSE_thm, n2bs_bir_update_mmap_thm]
*)
  )
);








(*bir_exp_is_taut_def*)
val bir_exp_is_taut_imp_imp_subst1_mem_thm = store_thm("bir_exp_is_taut_imp_imp_subst1_mem_thm",``
!v' prem vs v ve e vty.
  (bir_type_is_Mem (bir_var_type v)) ==>
  (bir_var_type v' = bir_var_type v) ==>
  (type_of_bir_exp ve = SOME (bir_var_type v)) ==>
  (v IN (bir_vars_of_exp e)) ==> (* we need this, otherwise the free variables of "(bir_exp_subst1 v ve e)" do not contain the free variables of "ve", therefore we cannot use them for establishing var_set_well_typed on the right hand side, i.e., the right tautology *)
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp prem)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp ve)))) ==>
  (~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e)))) ==>
  (
   (bir_exp_is_taut (bir_exp_imp prem (bir_exp_subst1 v ve e)))
   <=>
   (bir_exp_is_taut (bir_exp_imp prem
                    (bir_exp_imp (BExp_MemEq (BExp_Den v') ve)
                                 (bir_exp_varsubst1 v v' e)
                    ))
   )
  )
``,

  REPEAT STRIP_TAC >>

  ASSUME_TAC (Q.SPECL [`v'`, `prem`, `v`, `ve`, `e`] bir_exp_is_taut_imp_subst1_varsubst1_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  POP_ASSUM (K ALL_TAC) >>

  EQ_TAC >- (
    FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_is_taut_def] >>
    REPEAT STRIP_TAC >|
    [
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Mem_def] >>

      FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
      subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
        FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
      ) >>
      METIS_TAC [bir_exp_subst_TYPE_EQ]
    ,

      ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

      REPEAT STRIP_TAC >> (
        FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_var_set_is_well_typed_def]
      ) >>
      METIS_TAC []
    ,
      ALL_TAC
    ] >>

    ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

    Q.PAT_X_ASSUM `!env.A` (ASSUME_TAC o (Q.SPEC `env`)) >>
    REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>

    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    subgoal `bir_is_bool_exp (BExp_MemEq (BExp_Den v') ve)` >- (
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Mem_def]
    ) >>

    subgoal `bir_is_bool_exp (bir_exp_subst1 v (BExp_Den v') e)` >- (
      FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
      subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
        FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
      ) >>
      METIS_TAC [bir_exp_subst_TYPE_EQ]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (BExp_MemEq (BExp_Den v') ve))` >- (
      REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v (BExp_Den v') e))` >- (
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION]
    ) >>

    subgoal `bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v ve e))` >- (
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION]
    ) >>


    Cases_on `bir_eval_exp prem env = bir_val_true` >> Cases_on `bir_eval_exp (BExp_MemEq (BExp_Den v') ve) env = bir_val_true` >> Cases_on `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) env = bir_val_false` >- (

      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      blastLib.BBLAST_TAC >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

      subgoal `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) env =  bir_eval_exp (bir_exp_subst1 v ve e) env` >- (
        subgoal `type_of_bir_val (bir_eval_exp (BExp_Den v') env) = SOME (bir_var_type v)` >- (
          METIS_TAC [type_of_bir_exp_def, type_of_bir_exp_THM_with_init_vars, bir_vars_of_exp_def]
        ) >>
        subgoal `type_of_bir_val (bir_eval_exp ve env) = SOME (bir_var_type v)` >- (
          METIS_TAC [type_of_bir_exp_THM_with_init_vars]
        ) >>

        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_type_is_Mem_def] >>
        REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>

        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [type_of_bir_val_EQ_ELIMS] >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_memeq_def] >>
        FULL_SIMP_TAC (std_ss) [GSYM bir_eval_exp_def] >>

        subgoal `type_of_bir_exp e = SOME (BType_Imm Bit1)` >- (
          METIS_TAC [bir_exp_subst1_TYPE_EQ, bir_is_bool_exp_def]
        ) >>

        subgoal `bir_env_vars_are_initialised env ((bir_vars_of_exp e DIFF {v}) UNION (bir_vars_of_exp (BExp_Den v')) UNION (bir_vars_of_exp ve))` >- (
          METIS_TAC [bir_env_vars_are_initialised_UNION, bir_vars_of_exp_def]
        ) >>

        subgoal `type_of_bir_exp (BExp_Den v') = type_of_bir_exp ve` >- (
          METIS_TAC [type_of_bir_exp_def]
        ) >>

        METIS_TAC [bir_memeq_eval_eq, bir_type_is_Imm_def]
      ) >>

      Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env = bir_val_false` >- (
        FULL_SIMP_TAC std_ss [bir_val_false_def, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>

        ASSUME_TAC (computeLib.EVAL_CONV ``(word_or (~(1w:word1)) 0w)``) >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) []
      ) >>
      REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm] >>

      REV_FULL_SIMP_TAC std_ss [bir_val_true_def] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      POP_ASSUM (ASSUME_TAC o blastLib.BBLAST_RULE) >>
      FULL_SIMP_TAC std_ss []

    ) >> (
      REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm] >>

      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
      blastLib.BBLAST_TAC >>
      EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      blastLib.BBLAST_TAC
    )
  ) >>

  (* the other implication direction *)
  FULL_SIMP_TAC std_ss [bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def, bir_exp_is_taut_def] >>
  REPEAT STRIP_TAC >|
  [
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_is_bool_exp_REWRS, type_of_bir_exp_def, bir_type_is_Imm_def] >>

    FULL_SIMP_TAC (std_ss) [bir_is_bool_exp_def, bir_exp_subst1_def] >>
    subgoal `FEVERY (\(v,e). type_of_bir_exp e = SOME (bir_var_type v)) (FUPDATE FEMPTY (v',ve))` >- (
      FULL_SIMP_TAC (std_ss) [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY]
    ) >>
    METIS_TAC [bir_exp_subst_TYPE_EQ]
  ,

    ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS] >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_vars_of_exp_def, bir_var_set_is_well_typed_UNION] >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_var_set_is_well_typed_def]
    ) >>
    METIS_TAC []
  ,
    ALL_TAC
  ] >>


  ASSUME_TAC (((Q.SPECL [`v'`, `v`, `ve`, `e`]) o GSYM) bir_exp_vartsubst1_intro_thm) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [bir_exp_varsubst1_REWR] >>
  POP_ASSUM (K ALL_TAC) >>

  subgoal `(bir_is_bool_exp (bir_exp_subst1 v ve e)) /\
           (bir_env_vars_are_initialised env (bir_vars_of_exp (bir_exp_subst1 v ve e)))` >- (
    REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>
    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS, bir_is_bool_exp_def] >>
    METIS_TAC [bir_exp_subst1_TYPE_EQ_GEN]
  ) >>

  Cases_on `bir_eval_exp prem env = bir_val_true` >> Cases_on `bir_eval_exp (bir_exp_subst1 v ve e) env = bir_val_false` >- (
    subgoal `bir_eval_exp (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not prem)
                          (bir_exp_subst1 v ve e)) env = bir_val_false` >- (
      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      blastLib.BBLAST_TAC >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      EVAL_TAC
    ) >>
    ASM_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_val_true_def, bir_val_false_def] >>
    EVAL_TAC >>

    Cases_on `env` >>
    Q.RENAME1_TAC `BEnv sm` >>

    ASSUME_TAC (Q.SPECL [`v`, `ve`, `bir_var_name v'`, `bir_var_type v'`, `SOME (bir_eval_exp ve (BEnv sm))`, `e`, `sm`] bir_wp_simp_eval_subst1_lemma) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    Q.ABBREV_TAC `sm' = (FUPDATE sm (bir_var_name v',bir_var_type v,SOME (bir_eval_exp ve (BEnv sm))))` >>
    Q.PAT_X_ASSUM `!env. A ==> B` (ASSUME_TAC o (Q.SPEC `BEnv sm'`)) >>

    subgoal `(bir_eval_bin_exp BIExp_Or
          (bir_eval_unary_exp BIExp_Not (bir_eval_exp prem (BEnv sm')))
          (bir_eval_bin_exp BIExp_Or
             (bir_eval_unary_exp BIExp_Not
                (bir_eval_memeq
                   (bir_env_read v' (BEnv sm'))
                   (bir_eval_exp ve (BEnv sm'))))
             (bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e)
                (BEnv sm'))) =
        BVal_Imm (Imm1 1w))` >- (
(*
bir_env_vars_are_initialised_FUPDATE_thm
*)
      subgoal `(bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp prem) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp prem)) /\
               (bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp ve) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp ve)) /\
               (bir_env_vars_are_initialised (BEnv sm) (bir_vars_of_exp e DIFF {v}) ==> bir_env_vars_are_initialised (BEnv sm') (bir_vars_of_exp e DIFF {v}))` >- (
        subgoal `~((bir_var_name v') IN (IMAGE bir_var_name (bir_vars_of_exp e DIFF {v})))` >- (
          FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >> METIS_TAC []
        ) >>
        FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_FUPDATE_thm, Abbr `sm'`, pred_setTheory.DIFF_SUBSET, pred_setTheory.IMAGE_SUBSET]
      ) >>

      

      REV_FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION] >>
      FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>
      FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_FUPDATE_thm, Abbr `sm'`] >>
      REV_FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_env_vars_are_initialised_def, bir_env_var_is_initialised_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE, type_of_bir_exp_THM_with_init_vars]
    ) >>
    Q.PAT_X_ASSUM `A ==> B` (K ALL_TAC) >>

    subgoal `bir_eval_exp prem (BEnv sm') = bir_eval_exp prem (BEnv sm)` >- (
      FULL_SIMP_TAC std_ss [bir_eval_exp_env_FUPDATE_thm, Abbr `sm'`]
    ) >>
    subgoal `(bir_eval_exp ve (BEnv sm')) = (bir_eval_exp ve (BEnv sm))` >- (
      FULL_SIMP_TAC std_ss [bir_eval_exp_env_FUPDATE_thm, Abbr `sm'`]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>
    FULL_SIMP_TAC (std_ss) [] >>

(*
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [Abbr `sm'`] >>
    REV_FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_env_read_def, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    REV_FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>


    subgoal `(type_of_bir_val (bir_eval_exp ve (BEnv sm))) = SOME (bir_var_type v)` >- (
      FULL_SIMP_TAC std_ss [bir_is_bool_exp_def, type_of_bir_exp_THM_with_init_vars]
    ) >>
    REV_FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>

    Q.PAT_X_ASSUM `BType_Imm it = bir_var_type v` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_bin_pred_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR] >>
*)

    subgoal `(bir_env_read v' (BEnv sm')) = (bir_eval_exp ve (BEnv sm))` >- (
(*
      POP_ASSUM (ASSUME_TAC o GSYM) >>
      ASM_REWRITE_TAC [] >>
*)
      ASM_SIMP_TAC (srw_ss()) [bir_env_read_def, Abbr `sm'`, bir_env_lookup_def, finite_mapTheory.FLOOKUP_UPDATE]
    ) >>
    subgoal `(bir_eval_memeq (bir_eval_exp ve (BEnv sm)) (bir_eval_exp ve (BEnv sm))) = bir_val_true` >- (
      subgoal `bir_val_is_Mem (bir_eval_exp ve (BEnv sm))` >- (
        FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, bir_exp_subst1_USED_VARS] >>
        REV_FULL_SIMP_TAC std_ss [bir_env_vars_are_initialised_UNION, bir_val_checker_TO_type_of] >>
        FULL_SIMP_TAC std_ss [bir_type_is_Mem_def] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        Cases_on `(bir_eval_exp ve (BEnv sm))` >> (
          FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_valuesTheory.type_of_bir_val_def]
        ) >>
        FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [bir_eval_memeq_def, bir_exp_memTheory.bir_memeq_def]
(*        METIS_TAC [bir_typing_expTheory.type_of_bir_exp_THM_with_init_vars] *)
      ) >>
      FULL_SIMP_TAC std_ss [bir_val_is_Mem_def, bir_eval_memeq_def, bir_exp_memTheory.bir_memeq_def, bir_val_true_def, bir_exp_immTheory.bir_bin_pred_Equal_REWR, bool2b_def, bool2w_def]
    ) >>

    Q.PAT_X_ASSUM `bir_val_false = A` (ASSUME_TAC o GSYM) >>

    subgoal `bir_eval_exp (bir_exp_subst1 v (BExp_Den v') e) (BEnv sm') = bir_eval_exp (bir_exp_subst1 v ve e) (BEnv sm')` >- (
      FULL_SIMP_TAC (std_ss) [bir_val_true_def, bir_exp_subst1_EVAL_EQ_GEN, GSYM bir_eval_exp_def]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>
    FULL_SIMP_TAC (std_ss) [] >>


    REV_FULL_SIMP_TAC std_ss [bir_val_true_def, bir_val_false_def] >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    Q.PAT_X_ASSUM `A = (1w:word1)` (ASSUME_TAC o blastLib.BBLAST_RULE) >>
    FULL_SIMP_TAC std_ss []


  ) >> (
    FULL_SIMP_TAC std_ss [bir_is_bool_exp_REWRS] >>

    REV_FULL_SIMP_TAC std_ss [bir_eval_exp_not_true_false_thm, bir_eval_exp_not_false_true_thm, bir_exp_subst1_USED_VARS, bir_env_vars_are_initialised_UNION, bir_vars_of_exp_def, bir_env_vars_are_initialised_UNION] >>

    FULL_SIMP_TAC (std_ss++bir_immtype_ss) [bir_eval_exp_def, bir_eval_unary_exp_REWRS, bir_exp_immTheory.bir_unary_exp_REWRS, bir_eval_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_REWRS, bir_val_true_def, bir_val_false_def, bir_exp_immTheory.bir_unary_exp_GET_OPER_def, bir_exp_immTheory.bir_bin_exp_GET_OPER_def, type_of_bir_imm_def] >>
    
    blastLib.BBLAST_TAC >>
    EVERY_ASSUM (fn thm => ASSUME_TAC (blastLib.BBLAST_RULE thm)) >>
    FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss) [] >>
    blastLib.BBLAST_TAC
  )
);









(*

``
!v' prem vs v ve e.
  (~(v' IN prem, ve, e, vs,...)) ==>
  (
   (bir_exp_is_taut (bir_exp_imp prem (bir_exp_varsubst vs (bir_exp_subst1 v ve e))))
   <=>
   (bir_exp_is_taut (bir_exp_imp prem
                    (bir_exp_imp (BExp_BinPred BIExp_Equal (BExp_Den v') (bir_exp_varsubst vs ve))
                                 (bir_exp_varsubst1 v v' (bir_exp_varsubst vs e))
                    ))
   )
  )
``
*)





(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)
(* --------------------------------------------------------------------------------------------------- *)


(*




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

