open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_programTheory;
open wordsLib;

val _ = new_theory "bir_typing";


(* ------------------------------------------------------------------------- *)
(*  Expressions                                                              *)
(* ------------------------------------------------------------------------- *)

val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_type_ss = rewrites (type_rws ``:bir_type_t``);


val type_of_bir_exp_def = Define `
  (type_of_bir_exp (BExp_Const i) = SOME (BType_Imm (type_of_bir_imm i))) /\

  (type_of_bir_exp (BExp_Den v) = SOME (bir_var_type v)) /\

  (type_of_bir_exp (BExp_Cast ct e rty) = (case (type_of_bir_exp e) of
      NONE => NONE
    | SOME ty => (if (bir_type_is_Imm ty) then SOME (BType_Imm rty) else NONE))) /\

  (type_of_bir_exp (BExp_UnaryExp et e) = (case (type_of_bir_exp e) of
      NONE => NONE
    | SOME ty => (if (bir_type_is_Imm ty) then
        SOME ty else NONE))) /\

  (type_of_bir_exp (BExp_BinExp et e1 e2) = (case (type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bir_type_is_Imm ty1) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _ => NONE)) /\

  (type_of_bir_exp (BExp_BinPred pt e1 e2) = (case (type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bir_type_is_Imm ty1) /\ (ty2 = ty1)) then SOME BoolType else NONE)
       | _, _ => NONE)) /\


  (type_of_bir_exp (BExp_IfThenElse ec e1 e2) = (case (type_of_bir_exp ec, type_of_bir_exp e1,
       type_of_bir_exp e2) of
       (SOME ect, SOME ty1, SOME ty2) => (if ((ect = BoolType) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _, _ => NONE)) /\

  (type_of_bir_exp (BExp_Load me ae en rty) = (case (type_of_bir_exp me, type_of_bir_exp ae) of
       (SOME (BType_Mem aty vty), SOME (BType_Imm aty')) => (if (
            (aty = aty') /\ (if en = BEnd_NoEndian then (vty = rty) else (bir_number_of_mem_splits vty rty <> NONE))
           ) then SOME (BType_Imm rty) else NONE)
       | _, _ => NONE)) /\

  (type_of_bir_exp (BExp_Store me ae en v) = (case (type_of_bir_exp me, type_of_bir_exp ae, type_of_bir_exp v) of
       (SOME (BType_Mem aty vty), SOME (BType_Imm aty'), SOME (BType_Imm rty)) => (if (
            (aty = aty') /\ (if en = BEnd_NoEndian then (vty = rty) else (bir_number_of_mem_splits vty rty <> NONE))
           ) then SOME (BType_Mem aty vty) else NONE)
       | _, _, _ => NONE))`;



val type_of_bir_exp_THM = store_thm ("type_of_bir_exp_THM",
 ``!env. (bir_is_well_typed_env env) ==> !e ty. (type_of_bir_exp e = SOME ty) ==>
              ((bir_eval_exp e env = BVal_Unknown) \/ (type_of_bir_val (bir_eval_exp e env) = SOME ty))``,

GEN_TAC >> STRIP_TAC >>
Induct >> (
  SIMP_TAC (list_ss++bir_val_ss) [bir_eval_exp_def, type_of_bir_exp_def,
     type_of_bir_val_def] >>
  REPEAT CASE_TAC
) >- (
  METIS_TAC[bir_is_well_typed_env_read]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_cast_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_cast_REWRS,
    type_of_bir_gencast]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_unary_exp_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_unary_exp_REWRS,
    type_of_bir_unary_exp]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_bin_exp_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_bin_exp_REWRS,
    type_of_bir_bin_exp]
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_bin_pred_REWRS, bir_type_is_Imm_def] >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_bin_pred_REWRS,
    type_of_bir_val_def, BoolType_def, type_of_bool2b]
) >- (
  Cases_on `bir_eval_exp e env = BVal_Unknown` >- (
    ASM_SIMP_TAC std_ss [bir_eval_ifthenelse_REWRS]
  ) >>
  FULL_SIMP_TAC std_ss [bir_eval_ifthenelse_REWRS, bir_type_is_Imm_def] >> (
    FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_eval_ifthenelse_REWRS,
      BoolType_def] >>
    CASE_TAC
  )
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_load_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS, bir_eval_load_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    METIS_TAC[type_of_bir_load_from_mem]
  )
) >- (
  FULL_SIMP_TAC std_ss [bir_eval_store_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bir_val_EQ_ELIMS, bir_eval_store_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC
));



val type_of_bir_exp_EQ_SOME_REWRS = store_thm ("type_of_bir_exp_EQ_SOME_REWRS",``
  (!i ty. (type_of_bir_exp (BExp_Const i) = SOME ty) <=> (ty = BType_Imm (type_of_bir_imm i))) /\

  (!v ty. (type_of_bir_exp (BExp_Den v) = SOME ty) <=> (ty = bir_var_type v)) /\

  (!ct e ty ty'. (type_of_bir_exp (BExp_Cast ct e ty') = SOME ty) <=> (
     (ty = BType_Imm ty') /\ (?it. (type_of_bir_exp e = SOME (BType_Imm it))))) /\

  (!et e ty. (type_of_bir_exp (BExp_UnaryExp et e) = SOME ty) <=> (
     (bir_type_is_Imm ty) /\ (type_of_bir_exp e = SOME ty))) /\

  (!et e1 e2 ty. (type_of_bir_exp (BExp_BinExp et e1 e2) = SOME ty) <=> (
     (bir_type_is_Imm ty) /\ (type_of_bir_exp e1 = SOME ty) /\ (type_of_bir_exp e2 = SOME ty))) /\

  (!pt e1 e2 ty. (type_of_bir_exp (BExp_BinPred pt e1 e2) = SOME ty) <=> (
     (ty = BoolType) /\ (?it. (type_of_bir_exp e1 = SOME (BType_Imm it)) /\
                              (type_of_bir_exp e2 = SOME (BType_Imm it))))) /\

  (!ce e1 e2 ty. (type_of_bir_exp (BExp_IfThenElse ce e1 e2) = SOME ty) <=> (
     (type_of_bir_exp ce = SOME BoolType) /\
     (type_of_bir_exp e1 = SOME ty) /\
     (type_of_bir_exp e2 = SOME ty))) /\

  (!rty ty ae en me. (type_of_bir_exp (BExp_Load me ae en rty) = SOME ty) <=> (
     (ty = BType_Imm rty) /\ (?at vt. (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
                            (type_of_bir_exp ae = SOME (BType_Imm at)) /\
                            (if en = BEnd_NoEndian then (vt = rty) else
                                  (bir_number_of_mem_splits vt rty <> NONE))))) /\

  (!ty ae en me v. (type_of_bir_exp (BExp_Store me ae en v) = SOME ty) <=> (
     ?at vt rty. (ty = BType_Mem at vt) /\
             (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
             (type_of_bir_exp ae = SOME (BType_Imm at)) /\
             (type_of_bir_exp v = SOME (BType_Imm rty)) /\
             (if en = BEnd_NoEndian then (vt = rty) else
                                  (bir_number_of_mem_splits vt rty <> NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bir_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >>
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bir_type_is_Imm_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
));




val type_of_bir_exp_EQ_NONE_REWRS = store_thm ("type_of_bir_exp_EQ_NONE_REWRS",``
  (!i. ~(type_of_bir_exp (BExp_Const i) = NONE)) /\

  (!v. ~(type_of_bir_exp (BExp_Den v) = NONE)) /\

  (!ct e ty ty'. (type_of_bir_exp (BExp_Cast ct e ty') = NONE) <=> (
     (!ity. (type_of_bir_exp e <> SOME (BType_Imm ity))))) /\

  (!et e. (type_of_bir_exp (BExp_UnaryExp et e) = NONE) <=> (
     (!ity. type_of_bir_exp e <> SOME (BType_Imm ity)))) /\

  (!et e1 e2. (type_of_bir_exp (BExp_BinExp et e1 e2) = NONE) <=> !ity.
     (type_of_bir_exp e1 <> SOME (BType_Imm ity)) \/
     (type_of_bir_exp e2 <> SOME (BType_Imm ity))) /\

  (!pt e1 e2. (type_of_bir_exp (BExp_BinPred pt e1 e2) = NONE) <=> !ity.
     (type_of_bir_exp e1 <> SOME (BType_Imm ity)) \/
     (type_of_bir_exp e2 <> SOME (BType_Imm ity))) /\

  (!ce e1 e2 ty. (type_of_bir_exp (BExp_IfThenElse ce e1 e2) = NONE) <=> (
     (type_of_bir_exp ce <> SOME BoolType) \/
     (type_of_bir_exp e1 = NONE) \/
     (type_of_bir_exp e2 <> type_of_bir_exp e1))) /\

  (!rty ty ae en me. (type_of_bir_exp (BExp_Load me ae en rty) = NONE) <=> (
     (!at vt. (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
              (type_of_bir_exp ae = SOME (BType_Imm at)) ==>
              (if en = BEnd_NoEndian then (vt <> rty) else
                   (bir_number_of_mem_splits vt rty = NONE))))) /\

  (!ty ae en me v. (type_of_bir_exp (BExp_Store me ae en v) = NONE) <=> (
     !at vt rty.
             (type_of_bir_exp me = SOME (BType_Mem at vt)) /\
             (type_of_bir_exp ae = SOME (BType_Imm at)) /\
             (type_of_bir_exp v = SOME (BType_Imm rty)) ==>
             (if en = BEnd_NoEndian then (vt <> rty) else
                                  (bir_number_of_mem_splits vt rty = NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bir_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >>
    METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def] >>
    METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss) []
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
));



val bir_is_well_typed_exp_def = Define `bir_is_well_typed_exp e <=>  (type_of_bir_exp e <> NONE)`


(* ------------------------------------------------------------------------- *)
(*  Looking at  variables used somewhere in an expression                    *)
(* ------------------------------------------------------------------------- *)

val bir_vars_of_exp_def = Define `
  (bir_vars_of_exp (BExp_Const _) = {}) /\
  (bir_vars_of_exp (BExp_Den v) = {v}) /\
  (bir_vars_of_exp (BExp_Cast _ e _) = bir_vars_of_exp e) /\
  (bir_vars_of_exp (BExp_UnaryExp _ e) = bir_vars_of_exp e) /\
  (bir_vars_of_exp (BExp_BinExp _ e1 e2) = (bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_BinPred _ e1 e2) = (bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_IfThenElse ec e1 e2) = (bir_vars_of_exp ec UNION bir_vars_of_exp e1 UNION bir_vars_of_exp e2)) /\
  (bir_vars_of_exp (BExp_Load me ae _ _) = (bir_vars_of_exp me UNION bir_vars_of_exp ae)) /\
  (bir_vars_of_exp (BExp_Store me ae _ ve) = (bir_vars_of_exp me UNION bir_vars_of_exp ae UNION bir_vars_of_exp ve))`


val type_of_bir_exp_THM_with_init_vars = store_thm ("type_of_bir_exp_THM_with_init_vars",
  ``!env. (bir_is_well_typed_env env) ==>
          (!e ty. (type_of_bir_exp e = SOME ty) ==>
                  (bir_env_vars_are_initialised env (bir_vars_of_exp e)) ==>
                  (type_of_bir_val (bir_eval_exp e env) = SOME ty))``,

GEN_TAC >> STRIP_TAC >> Induct >> (
  SIMP_TAC (std_ss++bir_val_ss) [bir_eval_exp_def, BoolType_def,
    type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def,
    bir_env_vars_are_initialised_UNION, bir_env_vars_are_initialised_INSERT,
    bir_env_vars_are_initialised_EMPTY, PULL_EXISTS, PULL_FORALL, bir_type_is_Imm_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++bir_val_ss) [type_of_bir_val_EQ_ELIMS, bir_type_is_Imm_def]
) >- (
  rename1 `bir_env_read v env` >>
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [bir_env_read_def, bir_env_var_is_initialised_def, bir_var_name_def,
    bir_var_type_def, pairTheory.pair_case_thm] >>
  METIS_TAC[bir_is_well_typed_env_lookup]
) >- (
  SIMP_TAC (std_ss++bir_val_ss) [bir_eval_cast_REWRS, type_of_bir_gencast]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_unary_exp_REWRS, type_of_bir_unary_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_exp_REWRS, type_of_bir_bin_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_bin_pred_REWRS, type_of_bir_val_def,
    type_of_bool2b, BoolType_def]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_ifthenelse_REWRS] >>
  METIS_TAC[]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_load_BASIC_REWR] >>
  rename1 `bir_load_from_mem vt ity mmap en (b2n i)` >>
  Cases_on `bir_load_from_mem vt ity mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_load_from_mem_EQ_NONE] >>
    Cases_on `en = BEnd_NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bir_val_ss) [] >>
  METIS_TAC [type_of_bir_load_from_mem]
) >- (
  ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_eval_store_BASIC_REWR] >>
  rename1 `bir_store_in_mem vt ity mmap en (b2n i)` >>
  Cases_on `bir_store_in_mem vt ity mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bir_val_ss) [bir_store_in_mem_EQ_NONE] >>
    Cases_on `en = BEnd_NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bir_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bir_val_ss) []
));



(* ------------------------------------------------------------------------- *)
(*  Programs                                                                 *)
(* ------------------------------------------------------------------------- *)

val bir_is_well_typed_stmtE_def = Define `
  (bir_is_well_typed_stmtE (BStmt_Jmp _) = T) /\
  (bir_is_well_typed_stmtE (BStmt_CJmp c _ _) = (type_of_bir_exp c = SOME BoolType)) /\
  (bir_is_well_typed_stmtE (BStmt_Halt e) = (type_of_bir_exp e <> NONE))`

val bir_is_well_typed_stmtB_def = Define `
  (bir_is_well_typed_stmtB (BStmt_Declare _) = T) /\
  (bir_is_well_typed_stmtB (BStmt_Assign v e) = (type_of_bir_exp e = SOME (bir_var_type v))) /\
  (bir_is_well_typed_stmtB (BStmt_Assert e) = (type_of_bir_exp e = SOME BoolType)) /\
  (bir_is_well_typed_stmtB (BStmt_Assume e) = (type_of_bir_exp e = SOME BoolType))`;

val bir_is_well_typed_stmt_def = Define `
  (bir_is_well_typed_stmt (BStmtE s) = bir_is_well_typed_stmtE s) /\
  (bir_is_well_typed_stmt (BStmtB s) = bir_is_well_typed_stmtB s)`;

val bir_is_well_typed_block_def = Define `bir_is_well_typed_block bl <=>
  ((EVERY bir_is_well_typed_stmtB bl.bb_statements) /\ 
   (bir_is_well_typed_stmtE bl.bb_last_statement))`;

val bir_is_well_typed_program_def = Define `bir_is_well_typed_program (BirProgram p) <=>
  (EVERY bir_is_well_typed_block p)`;


val bir_get_current_statement_well_typed = store_thm ("bir_get_current_statement_well_typed",
  ``!p pc stmt. (bir_is_well_typed_program p /\
                (bir_get_current_statement p pc = SOME stmt)) ==>
                bir_is_well_typed_stmt stmt``,

Cases >> rename1 `BirProgram p` >>
SIMP_TAC std_ss [bir_is_well_typed_program_def, bir_get_current_statement_def] >>
GEN_TAC >>
Cases_on `(bir_get_program_block_info_by_label (BirProgram p) pc.bpc_label)` >- (
  ASM_SIMP_TAC std_ss []
) >>
rename1 `_ = SOME xy` >> Cases_on `xy` >>
rename1 `_ = SOME (i, bl)` >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [] >>
Cases_on `EVERY bir_is_well_typed_block p` >> ASM_SIMP_TAC std_ss [] >>
`bir_is_well_typed_block bl` by (
  `MEM bl p` by METIS_TAC [bir_get_program_block_info_by_label_THM, listTheory.MEM_EL] >>
  METIS_TAC[listTheory.EVERY_MEM]
) >>
CASE_TAC >> (
  FULL_SIMP_TAC std_ss [bir_is_well_typed_block_def, bir_is_well_typed_stmt_def]
) >>
METIS_TAC[listTheory.EVERY_MEM, listTheory.MEM_EL]);


val _ = export_theory();
