(* ========================================================================= *)
(* FILE          : bil_typingScript.sml                                      *)
(* DESCRIPTION   : Typing for a model of BAP Intermediate Language.          *)
(*                 Based on Anthony Fox's binary words treatment.            *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;
open bil_imm_expTheory bil_mem_expTheory bil_envTheory;
open bil_expTheory bil_programTheory;
open wordsLib;

val _ = new_theory "bil_typing";


(* ------------------------------------------------------------------------- *)
(*  Expressions                                                              *)
(* ------------------------------------------------------------------------- *)

val bil_val_ss = rewrites (type_rws ``:bil_val_t``);
val bil_type_ss = rewrites (type_rws ``:bil_type_t``);


val type_of_bil_exp_def = Define `
  (type_of_bil_exp (Const i) = SOME (ImmType (type_of_bil_imm i))) /\

  (type_of_bil_exp (Den v) = SOME (bil_var_type v)) /\

  (type_of_bil_exp (Cast ct e rty) = (case (type_of_bil_exp e) of
      NONE => NONE
    | SOME ty => (if (bil_type_is_ImmType ty) then SOME (ImmType rty) else NONE))) /\

  (type_of_bil_exp (UnaryExp et e) = (case (type_of_bil_exp e) of
      NONE => NONE
    | SOME ty => (if (bil_type_is_ImmType ty) then
        SOME ty else NONE))) /\

  (type_of_bil_exp (BinExp et e1 e2) = (case (type_of_bil_exp e1,
       type_of_bil_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bil_type_is_ImmType ty1) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _ => NONE)) /\

  (type_of_bil_exp (BinPred pt e1 e2) = (case (type_of_bil_exp e1,
       type_of_bil_exp e2) of
       (SOME ty1, SOME ty2) => (if ((bil_type_is_ImmType ty1) /\ (ty2 = ty1)) then SOME BoolType else NONE)
       | _, _ => NONE)) /\


  (type_of_bil_exp (IfThenElse ec e1 e2) = (case (type_of_bil_exp ec, type_of_bil_exp e1,
       type_of_bil_exp e2) of
       (SOME ect, SOME ty1, SOME ty2) => (if ((ect = BoolType) /\ (ty2 = ty1)) then SOME ty1 else NONE)
       | _, _, _ => NONE)) /\

  (type_of_bil_exp (Load me ae en rty) = (case (type_of_bil_exp me, type_of_bil_exp ae) of
       (SOME (MemType aty vty), SOME (ImmType aty')) => (if (
            (aty = aty') /\ (if en = NoEndian then (vty = rty) else (bil_number_of_mem_splits vty rty <> NONE))
           ) then SOME (ImmType rty) else NONE)
       | _, _ => NONE)) /\

  (type_of_bil_exp (Store me ae en v) = (case (type_of_bil_exp me, type_of_bil_exp ae, type_of_bil_exp v) of
       (SOME (MemType aty vty), SOME (ImmType aty'), SOME (ImmType rty)) => (if (
            (aty = aty') /\ (if en = NoEndian then (vty = rty) else (bil_number_of_mem_splits vty rty <> NONE))
           ) then SOME (MemType aty vty) else NONE)
       | _, _, _ => NONE))`;



val type_of_bil_exp_THM = store_thm ("full_type_of_bil_exp_THM",
 ``!env. (is_valid_env env) ==> !e ty. (type_of_bil_exp e = SOME ty) ==>
              ((bil_eval_exp e env = Unknown) \/ (type_of_bil_val (bil_eval_exp e env) = SOME ty))``,

GEN_TAC >> STRIP_TAC >>
Induct >> (
  SIMP_TAC (list_ss++bil_val_ss) [bil_eval_exp_def, type_of_bil_exp_def,
     type_of_bil_val_def] >>
  REPEAT CASE_TAC
) >- (
  METIS_TAC[is_valid_env_read]
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_cast_REWRS, bil_type_is_ImmType_def] >>
  FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_eval_cast_REWRS,
    type_of_bil_gencast]
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_unary_exp_REWRS, bil_type_is_ImmType_def] >>
  FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_eval_unary_exp_REWRS,
    type_of_bil_unary_exp]
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_bin_exp_REWRS, bil_type_is_ImmType_def] >>
  FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_eval_bin_exp_REWRS,
    type_of_bil_bin_exp]
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_bin_pred_REWRS, bil_type_is_ImmType_def] >>
  FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_eval_bin_pred_REWRS,
    type_of_bil_val_def, BoolType_def, type_of_bool2b]
) >- (
  Cases_on `bil_eval_exp e env = Unknown` >- (
    ASM_SIMP_TAC std_ss [bil_eval_ifthenelse_REWRS]
  ) >>
  FULL_SIMP_TAC std_ss [bil_eval_ifthenelse_REWRS, bil_type_is_ImmType_def] >> (
    FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_eval_ifthenelse_REWRS,
      BoolType_def] >>
    CASE_TAC
  )
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_load_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bil_val_EQ_ELIMS, bil_eval_load_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    METIS_TAC[type_of_bil_load_from_mem]
  )
) >- (
  FULL_SIMP_TAC std_ss [bil_eval_store_Unknown_REWRS] >>
  FULL_SIMP_TAC std_ss [type_of_bil_val_EQ_ELIMS, bil_eval_store_def] >>
  REPEAT GEN_TAC >> REPEAT CASE_TAC
));



val type_of_bil_exp_EQ_SOME_REWRS = store_thm ("type_of_bil_exp_EQ_SOME_REWRS",``
  (!i ty. (type_of_bil_exp (Const i) = SOME ty) <=> (ty = ImmType (type_of_bil_imm i))) /\

  (!v ty. (type_of_bil_exp (Den v) = SOME ty) <=> (ty = bil_var_type v)) /\

  (!ct e ty ty'. (type_of_bil_exp (Cast ct e ty') = SOME ty) <=> (
     (ty = ImmType ty') /\ (?it. (type_of_bil_exp e = SOME (ImmType it))))) /\

  (!et e ty. (type_of_bil_exp (UnaryExp et e) = SOME ty) <=> (
     (bil_type_is_ImmType ty) /\ (type_of_bil_exp e = SOME ty))) /\

  (!et e1 e2 ty. (type_of_bil_exp (BinExp et e1 e2) = SOME ty) <=> (
     (bil_type_is_ImmType ty) /\ (type_of_bil_exp e1 = SOME ty) /\ (type_of_bil_exp e2 = SOME ty))) /\

  (!pt e1 e2 ty. (type_of_bil_exp (BinPred pt e1 e2) = SOME ty) <=> (
     (ty = BoolType) /\ (?it. (type_of_bil_exp e1 = SOME (ImmType it)) /\
                              (type_of_bil_exp e2 = SOME (ImmType it))))) /\

  (!ce e1 e2 ty. (type_of_bil_exp (IfThenElse ce e1 e2) = SOME ty) <=> (
     (type_of_bil_exp ce = SOME BoolType) /\
     (type_of_bil_exp e1 = SOME ty) /\
     (type_of_bil_exp e2 = SOME ty))) /\

  (!rty ty ae en me. (type_of_bil_exp (Load me ae en rty) = SOME ty) <=> (
     (ty = ImmType rty) /\ (?at vt. (type_of_bil_exp me = SOME (MemType at vt)) /\
                            (type_of_bil_exp ae = SOME (ImmType at)) /\
                            (if en = NoEndian then (vt = rty) else
                                  (bil_number_of_mem_splits vt rty <> NONE))))) /\

  (!ty ae en me v. (type_of_bil_exp (Store me ae en v) = SOME ty) <=> (
     ?at vt rty. (ty = MemType at vt) /\
             (type_of_bil_exp me = SOME (MemType at vt)) /\
             (type_of_bil_exp ae = SOME (ImmType at)) /\
             (type_of_bil_exp v = SOME (ImmType rty)) /\
             (if en = NoEndian then (vt = rty) else
                                  (bil_number_of_mem_splits vt rty <> NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bil_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >>
    FULL_SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def] >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bil_type_is_ImmType_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC std_ss [bil_type_is_ImmType_def] >> METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> METIS_TAC[]
));




val type_of_bil_exp_EQ_NONE_REWRS = store_thm ("type_of_bil_exp_EQ_NONE_REWRS",``
  (!i. ~(type_of_bil_exp (Const i) = NONE)) /\

  (!v. ~(type_of_bil_exp (Den v) = NONE)) /\

  (!ct e ty ty'. (type_of_bil_exp (Cast ct e ty') = NONE) <=> (
     (!ity. (type_of_bil_exp e <> SOME (ImmType ity))))) /\

  (!et e. (type_of_bil_exp (UnaryExp et e) = NONE) <=> (
     (!ity. type_of_bil_exp e <> SOME (ImmType ity)))) /\

  (!et e1 e2. (type_of_bil_exp (BinExp et e1 e2) = NONE) <=> !ity.
     (type_of_bil_exp e1 <> SOME (ImmType ity)) \/
     (type_of_bil_exp e2 <> SOME (ImmType ity))) /\

  (!pt e1 e2. (type_of_bil_exp (BinPred pt e1 e2) = NONE) <=> !ity.
     (type_of_bil_exp e1 <> SOME (ImmType ity)) \/
     (type_of_bil_exp e2 <> SOME (ImmType ity))) /\

  (!ce e1 e2 ty. (type_of_bil_exp (IfThenElse ce e1 e2) = NONE) <=> (
     (type_of_bil_exp ce <> SOME BoolType) \/
     (type_of_bil_exp e1 = NONE) \/
     (type_of_bil_exp e2 <> type_of_bil_exp e1))) /\

  (!rty ty ae en me. (type_of_bil_exp (Load me ae en rty) = NONE) <=> (
     (!at vt. (type_of_bil_exp me = SOME (MemType at vt)) /\
              (type_of_bil_exp ae = SOME (ImmType at)) ==>
              (if en = NoEndian then (vt <> rty) else
                   (bil_number_of_mem_splits vt rty = NONE))))) /\

  (!ty ae en me v. (type_of_bil_exp (Store me ae en v) = NONE) <=> (
     !at vt rty.
             (type_of_bil_exp me = SOME (MemType at vt)) /\
             (type_of_bil_exp ae = SOME (ImmType at)) /\
             (type_of_bil_exp v = SOME (ImmType rty)) ==>
             (if en = NoEndian then (vt <> rty) else
                                  (bil_number_of_mem_splits vt rty = NONE))))
``,

REPEAT CONJ_TAC >> (
  SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [type_of_bil_exp_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> FULL_SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def]
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def] >>
    METIS_TAC[]
  )
) >- (
  REPEAT GEN_TAC >> REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def] >>
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



val bil_is_well_typed_exp_def = Define `bil_is_well_typed_exp e <=>  (type_of_bil_exp e <> NONE)`


(* ------------------------------------------------------------------------- *)
(*  Looking at  variables used somewhere in an expression                    *)
(* ------------------------------------------------------------------------- *)

val bil_vars_of_exp_def = Define `
  (bil_vars_of_exp (Const _) = {}) /\
  (bil_vars_of_exp (Den v) = {v}) /\
  (bil_vars_of_exp (Cast _ e _) = bil_vars_of_exp e) /\
  (bil_vars_of_exp (UnaryExp _ e) = bil_vars_of_exp e) /\
  (bil_vars_of_exp (BinExp _ e1 e2) = (bil_vars_of_exp e1 UNION bil_vars_of_exp e2)) /\
  (bil_vars_of_exp (BinPred _ e1 e2) = (bil_vars_of_exp e1 UNION bil_vars_of_exp e2)) /\
  (bil_vars_of_exp (IfThenElse ec e1 e2) = (bil_vars_of_exp ec UNION bil_vars_of_exp e1 UNION bil_vars_of_exp e2)) /\
  (bil_vars_of_exp (Load me ae _ _) = (bil_vars_of_exp me UNION bil_vars_of_exp ae)) /\
  (bil_vars_of_exp (Store me ae _ ve) = (bil_vars_of_exp me UNION bil_vars_of_exp ae UNION bil_vars_of_exp ve))`


val type_of_bil_exp_THM_with_init_vars = store_thm ("type_of_bil_exp_THM_with_init_vars",
  ``!env. (is_valid_env env) ==>
          (!e ty. (type_of_bil_exp e = SOME ty) ==>
                  (bil_env_vars_are_initialised env (bil_vars_of_exp e)) ==>
                  (type_of_bil_val (bil_eval_exp e env) = SOME ty))``,

GEN_TAC >> STRIP_TAC >> Induct >> (
  SIMP_TAC (std_ss++bil_val_ss) [bil_eval_exp_def, BoolType_def,
    type_of_bil_exp_EQ_SOME_REWRS, bil_vars_of_exp_def,
    bil_env_vars_are_initialised_UNION, bil_env_vars_are_initialised_INSERT,
    bil_env_vars_are_initialised_EMPTY, PULL_EXISTS, PULL_FORALL, bil_type_is_ImmType_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++bil_val_ss) [type_of_bil_val_EQ_ELIMS, bil_type_is_ImmType_def]
) >- (
  rename1 `bil_env_read v env` >>
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [bil_env_read_def, bil_env_var_is_initialised_def, bil_var_name_def,
    bil_var_type_def, pairTheory.pair_case_thm] >>
  METIS_TAC[is_valid_env_lookup]
) >- (
  SIMP_TAC (std_ss++bil_val_ss) [bil_eval_cast_REWRS, type_of_bil_gencast]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_unary_exp_REWRS, type_of_bil_unary_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_bin_exp_REWRS, type_of_bil_bin_exp]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_bin_pred_REWRS, type_of_bil_val_def,
    type_of_bool2b, BoolType_def]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_ifthenelse_REWRS] >>
  METIS_TAC[]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_load_BASIC_REWR] >>
  rename1 `bil_load_from_mem vt ity mmap en (b2n i)` >>
  Cases_on `bil_load_from_mem vt ity mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_load_from_mem_EQ_NONE] >>
    Cases_on `en = NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bil_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bil_val_ss) [] >>
  METIS_TAC [type_of_bil_load_from_mem]
) >- (
  ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_eval_store_BASIC_REWR] >>
  rename1 `bil_store_in_mem vt ity mmap en (b2n i)` >>
  Cases_on `bil_store_in_mem vt ity mmap en (b2n i)` >- (
    POP_ASSUM MP_TAC >>
    ASM_SIMP_TAC (std_ss++bil_val_ss) [bil_store_in_mem_EQ_NONE] >>
    Cases_on `en = NoEndian` >> (
       FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [bil_number_of_mem_splits_ID]
    )
  ) >>
  ASM_SIMP_TAC (std_ss++bil_val_ss) []
));



(* ------------------------------------------------------------------------- *)
(*  Programs                                                                 *)
(* ------------------------------------------------------------------------- *)

val bil_is_well_typed_stmt_def = Define `
  (bil_is_well_typed_stmt (Declare _) = T) /\
  (bil_is_well_typed_stmt (Assign v e) = (type_of_bil_exp e = SOME (bil_var_type v))) /\
  (bil_is_well_typed_stmt (Jmp _) = T) /\
  (bil_is_well_typed_stmt (CJmp c _ _) = (type_of_bil_exp c = SOME BoolType)) /\
  (bil_is_well_typed_stmt (Halt e) = (type_of_bil_exp e <> NONE)) /\
  (bil_is_well_typed_stmt (Assert e) = (type_of_bil_exp e = SOME BoolType)) /\
  (bil_is_well_typed_stmt (Assume e) = (type_of_bil_exp e = SOME BoolType))`


val bil_is_well_typed_program_def = Define `bil_is_well_typed_program (BilProgram p) <=>
  (EVERY (\bl. EVERY bil_is_well_typed_stmt bl.statements) p)`;


val bil_get_current_statement_well_typed = store_thm ("bil_get_current_statement_well_typed",
  ``!p pc stmt. (bil_is_well_typed_program p /\
                (bil_get_current_statement p pc = SOME stmt)) ==>
                bil_is_well_typed_stmt stmt``,

Cases >> rename1 `BilProgram p` >>
SIMP_TAC std_ss [bil_is_well_typed_program_def, bil_get_current_statement_def] >>
REPEAT GEN_TAC >>
Cases_on `(bil_get_program_block_info_by_label (BilProgram p) pc.label)` >- (
  ASM_SIMP_TAC std_ss []
) >>
rename1 `_ = SOME xy` >> Cases_on `xy` >>
rename1 `_ = SOME (i, bl)` >>
ASM_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >>
`MEM stmt bl.statements` by METIS_TAC[listTheory.MEM_EL] >>
`MEM bl p` by METIS_TAC [bil_get_program_block_info_by_label_THM, listTheory.MEM_EL] >>
FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM] >>
METIS_TAC[]);


val _ = export_theory();
