open HolKernel Parse boolLib bossLib BasicProvers;

open listTheory optionTheory pred_setTheory pred_setSimps;

open bir_programTheory bir_typing_progTheory bir_program_blocksTheory;
open HolBACoreSimps;

open resolutionTheory simulationTheory simulationFailTheory contractTransferTheory;

val _ = new_theory "resolve";


Theorem INDEX_FIND_append_stop:
  ∀P xs n ys.
    EXISTS P xs ⇒
    INDEX_FIND n P (xs ++ ys) =
    INDEX_FIND n P xs
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >- (
  SIMP_TAC list_ss []
) >>
SIMP_TAC list_ss [] >>
STRIP_TAC >>
ASM_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem INDEX_FIND_append_skip:
  ∀P xs n ys n' x.
    EVERY ($~ o P) xs ⇒
    INDEX_FIND n P (xs ++ ys) = SOME (n', x) ⇒
    ∃n''. INDEX_FIND n P ys = SOME (n'', x)
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >- (
  SIMP_TAC list_ss []
) >>
SIMP_TAC list_ss [] >>
ASM_SIMP_TAC arith_ss [INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [‘SUC n’, ‘n'’, ‘P’, ‘(xs ++ ys)’, ‘x’] holba_auxiliaryTheory.INDEX_FIND_PRE) >>
ASM_SIMP_TAC std_ss []
QED

Theorem INDEX_FIND_cons_stop:
  ∀P x n xs.
    P x ⇒
    INDEX_FIND n P (x::xs) = SOME (n, x)
Proof
SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem bir_get_program_block_info_by_label_append_stop:
  ∀bls1 bls2 l.
    EXISTS (\bl. bl.bb_label = l) bls1 ⇒
    bir_get_program_block_info_by_label (BirProgram (bls1 ++ bls2)) l =
    bir_get_program_block_info_by_label (BirProgram bls1) l
Proof
SIMP_TAC std_ss [bir_get_program_block_info_by_label_def,
                 INDEX_FIND_append_stop]
QED

Theorem bir_get_program_block_info_by_label_append_skip:
  ∀l bls1 bls2 i bl.
    EVERY (\bl. bl.bb_label ≠ l) bls1 ⇒
    bir_get_program_block_info_by_label (BirProgram (bls1 ++ bls2)) l = SOME (i, bl) ⇒
    ∃j. bir_get_program_block_info_by_label (BirProgram bls2) l = SOME (j, bl)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_def] >>
IRULE_TAC INDEX_FIND_append_skip >>
FULL_SIMP_TAC std_ss [combinTheory.o_ABS_R] >>
PROVE_TAC []
QED

Theorem bir_get_program_block_info_by_label_cons_stop:
  ∀bl bls l.
    bl.bb_label = l ⇒
    ∃n. bir_get_program_block_info_by_label (BirProgram (bl::bls)) l =
        SOME (n, bl)
Proof
SIMP_TAC std_ss [bir_get_program_block_info_by_label_def,
                 INDEX_FIND_cons_stop]
QED

Theorem bir_get_current_block_append_stop:
  ∀bls1 bls2 l.
    EXISTS (\bl. bl.bb_label = l) bls1 ⇒
    bir_get_current_block (BirProgram (bls1 ++ bls2)) (bir_block_pc l) =
    bir_get_current_block (BirProgram bls1) (bir_block_pc l)
Proof
SIMP_TAC (std_ss++holBACore_ss)
         [bir_get_current_block_def, bir_block_pc_def,
          bir_get_program_block_info_by_label_append_stop]
QED

Theorem bir_get_current_block_append_skip:
  ∀bls1 bls2 l.
    EVERY (\bl. bl.bb_label ≠ l) bls1 ⇒
    bir_get_current_block (BirProgram (bls1 ++ bls2)) (bir_block_pc l) =
    bir_get_current_block (BirProgram bls2) (bir_block_pc l)
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss)
         [bir_get_current_block_def, bir_block_pc_def] >>

Cases_on ‘bir_get_program_block_info_by_label (BirProgram bls2) l’ >>
ASM_SIMP_TAC std_ss [] >- (
  subgoal ‘∀bl. MEM bl (bls1 ++ bls2) ⇒ bl.bb_label ≠ l’ >- (
    FULL_SIMP_TAC list_ss [bir_get_program_block_info_by_label_THM,
                           EVERY_MEM] >>
    PROVE_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [GSYM bir_get_program_block_info_by_label_THM]
) >>

Cases_on ‘x’ >> rename1 ‘(j, bl')’ >>
subgoal ‘MEM l (bir_labels_of_program (BirProgram (bls1 ++ bls2)))’ >- (
    SIMP_TAC list_ss [bir_labels_of_program_def] >>
    PROVE_TAC [bir_labels_of_program_def,
               bir_get_program_block_info_by_label_MEM, pairTheory.PAIR]
) >>
FULL_SIMP_TAC std_ss [bir_get_program_block_info_by_label_MEM] >>
IMP_RES_TAC bir_get_program_block_info_by_label_append_skip >>
FULL_SIMP_TAC std_ss []
QED

Theorem bir_get_current_block_cons_stop:
  ∀bl bls l.
    bl.bb_label = l ⇒
    bir_get_current_block (BirProgram (bl::bls)) (bir_block_pc l) =
    SOME bl
Proof
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss)
         [bir_get_current_block_def, bir_block_pc_def] >>
IMP_RES_TAC bir_get_program_block_info_by_label_cons_stop >>
POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘bls’]) >>
ASM_SIMP_TAC std_ss []
QED

Theorem bir_get_current_block_cons_skip:
  ∀bl bls l.
    bl.bb_label ≠ l ⇒
    bir_get_current_block (BirProgram (bl::bls)) (bir_block_pc l) =
    bir_get_current_block (BirProgram bls) (bir_block_pc l)
Proof
REPEAT GEN_TAC >>
MP_TAC (Q.SPECL [‘[bl]’, ‘bls’, ‘l’] bir_get_current_block_append_skip) >>
SIMP_TAC list_ss []
QED


Definition replace_def:
  (replace f P [] = NONE) ∧
  (replace f P (h::t) =
   if P h then OPTION_MAP (\hs. hs ++ t) (f h)
   else OPTION_MAP (\t'. h::t') (replace f P t))
End

Theorem replace_SOME:
  ∀f P xs xs'.
    replace f P xs = SOME xs' ⇒
    (∃xs1 y xs2 ys.
       P y ∧ EVERY (\x. ~P x) xs1 ∧
       f y = SOME ys ∧
       xs = xs1 ++ y::xs2 ∧
       xs' = xs1 ++ ys ++ xs2)
Proof
Induct_on ‘xs’ >>
REPEAT GEN_TAC >>
SIMP_TAC std_ss [replace_def] >>
Cases_on ‘P h’ >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >- (
  Q.EXISTS_TAC ‘[]’ >>
  ASM_SIMP_TAC list_ss []
) >>

Q.PAT_X_ASSUM ‘∀f P xs'. _’ IMP_RES_TAC >>
Q.EXISTS_TAC ‘h::xs1’ >>
ASM_SIMP_TAC list_ss []
QED

Definition replace_block_def:
  replace_block (BirProgram p) l f =
  OPTION_MAP BirProgram (replace f (\b. b.bb_label = l) p)
End

Theorem replace_block_SOME:
  ∀p l f p'.
    replace_block (BirProgram p) l f = SOME (BirProgram p') ⇒
    (∃bls1 bl bls2 bls.
       bl.bb_label = l ∧ EVERY (\bl. bl.bb_label ≠ l) bls1 ∧
       f bl = SOME bls ∧
       p = bls1 ++ bl::bls2 ∧
       p' = bls1 ++ bls ++ bls2)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++bir_TYPES_ss) [replace_block_def] >>
STRIP_TAC >>
IMP_RES_TAC replace_SOME >>
PROVE_TAC []
QED

Definition refines_vars_def:
  refines_vars f =
  ∀bl bls.
    f bl = SOME bls ⇒
    BIGUNION (IMAGE bir_vars_of_block (set bls)) SUBSET bir_vars_of_block bl
End

(*Actually set equality should hold in all reasonable cases since
 variables should be used elsewhere, but is harder to prove and is not necessary*)
Theorem replace_block_SOME_vars:
  ∀p l f p'.
    refines_vars f ⇒
    replace_block p l f = SOME p' ⇒
    bir_vars_of_program p' SUBSET bir_vars_of_program p
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
Cases_on ‘p'’ >> rename1 ‘SOME (BirProgram p')’ >>
DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP replace_block_SOME) >>
ASM_SIMP_TAC (list_ss++PRED_SET_ss) [bir_vars_of_program_def] >>
FULL_SIMP_TAC std_ss [refines_vars_def, SUBSET_DEF, IN_UNION]
QED


Definition resolve_fail_block_def:
  (resolve_fail_block bl =
     case bl.bb_last_statement of
       BStmt_Jmp (BLE_Exp e) =>
         SOME [assert_block bl.bb_label bl.bb_statements (BStmt_Halt (BExp_Const (Imm1 0w)))]
     | _ => NONE)
End

Theorem resolve_fail_block_sound:
  ∀bl1 r.
    resolve_fail_block bl1 = SOME r ⇒
    (∃bl2. r = [bl2] ∧
           resolved_fail_block (bl1.bb_label) bl1 bl2)
Proof
REPEAT GEN_TAC >>
Cases_on ‘bl1’ >>
rename1 ‘bir_block_t l1 bss es’ >>
SIMP_TAC (std_ss++holBACore_ss) [resolve_fail_block_def] >>
REPEAT CASE_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [resolved_fail_block_cases] >>
PROVE_TAC []
QED

Theorem resolve_fail_block_refines_vars:
  refines_vars resolve_fail_block
Proof
SIMP_TAC std_ss [refines_vars_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC resolve_fail_block_sound >>
ASM_SIMP_TAC (list_ss++PRED_SET_ss) [] >>
subgoal ‘bir_vars_of_stmtE bl2.bb_last_statement = ∅’ >- (
  FULL_SIMP_TAC std_ss [resolve_fail_block_def] >>
  EVERY_CASE_TAC >>
  FULL_SIMP_TAC std_ss [assert_block_def] >>
  RW_TAC (std_ss++holBACore_ss) [bir_vars_of_stmtE_def]
) >>
PROVE_TAC [resolved_fail_block_vars]
QED

Definition resolve_fail_def:
  resolve_fail p l = replace_block p l resolve_fail_block
End

Theorem EXISTS_MEM_labels:
  ∀l bls.
    EXISTS (\bl. bl.bb_label = l) bls ⇒
    MEM l (bir_labels_of_program (BirProgram bls))
Proof
SIMP_TAC std_ss [bir_labels_of_program_def, MEM_MAP, EXISTS_MEM] >>
PROVE_TAC []
QED

Theorem resolve_fail_sound:
  ∀p l p'.
    resolve_fail p l = SOME p' ⇒
    resolved_fail l p p'
Proof
REPEAT GEN_TAC >>
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
Cases_on ‘p'’ >> rename1 ‘SOME (BirProgram p')’ >>
SIMP_TAC std_ss [resolve_fail_def] >>
DISCH_THEN (MP_TAC o MATCH_MP replace_block_SOME) >>
BETA_TAC >> STRIP_TAC >>
Q.PAT_X_ASSUM ‘_ = SOME _’
 (STRIP_ASSUME_TAC o MATCH_MP resolve_fail_block_sound) >>
‘bl2.bb_label = l’ by PROVE_TAC [resolved_fail_block_labels] >>

SIMP_TAC std_ss [resolved_fail_cases] >>
Q.LIST_EXISTS_TAC [‘bl’, ‘bl2’] >>
ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND] >>
REPEAT STRIP_TAC >| [
  (*labels*)
  ASM_SIMP_TAC list_ss [bir_labels_of_program_def],

  (*Changed block*)
  ASM_SIMP_TAC std_ss [bir_get_current_block_append_skip,
                       bir_get_current_block_cons_stop],
  ASM_SIMP_TAC std_ss [bir_get_current_block_append_skip,
                       bir_get_current_block_cons_stop],
  REV_FULL_SIMP_TAC std_ss [],

  (*Unchanged blocks*)
  Cases_on ‘EXISTS (\bl. bl.bb_label = l') bls1’ >- (
    ASM_SIMP_TAC std_ss [bir_get_current_block_append_stop, GSYM IS_SOME_EXISTS,
                         bir_get_current_block_block_pc_IS_SOME, EXISTS_MEM_labels]
  ) >>

  FULL_SIMP_TAC list_ss [combinTheory.o_ABS_R] >>
  subgoal ‘MEM l' (bir_labels_of_program (BirProgram bls2))’ >- (
    FULL_SIMP_TAC list_ss [bir_labels_of_program_def, MEM_MAP, EVERY_MEM] >>
    PROVE_TAC []
  ) >>
  ASM_SIMP_TAC list_ss [bir_get_current_block_append_skip,
                        bir_get_current_block_cons_skip,
                        GSYM IS_SOME_EXISTS,
                        bir_get_current_block_block_pc_IS_SOME]
]
QED

Theorem resolve_fail_simulated_termination:
 ∀p l p'.
    resolve_fail p l = SOME p' ⇒
    simulated_termination p p'
Proof
PROVE_TAC [resolve_fail_sound,
           simulated_fail_simulated_termination,
           resolved_fail_simulated_fail]
QED

Theorem resolve_fail_vars:
  ∀p l p'.
    resolve_fail p l = SOME p' ⇒
    bir_vars_of_program p' SUBSET bir_vars_of_program p
Proof
METIS_TAC [resolve_fail_def, replace_block_SOME_vars,
           resolve_fail_block_refines_vars]
QED

Theorem resolve_fail_labels:
  ∀p l p'.
    resolve_fail p l = SOME p' ⇒
    bir_labels_of_program p = bir_labels_of_program p'
Proof
REPEAT GEN_TAC >>
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
Cases_on ‘p'’ >> rename1 ‘SOME (BirProgram p')’ >>
SIMP_TAC std_ss [resolve_fail_def] >>
DISCH_THEN (MP_TAC o MATCH_MP replace_block_SOME) >>
BETA_TAC >> STRIP_TAC >>

IMP_RES_TAC resolve_fail_block_sound >>
‘bl2.bb_label = l’ by PROVE_TAC [resolved_fail_block_labels] >>
ASM_SIMP_TAC std_ss [Once (GSYM APPEND_ASSOC), APPEND] >>
ASM_SIMP_TAC list_ss [bir_labels_of_program_def]
QED


Definition resolve_block_def:
  (resolve_block bl v sl =
     case bl.bb_last_statement of
       BStmt_Jmp (BLE_Exp e) =>
         if type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v))
         then SOME [cjmp_block bl.bb_label bl.bb_statements e v sl;
                    jmp_block sl e]
         else NONE
     | _ => NONE)
End

Theorem resolve_block_sound:
  ∀bl1 v sl r.
    resolve_block bl1 v sl = SOME r ⇒
    (∃bl2 bl3.
       r = [bl2; bl3] ∧
       resolved_block (bl1.bb_label) v sl bl1 bl2 bl3)
Proof
REPEAT GEN_TAC >>
Cases_on ‘bl1’ >> rename1 ‘bir_block_t l1 bss es’ >>
Cases_on ‘es’ >>
SIMP_TAC (std_ss++holBACore_ss) [resolve_block_def] >>
rename1 ‘BStmt_Jmp e’ >>
Cases_on ‘e’ >>
SIMP_TAC (list_ss++holBACore_ss) [resolved_block_cases, jmp_block_def]
QED

Theorem resolve_block_refines_vars:
  ∀v sl. refines_vars (\bl. resolve_block bl v sl)
Proof
SIMP_TAC std_ss [refines_vars_def] >>
REPEAT GEN_TAC >>
DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP resolve_block_sound) >>
IMP_RES_TAC resolved_block_vars >>
ASM_SIMP_TAC (list_ss++PRED_SET_ss) []
QED

Definition resolve_def:
  resolve p l v sl = replace_block p l (\bl. resolve_block bl v sl)
End

Theorem resolve_sound:
  ∀p l v sl p'.
    fresh_label (BL_Label sl) p ⇒
    resolve p l v sl = SOME p' ⇒
    resolved l v sl p p'
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
Cases_on ‘p'’ >> rename1 ‘SOME (BirProgram p')’ >>
SIMP_TAC std_ss [resolve_def] >>
DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP replace_block_SOME) >>
FULL_SIMP_TAC std_ss [] >>
Q.PAT_X_ASSUM ‘_ = SOME _’
 (STRIP_ASSUME_TAC o MATCH_MP resolve_block_sound) >>
‘bl2.bb_label = l ∧ bl3.bb_label = BL_Label sl’
  by PROVE_TAC [resolved_block_labels] >>

SIMP_TAC std_ss [resolved_cases] >>
Q.LIST_EXISTS_TAC [‘bl’, ‘bl2’, ‘bl3’] >>
ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND] >>
REPEAT STRIP_TAC >| [
  (*labels*)
  ASM_SIMP_TAC list_ss [bir_labels_of_program_def] >>
  PROVE_TAC [],

  (*Changed block*)
  ASM_SIMP_TAC std_ss [bir_get_current_block_append_skip,
                       bir_get_current_block_cons_stop],
  ASM_SIMP_TAC std_ss [bir_get_current_block_append_skip,
                       bir_get_current_block_cons_stop],
  subgoal ‘EVERY (\bl. bl.bb_label ≠ BL_Label sl) bls1 ∧
           bl2.bb_label ≠ BL_Label sl’ >- (
    FULL_SIMP_TAC list_ss [fresh_label_def, bir_labels_of_program_def,
                           MEM_MAP, EVERY_MEM] >>
    PROVE_TAC []
  ) >>
  ASM_SIMP_TAC std_ss [bir_get_current_block_append_skip,
                       bir_get_current_block_cons_skip,
                       bir_get_current_block_cons_stop],
  REV_FULL_SIMP_TAC std_ss [],

  (*Unchanged blocks*)
  Cases_on ‘EXISTS (\bl. bl.bb_label = l') bls1’ >- (
    ASM_SIMP_TAC std_ss [bir_get_current_block_append_stop, GSYM IS_SOME_EXISTS,
                         bir_get_current_block_block_pc_IS_SOME, EXISTS_MEM_labels]
  ) >>

  FULL_SIMP_TAC list_ss [combinTheory.o_ABS_R] >>
  subgoal ‘MEM l' (bir_labels_of_program (BirProgram bls2))’ >- (
    FULL_SIMP_TAC list_ss [bir_labels_of_program_def, MEM_MAP, EVERY_MEM] >>
    PROVE_TAC []
  ) >>
  subgoal ‘bl3.bb_label ≠ l'’ >- (
    FULL_SIMP_TAC list_ss [fresh_label_def, bir_labels_of_program_def, MEM_MAP] >>
    PROVE_TAC []
  ) >>
  ASM_SIMP_TAC list_ss [bir_get_current_block_append_skip,
                        bir_get_current_block_cons_skip,
                        GSYM IS_SOME_EXISTS,
                        bir_get_current_block_block_pc_IS_SOME]
]
QED

Theorem resolve_simulated_termination:
  ∀p l v sl p'.
    fresh_label (BL_Label sl) p ⇒
    resolve p l v sl = SOME p' ⇒
    simulated_termination p p'
Proof
PROVE_TAC [resolve_sound,
           simulated_simulated_termination,
           resolved_simulated]
QED

Theorem resolve_vars:
  ∀p l v sl p'.
    resolve p l v sl = SOME p' ⇒
    bir_vars_of_program p' SUBSET bir_vars_of_program p
Proof
METIS_TAC [resolve_def, replace_block_SOME_vars,
           resolve_block_refines_vars]
QED

Theorem resolve_labels:
  ∀p l v sl p'.
    resolve p l v sl = SOME p' ⇒
    set (bir_labels_of_program p) SUBSET set (bir_labels_of_program p')
Proof
REPEAT GEN_TAC >>
Cases_on ‘p’ >> rename1 ‘BirProgram p’ >>
Cases_on ‘p'’ >> rename1 ‘SOME (BirProgram p')’ >>
SIMP_TAC std_ss [resolve_def] >>
DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP replace_block_SOME) >>
ASM_SIMP_TAC (list_ss++PRED_SET_ss) [bir_labels_of_program_def] >>
STRIP_TAC >- (
  SIMP_TAC (std_ss++PRED_SET_ss) [SUBSET_DEF]
) >>

FULL_SIMP_TAC std_ss [] >>
IMP_RES_TAC resolve_block_sound >>
ASM_SIMP_TAC list_ss [] >>
PROVE_TAC [resolved_block_labels]
QED


val _ = export_theory();
