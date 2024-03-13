open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory listTheory pred_setTheory;
open finite_mapTheory;
open bir_auxiliaryTheory bir_immTheory;

val _ = new_theory "bir_values";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));

(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_val_t =
    BVal_Imm bir_imm_t
  | BVal_Mem bir_immtype_t (*Addr-Type*) bir_immtype_t (* value-type *) (num |-> num)
End


Datatype:
  bir_type_t =
    BType_Imm bir_immtype_t
  | BType_Mem bir_immtype_t (* Addr-Type *) bir_immtype_t (* Value-Type *)
End

Definition bir_val_default_def:
  (bir_val_default (BType_Imm Bit1)   = BVal_Imm (Imm1   0w)) /\
  (bir_val_default (BType_Imm Bit8)   = BVal_Imm (Imm8   0w)) /\
  (bir_val_default (BType_Imm Bit16)  = BVal_Imm (Imm16  0w)) /\
  (bir_val_default (BType_Imm Bit32)  = BVal_Imm (Imm32  0w)) /\
  (bir_val_default (BType_Imm Bit64)  = BVal_Imm (Imm64  0w)) /\
  (bir_val_default (BType_Imm Bit128) = BVal_Imm (Imm128 0w)) /\
  (bir_val_default (BType_Mem at vt)  = BVal_Mem at vt (FEMPTY))
End

Definition BType_Bool_def:
  BType_Bool = BType_Imm Bit1
End


val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_type_ss = rewrites (type_rws ``:bir_type_t``);


(* ------------------------------------------------------------------------- *)
(*  Checkers for Values                                                      *)
(* ------------------------------------------------------------------------- *)

Definition bir_val_is_Imm_def:
  bir_val_is_Imm v = ?b. (v = BVal_Imm b)
End
Definition bir_val_is_Imm_s_def:
  bir_val_is_Imm_s s v = ?n. (v = BVal_Imm (n2bs n s))
End
Definition bir_val_is_Bool_def:
  bir_val_is_Bool = bir_val_is_Imm_s Bit1
End
Definition bir_val_is_Mem_def:
  bir_val_is_Mem v = ?at vt mmap. (v = BVal_Mem at vt mmap)
End

val bir_val_checker_DEFS = save_thm ("bir_val_checker_DEFS", LIST_CONJ [
  bir_val_is_Imm_def, bir_val_is_Imm_s_def,
  bir_val_is_Bool_def, bir_val_is_Mem_def]);


Theorem bir_val_is_Imm_s_ALT_DEF:
  !s v. bir_val_is_Imm_s s v <=>
  (?b. (v = BVal_Imm b) /\ (type_of_bir_imm b = s))
Proof
Cases_on `v` >> (
  SIMP_TAC (std_ss ++ bir_val_ss) [bir_val_is_Imm_s_def,
    type_of_bir_imm_n2bs_INTRO]
)
QED


Theorem bir_val_checker_REWRS:
  (!b. bir_val_is_Imm (BVal_Imm b)) /\
    (!at vt mmap. ~(bir_val_is_Imm (BVal_Mem at vt mmap))) /\

    (!b. ~(bir_val_is_Mem (BVal_Imm b))) /\
    (!at vt mmap. (bir_val_is_Mem (BVal_Mem at vt mmap))) /\

    (!s b. bir_val_is_Imm_s s (BVal_Imm b) <=> (type_of_bir_imm b = s)) /\
    (!s at vt mmap. ~(bir_val_is_Imm_s s (BVal_Mem at vt mmap))) /\

    (!b. bir_val_is_Bool (BVal_Imm b) <=> (type_of_bir_imm b = Bit1)) /\
    (!at vt mmap. ~(bir_val_is_Bool (BVal_Mem at vt mmap)))
Proof
REWRITE_TAC[bir_val_is_Imm_s_ALT_DEF, bir_val_is_Bool_def] >>
  SIMP_TAC (std_ss ++ bir_val_ss) [bir_val_checker_DEFS]
QED


Theorem bir_val_is_Imm_s_IMPL:
  !s v. bir_val_is_Imm_s s v ==> bir_val_is_Imm v
Proof
SIMP_TAC (std_ss++bir_val_ss) [bir_val_is_Imm_def, bir_val_is_Imm_s_def,
  GSYM LEFT_FORALL_IMP_THM]
QED

Theorem bir_val_is_Bool_IMPL:
  !v. bir_val_is_Bool v ==> bir_val_is_Imm v
Proof
SIMP_TAC (std_ss++bir_val_ss) [bir_val_is_Imm_def, bir_val_is_Bool_def,
  bir_val_is_Imm_s_def, GSYM LEFT_FORALL_IMP_THM]
QED



(* ------------------------------------------------------------------------- *)
(*  Boolean Values                                                           *)
(* ------------------------------------------------------------------------- *)

Definition bir_dest_bool_val_def:
  (bir_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_dest_bool_val _ = NONE)
End

Theorem bir_dest_bool_val_EQ_SOME:
  !v b. (bir_dest_bool_val v = SOME b) <=> (v = BVal_Imm (bool2b b))
Proof
Cases >> SIMP_TAC (std_ss++bir_val_ss) [bir_dest_bool_val_def] >>
rename1 `BVal_Imm i` >>
Cases_on `i` >> SIMP_TAC (std_ss++bir_imm_ss) [bir_dest_bool_val_def, bool2b_NEQ_IMM_ELIMS] >>
SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def] >>
Cases_on `b'` >> SIMP_TAC std_ss [bool2w_def] >>
METIS_TAC[word1_dichotomy, word1_distinct]
QED

Theorem bir_dest_bool_val_EQ_NONE:
  !v. (bir_dest_bool_val v = NONE) <=> ~(bir_val_is_Bool v)
Proof
Cases >> SIMP_TAC std_ss [bir_val_checker_REWRS, bir_dest_bool_val_def] >>
Cases_on `b` >> SIMP_TAC (std_ss++bir_imm_ss) [bir_val_checker_REWRS, bir_dest_bool_val_def,
  type_of_bir_imm_def]
QED

Theorem bir_dest_bool_val_bool2b:
  !b. bir_dest_bool_val (BVal_Imm (bool2b b)) = SOME b
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss) [
  bool2b_def, bool2w_def, bir_dest_bool_val_def]
QED

(* TODO: See if this really needs to be used *)
Definition bir_dest_bool_val_opt_def:
  (bir_dest_bool_val_opt (SOME v) = bir_dest_bool_val v) /\
  (bir_dest_bool_val_opt _ = NONE)
End

(* TODO: See if this really needs to be used *)
Theorem bir_dest_bool_val_opt_EQ_SOME:
  !v b.
    (bir_dest_bool_val_opt v = SOME b) <=> (v = SOME (BVal_Imm (bool2b b)))
Proof
Cases >> (
  SIMP_TAC std_ss [bir_dest_bool_val_opt_def]
) >>
Cases_on `x` >> (
  SIMP_TAC (std_ss++bir_val_ss) [bir_dest_bool_val_opt_def, bir_dest_bool_val_def]
) >>
rename1 `BVal_Imm i` >>
Cases_on `i` >> SIMP_TAC (std_ss++bir_imm_ss) [bir_dest_bool_val_def, bool2b_NEQ_IMM_ELIMS] >>
SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def] >>
Cases_on `b'` >> SIMP_TAC std_ss [bool2w_def] >>
METIS_TAC[word1_dichotomy, word1_distinct]
QED

(* TODO: See if this really needs to be used *)
Theorem bir_dest_bool_val_opt_EQ_NONE:
  !v_opt.
    (bir_dest_bool_val_opt v_opt = NONE) <=>
      ((?v. (v_opt = SOME v) /\ ~(bir_val_is_Bool v)) \/
       (v_opt = NONE)
      )
Proof
Cases >> (
  SIMP_TAC std_ss [bir_dest_bool_val_opt_def]
) >>
Cases_on `x` >> (
  SIMP_TAC std_ss [bir_val_checker_REWRS, bir_dest_bool_val_opt_def, bir_dest_bool_val_def]
) >>
rename1 `BVal_Imm i` >>
Cases_on `i` >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_val_checker_REWRS, bir_dest_bool_val_def,
    type_of_bir_imm_def]
)
QED

(* TODO: See if this really needs to be used *)
Theorem bir_dest_bool_val_opt_bool2b:
  !b.
    bir_dest_bool_val_opt (SOME (BVal_Imm (bool2b b))) = SOME b
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss)
  [bool2b_def, bool2w_def, bir_dest_bool_val_opt_def, bir_dest_bool_val_def]
QED

(* ------------------------------------------------------------------------- *)
(*  Some basic typing                                                        *)
(* ------------------------------------------------------------------------- *)

Definition type_of_bir_val_def:
  (type_of_bir_val (BVal_Imm imm) = (BType_Imm (type_of_bir_imm imm))) /\
  (type_of_bir_val (BVal_Mem at vt _) = (BType_Mem at vt))
End

Definition bir_type_is_Imm_def:
  bir_type_is_Imm ty = (?s. ty = BType_Imm s)
End
Definition bir_type_is_Imm_s_def:
  bir_type_is_Imm_s s ty = (ty = BType_Imm s)
End
Definition bir_type_is_Bool_def:
  bir_type_is_Bool ty = (ty = BType_Imm Bit1)
End
Definition bir_type_is_Mem_def:
  bir_type_is_Mem ty = (?at vt. ty = BType_Mem at vt)
End

val bir_type_checker_DEFS = save_thm ("bir_type_checker_DEFS", LIST_CONJ [
  bir_type_is_Imm_def, bir_type_is_Imm_s_def,
  bir_type_is_Bool_def, bir_type_is_Mem_def]);


Theorem bir_type_checker_REWRS:
  (!b. bir_type_is_Imm (BType_Imm b)) /\
    (!at vt. ~(bir_type_is_Imm (BType_Mem at vt))) /\

    (!b. ~(bir_type_is_Mem (BType_Imm b))) /\
    (!at vt. (bir_type_is_Mem (BType_Mem at vt))) /\

    (!s b. bir_type_is_Imm_s s (BType_Imm b) <=> (b = s)) /\
    (!s at vt. ~(bir_type_is_Imm_s s (BType_Mem at vt))) /\

    (!b. bir_type_is_Bool BType_Bool <=> T) /\

    (!b. bir_type_is_Bool (BType_Imm b) <=> (b = Bit1)) /\
    (!at vt. ~(bir_type_is_Bool (BType_Mem at vt)))
Proof
SIMP_TAC (std_ss ++ bir_type_ss) [bir_type_checker_DEFS, BType_Bool_def]
QED


Theorem bir_type_is_Imm_s_IMPL:
  !s v. bir_type_is_Imm_s s v ==> bir_type_is_Imm v
Proof
SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def, bir_type_is_Imm_s_def]
QED


Theorem bir_type_is_Bool_IMPL:
  !v. bir_type_is_Bool v ==> bir_type_is_Imm v
Proof
SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def, bir_type_is_Bool_def]
QED


Theorem type_of_bir_val_EQ_ELIMS:
  (!v ty. (type_of_bir_val v = (BType_Imm ty)) <=>
            (?i. (type_of_bir_imm i = ty) /\ (v = BVal_Imm i))) /\
    (!v aty vty. (type_of_bir_val v = (BType_Mem aty vty)) <=>
            (?f. (v = BVal_Mem aty vty f)))
Proof
REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC (std_ss++bir_val_ss++bir_type_ss) [type_of_bir_val_def]
)
QED


Theorem bir_val_checker_TO_type_of:
  (!v ty. (bir_val_is_Imm_s ty v) <=> (type_of_bir_val v = (BType_Imm ty))) /\
    (!v. (bir_val_is_Imm v) <=> (?ty. type_of_bir_val v = (BType_Imm ty))) /\
    (!v. (bir_val_is_Bool v) <=> (type_of_bir_val v = BType_Bool)) /\
    (!v. (bir_val_is_Mem v <=>
         (?aty vty. type_of_bir_val v = (BType_Mem aty vty))))
Proof
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [type_of_bir_val_EQ_ELIMS, BType_Bool_def, bir_val_is_Bool_def,
  bir_val_is_Imm_s_ALT_DEF, bir_val_is_Imm_def,
  bir_val_is_Mem_def] >>
METIS_TAC[]
QED


(* ------------------------------------------------------------------------- *)
(*  Finiteness                                                               *)
(* ------------------------------------------------------------------------- *)

Definition bir_type_t_LIST_def:
  bir_type_t_LIST =
  (MAP BType_Imm bir_immtype_t_LIST) ++
  (FLAT (MAP (\f. MAP f bir_immtype_t_LIST) (MAP BType_Mem bir_immtype_t_LIST)))
End

val bir_type_t_LIST_EVAL = save_thm ("bir_type_t_LIST_EVAL", EVAL ``bir_type_t_LIST``);

Theorem bir_type_t_LIST_THM:
  !ty. MEM ty bir_type_t_LIST
Proof
SIMP_TAC list_ss [bir_type_t_LIST_def, MEM_MAP, MEM_FLAT, PULL_EXISTS,
  bir_immtype_t_LIST_THM] >>
Cases >> METIS_TAC[]
QED

Theorem bir_type_t_UNIV_SPEC:
  (UNIV:bir_type_t set) = set bir_type_t_LIST
Proof
SIMP_TAC list_ss [EXTENSION, bir_type_t_LIST_THM, IN_UNIV]
QED


Theorem bir_type_t_FINITE_UNIV:
  FINITE (UNIV : (bir_type_t set))
Proof
REWRITE_TAC[bir_type_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]
QED


(* ------------------------------------------------------------------------- *)
(*  Default value                                                            *)
(* ------------------------------------------------------------------------- *)

Definition bir_default_value_of_type_def:
  (bir_default_value_of_type (BType_Imm s) = BVal_Imm (n2bs 0 s)) /\
  (bir_default_value_of_type (BType_Mem a_s v_s) = BVal_Mem a_s v_s (FEMPTY))
End

Theorem bir_default_value_of_type_SPEC:
  !ty. type_of_bir_val (bir_default_value_of_type ty) = ty
Proof
Cases >> (
  SIMP_TAC std_ss [bir_default_value_of_type_def, type_of_bir_val_def, type_of_n2bs]
)
QED


val _ = export_theory();
