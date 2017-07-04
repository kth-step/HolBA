(* ========================================================================= *)
(* FILE          : bil_valuesScript.sml                                      *)
(* DESCRIPTION   : A model of bil values and types                           *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory;

val _ = new_theory "bil_values";

val bil_imm_ss = rewrites ((type_rws ``:bil_imm_t``) @ (type_rws ``:bil_immtype_t``));

(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_val_t =
    BVal_Unknown
  | BVal_Imm bil_imm_t
  | BVal_Mem bil_immtype_t (*Addr-Type*) bil_immtype_t (* value-type *) (num -> num)
`;


val _ = Datatype `bil_type_t =
    BType_Imm bil_immtype_t
  | BType_Mem bil_immtype_t (* Addr-Type *) bil_immtype_t (* Value-Type *)
`;

val BoolType_def = Define `BoolType = BType_Imm Bit1`;


val bil_val_ss = rewrites (type_rws ``:bil_val_t``);
val bil_type_ss = rewrites (type_rws ``:bil_type_t``);


(* ------------------------------------------------------------------------- *)
(*  Checkers for Values                                                      *)
(* ------------------------------------------------------------------------- *)

val bil_val_is_Unknown_def = Define `bil_val_is_Unknown v = (v = BVal_Unknown)`;
val bil_val_is_Imm_def = Define `bil_val_is_Imm v = ?b. (v = BVal_Imm b)`;
val bil_val_is_Imm_s_def = Define `bil_val_is_Imm_s s v = ?n. (v = BVal_Imm (n2bs n s))`;
val bil_val_is_Bool_def = Define `bil_val_is_Bool = bil_val_is_Imm_s Bit1`;
val bil_val_is_Mem_def = Define `bil_val_is_Mem v = ?at vt mmap. (v = BVal_Mem at vt mmap)`;

val bil_val_checker_DEFS = save_thm ("bil_val_checker_DEFS", LIST_CONJ [
  bil_val_is_Unknown_def, bil_val_is_Imm_def, bil_val_is_Imm_s_def,
  bil_val_is_Bool_def, bil_val_is_Mem_def]);


val bil_val_is_Imm_s_ALT_DEF = store_thm ("bil_val_is_Imm_s_ALT_DEF",
``!s v. bil_val_is_Imm_s s v <=>
  (?b. (v = BVal_Imm b) /\ (type_of_bil_imm b = s))``,

Cases_on `v` >> (
  SIMP_TAC (std_ss ++ bil_val_ss) [bil_val_is_Imm_s_def,
    type_of_bil_imm_n2bs_INTRO]
));


val bil_val_checker_REWRS = store_thm ("bil_val_checker_REWRS",
  ``bil_val_is_Unknown BVal_Unknown /\
    (!b. ~bil_val_is_Unknown (BVal_Imm b)) /\
    (!at vt mmap. ~(bil_val_is_Unknown (BVal_Mem at vt mmap))) /\

    ~(bil_val_is_Imm BVal_Unknown) /\
    (!b. bil_val_is_Imm (BVal_Imm b)) /\
    (!at vt mmap. ~(bil_val_is_Imm (BVal_Mem at vt mmap))) /\

    ~(bil_val_is_Mem BVal_Unknown) /\
    (!b. ~(bil_val_is_Mem (BVal_Imm b))) /\
    (!at vt mmap. (bil_val_is_Mem (BVal_Mem at vt mmap))) /\

    (!s. ~(bil_val_is_Imm_s s BVal_Unknown)) /\
    (!s b. bil_val_is_Imm_s s (BVal_Imm b) <=> (type_of_bil_imm b = s)) /\
    (!s at vt mmap. ~(bil_val_is_Imm_s s (BVal_Mem at vt mmap))) /\

    (~(bil_val_is_Bool BVal_Unknown)) /\
    (!b. bil_val_is_Bool (BVal_Imm b) <=> (type_of_bil_imm b = Bit1)) /\
    (!at vt mmap. ~(bil_val_is_Bool (BVal_Mem at vt mmap)))``,


  REWRITE_TAC[bil_val_is_Imm_s_ALT_DEF, bil_val_is_Bool_def] >>
  SIMP_TAC (std_ss ++ bil_val_ss) [bil_val_checker_DEFS]);


val bil_val_is_Imm_s_IMPL = store_thm ("bil_val_is_Imm_s_IMPL",
  ``!s v. bil_val_is_Imm_s s v ==> bil_val_is_Imm v``,
SIMP_TAC (std_ss++bil_val_ss) [bil_val_is_Imm_def, bil_val_is_Imm_s_def,
  GSYM LEFT_FORALL_IMP_THM]);

val bil_val_is_Bool_IMPL = store_thm ("bil_val_is_Bool_IMPL",
  ``!v. bil_val_is_Bool v ==> bil_val_is_Imm v``,
SIMP_TAC (std_ss++bil_val_ss) [bil_val_is_Imm_def, bil_val_is_Bool_def,
  bil_val_is_Imm_s_def, GSYM LEFT_FORALL_IMP_THM]);



(* ------------------------------------------------------------------------- *)
(*  Some basic typing                                                        *)
(* ------------------------------------------------------------------------- *)

val type_of_bil_val_def = Define `
  (type_of_bil_val BVal_Unknown = NONE) /\
  (type_of_bil_val (BVal_Imm imm) = SOME (BType_Imm (type_of_bil_imm imm))) /\
  (type_of_bil_val (BVal_Mem at vt _) = SOME (BType_Mem at vt))`;

val bil_type_is_Imm_def = Define `bil_type_is_Imm ty = (?s. ty = BType_Imm s)`;
val bil_type_is_Imm_s_def = Define `bil_type_is_Imm_s s ty = (ty = BType_Imm s)`
val bil_type_is_Bool_def = Define `bil_type_is_Bool ty = (ty = BType_Imm Bit1)`
val bil_type_is_Mem_def = Define `bil_type_is_Mem ty = (?at vt. ty = BType_Mem at vt)`;

val bil_type_checker_DEFS = save_thm ("bil_type_checker_DEFS", LIST_CONJ [
  bil_type_is_Imm_def, bil_type_is_Imm_s_def,
  bil_type_is_Bool_def, bil_type_is_Mem_def]);


val bil_type_checker_REWRS = store_thm ("bil_type_checker_REWRS", ``
    (!b. bil_type_is_Imm (BType_Imm b)) /\
    (!at vt. ~(bil_type_is_Imm (BType_Mem at vt))) /\

    (!b. ~(bil_type_is_Mem (BType_Imm b))) /\
    (!at vt. (bil_type_is_Mem (BType_Mem at vt))) /\

    (!s b. bil_type_is_Imm_s s (BType_Imm b) <=> (b = s)) /\
    (!s at vt. ~(bil_type_is_Imm_s s (BType_Mem at vt))) /\

    (!b. bil_type_is_Bool BoolType <=> T) /\

    (!b. bil_type_is_Bool (BType_Imm b) <=> (b = Bit1)) /\
    (!at vt. ~(bil_type_is_Bool (BType_Mem at vt)))``,

  SIMP_TAC (std_ss ++ bil_type_ss) [bil_type_checker_DEFS, BoolType_def]);


val bil_type_is_Imm_s_IMPL = store_thm ("bil_type_is_Imm_s_IMPL",
  ``!s v. bil_type_is_Imm_s s v ==> bil_type_is_Imm v``,
SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_Imm_def, bil_type_is_Imm_s_def]);


val bil_type_is_Bool_IMPL = store_thm ("bil_type_is_Bool_IMPL",
  ``!v. bil_type_is_Bool v ==> bil_type_is_Imm v``,
SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_Imm_def, bil_type_is_Bool_def]);


val type_of_bil_val_EQ_ELIMS = store_thm ("type_of_bil_val_EQ_ELIMS",
  ``(!v. (type_of_bil_val v = NONE) <=> (v = BVal_Unknown)) /\
    (!v ty. (type_of_bil_val v = SOME (BType_Imm ty)) <=>
            (?i. (type_of_bil_imm i = ty) /\ (v = BVal_Imm i))) /\
    (!v aty vty. (type_of_bil_val v = SOME (BType_Mem aty vty)) <=>
            (?f. (v = BVal_Mem aty vty f)))``,
REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC (std_ss++bil_val_ss++bil_type_ss) [type_of_bil_val_def]
));


val _ = export_theory();
