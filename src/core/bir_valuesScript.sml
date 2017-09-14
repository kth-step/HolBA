open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory listTheory pred_setTheory;
open bir_auxiliaryTheory bir_immTheory;

val _ = new_theory "bir_values";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));

(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_val_t =
    BVal_Unknown
  | BVal_Imm bir_imm_t
  | BVal_Mem bir_immtype_t (*Addr-Type*) bir_immtype_t (* value-type *) (num -> num)
`;


val _ = Datatype `bir_type_t =
    BType_Imm bir_immtype_t
  | BType_Mem bir_immtype_t (* Addr-Type *) bir_immtype_t (* Value-Type *)
`;

val BType_Bool_def = Define `BType_Bool = BType_Imm Bit1`;


val bir_val_ss = rewrites (type_rws ``:bir_val_t``);
val bir_type_ss = rewrites (type_rws ``:bir_type_t``);


(* ------------------------------------------------------------------------- *)
(*  Checkers for Values                                                      *)
(* ------------------------------------------------------------------------- *)

val bir_val_is_Unknown_def = Define `bir_val_is_Unknown v = (v = BVal_Unknown)`;
val bir_val_is_Imm_def = Define `bir_val_is_Imm v = ?b. (v = BVal_Imm b)`;
val bir_val_is_Imm_s_def = Define `bir_val_is_Imm_s s v = ?n. (v = BVal_Imm (n2bs n s))`;
val bir_val_is_Bool_def = Define `bir_val_is_Bool = bir_val_is_Imm_s Bit1`;
val bir_val_is_Mem_def = Define `bir_val_is_Mem v = ?at vt mmap. (v = BVal_Mem at vt mmap)`;

val bir_val_checker_DEFS = save_thm ("bir_val_checker_DEFS", LIST_CONJ [
  bir_val_is_Unknown_def, bir_val_is_Imm_def, bir_val_is_Imm_s_def,
  bir_val_is_Bool_def, bir_val_is_Mem_def]);


val bir_val_is_Imm_s_ALT_DEF = store_thm ("bir_val_is_Imm_s_ALT_DEF",
``!s v. bir_val_is_Imm_s s v <=>
  (?b. (v = BVal_Imm b) /\ (type_of_bir_imm b = s))``,

Cases_on `v` >> (
  SIMP_TAC (std_ss ++ bir_val_ss) [bir_val_is_Imm_s_def,
    type_of_bir_imm_n2bs_INTRO]
));


val bir_val_checker_REWRS = store_thm ("bir_val_checker_REWRS",
  ``bir_val_is_Unknown BVal_Unknown /\
    (!b. ~bir_val_is_Unknown (BVal_Imm b)) /\
    (!at vt mmap. ~(bir_val_is_Unknown (BVal_Mem at vt mmap))) /\

    ~(bir_val_is_Imm BVal_Unknown) /\
    (!b. bir_val_is_Imm (BVal_Imm b)) /\
    (!at vt mmap. ~(bir_val_is_Imm (BVal_Mem at vt mmap))) /\

    ~(bir_val_is_Mem BVal_Unknown) /\
    (!b. ~(bir_val_is_Mem (BVal_Imm b))) /\
    (!at vt mmap. (bir_val_is_Mem (BVal_Mem at vt mmap))) /\

    (!s. ~(bir_val_is_Imm_s s BVal_Unknown)) /\
    (!s b. bir_val_is_Imm_s s (BVal_Imm b) <=> (type_of_bir_imm b = s)) /\
    (!s at vt mmap. ~(bir_val_is_Imm_s s (BVal_Mem at vt mmap))) /\

    (~(bir_val_is_Bool BVal_Unknown)) /\
    (!b. bir_val_is_Bool (BVal_Imm b) <=> (type_of_bir_imm b = Bit1)) /\
    (!at vt mmap. ~(bir_val_is_Bool (BVal_Mem at vt mmap)))``,


  REWRITE_TAC[bir_val_is_Imm_s_ALT_DEF, bir_val_is_Bool_def] >>
  SIMP_TAC (std_ss ++ bir_val_ss) [bir_val_checker_DEFS]);


val bir_val_is_Imm_s_IMPL = store_thm ("bir_val_is_Imm_s_IMPL",
  ``!s v. bir_val_is_Imm_s s v ==> bir_val_is_Imm v``,
SIMP_TAC (std_ss++bir_val_ss) [bir_val_is_Imm_def, bir_val_is_Imm_s_def,
  GSYM LEFT_FORALL_IMP_THM]);

val bir_val_is_Bool_IMPL = store_thm ("bir_val_is_Bool_IMPL",
  ``!v. bir_val_is_Bool v ==> bir_val_is_Imm v``,
SIMP_TAC (std_ss++bir_val_ss) [bir_val_is_Imm_def, bir_val_is_Bool_def,
  bir_val_is_Imm_s_def, GSYM LEFT_FORALL_IMP_THM]);



(* ------------------------------------------------------------------------- *)
(*  Boolean Values                                                           *)
(* ------------------------------------------------------------------------- *)

val bir_dest_bool_val_def = Define `
  (bir_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_dest_bool_val _ = NONE)`

val bir_dest_bool_val_EQ_SOME = store_thm ("bir_dest_bool_val_EQ_SOME",
  ``!v b. (bir_dest_bool_val v = SOME b) <=> (v = BVal_Imm (bool2b b))``,
Cases >> SIMP_TAC (std_ss++bir_val_ss) [bir_dest_bool_val_def] >>
rename1 `BVal_Imm i` >>
Cases_on `i` >> SIMP_TAC (std_ss++bir_imm_ss) [bir_dest_bool_val_def, bool2b_NEQ_IMM_ELIMS] >>
SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def] >>
Cases_on `b'` >> SIMP_TAC std_ss [bool2w_def] >>
METIS_TAC[word1_dichotomy, word1_distinct]);

val bir_dest_bool_val_EQ_NONE = store_thm ("bir_dest_bool_val_EQ_NONE",
  ``!v. (bir_dest_bool_val v = NONE) <=> ~(bir_val_is_Bool v)``,
Cases >> SIMP_TAC std_ss [bir_val_checker_REWRS, bir_dest_bool_val_def] >>
Cases_on `b` >> SIMP_TAC (std_ss++bir_imm_ss) [bir_val_checker_REWRS, bir_dest_bool_val_def,
  type_of_bir_imm_def]);

val bir_dest_bool_val_bool2b = store_thm ("bir_dest_bool_val_bool2b",
  ``bir_dest_bool_val (BVal_Imm (bool2b b)) = SOME b``,
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss) [
  bool2b_def, bool2w_def, bir_dest_bool_val_def]);

(* ------------------------------------------------------------------------- *)
(*  Some basic typing                                                        *)
(* ------------------------------------------------------------------------- *)

val type_of_bir_val_def = Define `
  (type_of_bir_val BVal_Unknown = NONE) /\
  (type_of_bir_val (BVal_Imm imm) = SOME (BType_Imm (type_of_bir_imm imm))) /\
  (type_of_bir_val (BVal_Mem at vt _) = SOME (BType_Mem at vt))`;

val bir_type_is_Imm_def = Define `bir_type_is_Imm ty = (?s. ty = BType_Imm s)`;
val bir_type_is_Imm_s_def = Define `bir_type_is_Imm_s s ty = (ty = BType_Imm s)`
val bir_type_is_Bool_def = Define `bir_type_is_Bool ty = (ty = BType_Imm Bit1)`
val bir_type_is_Mem_def = Define `bir_type_is_Mem ty = (?at vt. ty = BType_Mem at vt)`;

val bir_type_checker_DEFS = save_thm ("bir_type_checker_DEFS", LIST_CONJ [
  bir_type_is_Imm_def, bir_type_is_Imm_s_def,
  bir_type_is_Bool_def, bir_type_is_Mem_def]);


val bir_type_checker_REWRS = store_thm ("bir_type_checker_REWRS", ``
    (!b. bir_type_is_Imm (BType_Imm b)) /\
    (!at vt. ~(bir_type_is_Imm (BType_Mem at vt))) /\

    (!b. ~(bir_type_is_Mem (BType_Imm b))) /\
    (!at vt. (bir_type_is_Mem (BType_Mem at vt))) /\

    (!s b. bir_type_is_Imm_s s (BType_Imm b) <=> (b = s)) /\
    (!s at vt. ~(bir_type_is_Imm_s s (BType_Mem at vt))) /\

    (!b. bir_type_is_Bool BType_Bool <=> T) /\

    (!b. bir_type_is_Bool (BType_Imm b) <=> (b = Bit1)) /\
    (!at vt. ~(bir_type_is_Bool (BType_Mem at vt)))``,

  SIMP_TAC (std_ss ++ bir_type_ss) [bir_type_checker_DEFS, BType_Bool_def]);


val bir_type_is_Imm_s_IMPL = store_thm ("bir_type_is_Imm_s_IMPL",
  ``!s v. bir_type_is_Imm_s s v ==> bir_type_is_Imm v``,
SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def, bir_type_is_Imm_s_def]);


val bir_type_is_Bool_IMPL = store_thm ("bir_type_is_Bool_IMPL",
  ``!v. bir_type_is_Bool v ==> bir_type_is_Imm v``,
SIMP_TAC (std_ss++bir_type_ss) [bir_type_is_Imm_def, bir_type_is_Bool_def]);


val type_of_bir_val_EQ_ELIMS = store_thm ("type_of_bir_val_EQ_ELIMS",
  ``(!v. (type_of_bir_val v = NONE) <=> (v = BVal_Unknown)) /\
    (!v ty. (type_of_bir_val v = SOME (BType_Imm ty)) <=>
            (?i. (type_of_bir_imm i = ty) /\ (v = BVal_Imm i))) /\
    (!v aty vty. (type_of_bir_val v = SOME (BType_Mem aty vty)) <=>
            (?f. (v = BVal_Mem aty vty f)))``,
REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC (std_ss++bir_val_ss++bir_type_ss) [type_of_bir_val_def]
));


val bir_val_checker_TO_type_of = store_thm ("bir_val_checker_TO_type_of",
  ``(!v. (bir_val_is_Unknown v) <=> (type_of_bir_val v = NONE)) /\
    (!v ty. (bir_val_is_Imm_s ty v) <=> (type_of_bir_val v = SOME (BType_Imm ty))) /\
    (!v. (bir_val_is_Imm v) <=> (?ty. type_of_bir_val v = SOME (BType_Imm ty))) /\
    (!v. (bir_val_is_Bool v) <=> (type_of_bir_val v = SOME BType_Bool)) /\
    (!v. (bir_val_is_Mem v <=>
         (?aty vty. type_of_bir_val v = SOME (BType_Mem aty vty))))``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [type_of_bir_val_EQ_ELIMS, BType_Bool_def, bir_val_is_Bool_def,
  bir_val_is_Imm_s_ALT_DEF, bir_val_is_Imm_def, bir_val_is_Unknown_def,
  bir_val_is_Mem_def] >>
METIS_TAC[]);


(* ------------------------------------------------------------------------- *)
(*  Finiteness                                                               *)
(* ------------------------------------------------------------------------- *)

val bir_type_t_LIST_def = Define `bir_type_t_LIST =
  (MAP BType_Imm bir_immtype_t_LIST) ++
  (FLAT (MAP (\f. MAP f bir_immtype_t_LIST) (MAP BType_Mem bir_immtype_t_LIST)))`;

val bir_type_t_LIST_EVAL = save_thm ("bir_type_t_LIST_EVAL", EVAL ``bir_type_t_LIST``);

val bir_type_t_LIST_THM = store_thm ("bir_type_t_LIST_THM",
  ``!ty. MEM ty bir_type_t_LIST``,

SIMP_TAC list_ss [bir_type_t_LIST_def, MEM_MAP, MEM_FLAT, PULL_EXISTS,
  bir_immtype_t_LIST_THM] >>
Cases >> METIS_TAC[]);

val bir_type_t_UNIV_SPEC = store_thm ("bir_type_t_UNIV_SPEC",
  ``(UNIV:bir_type_t set) = set bir_type_t_LIST``,

SIMP_TAC list_ss [EXTENSION, bir_type_t_LIST_THM, IN_UNIV]);


val bir_type_t_FINITE_UNIV = store_thm ("bir_type_t_FINITE_UNIV",
  ``FINITE (UNIV : (bir_type_t set))``,
REWRITE_TAC[bir_type_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]);


(* ------------------------------------------------------------------------- *)
(*  Default value                                                            *)
(* ------------------------------------------------------------------------- *)

val bir_default_value_of_type_def = Define `
  (bir_default_value_of_type (BType_Imm s) = BVal_Imm (n2bs 0 s)) /\
  (bir_default_value_of_type (BType_Mem a_s v_s) = BVal_Mem a_s v_s (K 0))`;

val bir_default_value_of_type_SPEC = store_thm ("bir_default_value_of_type_SPEC",
  ``!ty. type_of_bir_val (bir_default_value_of_type ty) = SOME ty``,

Cases >> (
  SIMP_TAC std_ss [bir_default_value_of_type_def, type_of_bir_val_def, type_of_n2bs]
));


val _ = export_theory();
