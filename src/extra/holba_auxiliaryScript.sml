open HolKernel Parse boolLib bossLib;

open holba_auxiliaryLib;

open wordsTheory wordsLib;
open bitstringTheory ASCIInumbersTheory;
open pred_setTheory;
open listTheory;

val _ = new_theory "holba_auxiliary";

(* -------------------------------------------------------------------------- *)
(* List lemmata                                                               *)
(* -------------------------------------------------------------------------- *)

Theorem LAST_FILTER_EL:
  !P l. (FILTER P l <> []) ==> (
          (?i. (i < LENGTH l) /\ (LAST (FILTER P l) = EL i l) /\ P (EL i l) /\
               (!j. i < j /\ j < LENGTH l ==> ~(P (EL j l)))))
Proof
GEN_TAC >> Induct >- (
  SIMP_TAC list_ss []
) >>
SIMP_TAC list_ss [] >>
CONV_TAC (RENAME_VARS_CONV ["e1"]) >>
REPEAT STRIP_TAC >>
Cases_on `FILTER P l = []` >| [
  Q.EXISTS_TAC `0` >>
  Cases_on `P e1` >> FULL_SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  `MEM (EL j (e1::l)) (FILTER P l)` suffices_by ASM_SIMP_TAC list_ss [] >>
  SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  ASM_SIMP_TAC list_ss [listTheory.MEM_EL] >>
  Q.EXISTS_TAC `PRE j` >>
  Cases_on `j` >> FULL_SIMP_TAC list_ss [],

  FULL_SIMP_TAC list_ss [] >>
  Q.EXISTS_TAC `SUC i` >>
  ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [listTheory.LAST_DEF] >>
  REPEAT STRIP_TAC >>
  Cases_on `j` >> FULL_SIMP_TAC list_ss [] >>
  METIS_TAC[]
]
QED


Theorem LENGTH_LASTN_LE:
  !n l. LENGTH (LASTN n l) <= LENGTH l
Proof
SIMP_TAC list_ss [rich_listTheory.LASTN_def,
  listTheory.LENGTH_TAKE_EQ]
QED


Theorem dropWhile_MAP:
  !P f l. dropWhile P (MAP f l) =
            MAP f (dropWhile (P o f) l)
Proof
GEN_TAC >> GEN_TAC >>
Induct >> ASM_SIMP_TAC list_ss [] >>
GEN_TAC >> COND_CASES_TAC >> (
  SIMP_TAC list_ss []
)
QED

Theorem DROP_GENLIST:
  !n (f:num->'a) m.
      DROP n (GENLIST f m) =
      GENLIST (\n'. (f (n' + n))) (m - n)
Proof
Induct >- (
  SIMP_TAC (list_ss++boolSimps.ETA_ss) []
) >>
GEN_TAC >> Cases >- (
  SIMP_TAC list_ss []
) >>
ASM_SIMP_TAC list_ss [listTheory.GENLIST_CONS, arithmeticTheory.ADD_CLAUSES]
QED


Theorem ALL_DISTINCT_MAP_FILTER:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
GEN_TAC >> GEN_TAC >>
Induct >> ASM_SIMP_TAC list_ss [] >>

REPEAT STRIP_TAC >>
rename1 `f x` >>
Cases_on `P x` >- (
  FULL_SIMP_TAC list_ss [listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  METIS_TAC[]
) >>
ASM_SIMP_TAC list_ss []
QED



Theorem INDEX_FIND_EQ_NONE:
  !l i P. INDEX_FIND i P l = NONE <=> ~EXISTS P l
Proof
Induct >> (gs[listTheory.INDEX_FIND_def])
QED


Theorem INDEX_FIND_EQ_SOME:
  !l i P j e. (INDEX_FIND i P l = SOME (j, e)) <=> (
       (i <= j) /\ (j - i < LENGTH l) /\
       (EL (j - i) l = e) /\ P e /\
       (!j'. (i <= j' /\ j' < j) ==> ~(P (EL (j' - i) l))))
Proof
Induct >> SIMP_TAC list_ss [listTheory.INDEX_FIND_def] >>
REPEAT GEN_TAC >> COND_CASES_TAC >| [
  SIMP_TAC list_ss [] >>
  EQ_TAC >| [
    SIMP_TAC list_ss [] >>
    PROVE_TAC[],

    STRIP_TAC >>
    Cases_on `i < j` >| [
      `~(P (EL (i - i) (h :: l)))` by METIS_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      FULL_SIMP_TAC list_ss [],

      `i = j` by DECIDE_TAC >>
      FULL_SIMP_TAC list_ss []
    ]
  ],

  ONCE_ASM_REWRITE_TAC[] >>
  EQ_TAC >> STRIP_TAC >> ASM_SIMP_TAC list_ss [] >| [
     REPEAT STRIP_TAC >- (
       `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
       ASM_SIMP_TAC list_ss []
     ) >>
     Cases_on `i = j'` >- (
       FULL_SIMP_TAC list_ss []
     ) >>
     Q.PAT_X_ASSUM `!j'. _ ==> ~(P _)` (MP_TAC o Q.SPEC `j'`) >>
     `j' - i = SUC (j' - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss [],


     Cases_on `i = j` >- (
       FULL_SIMP_TAC list_ss []
     ) >>
     `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss [] >>
     REPEAT STRIP_TAC >>
     Q.PAT_X_ASSUM `!j'. _ ==> ~(P _)` (MP_TAC o Q.SPEC `j'`) >>
     `j' - i = SUC (j' - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss []
  ]
]
QED


Theorem INDEX_FIND_EQ_SOME_0:
  !l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))
Proof
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [INDEX_FIND_EQ_SOME] >>
Cases_on `LENGTH l` >> SIMP_TAC std_ss []
QED


Theorem INDEX_FIND_INDEX_CHANGE:
  !i P l. INDEX_FIND i P l = OPTION_MAP (\ (j, v). (j+i, v)) (INDEX_FIND 0 P l)
Proof
REPEAT GEN_TAC >>
Q.ID_SPEC_TAC `i` >>
Induct_on `l` >> SIMP_TAC std_ss [listTheory.INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
rename1 `P x` >>
ONCE_ASM_REWRITE_TAC[] >>
POP_ASSUM (K ALL_TAC) >>
Cases_on `P x` >> (
  ASM_SIMP_TAC std_ss []
) >>
Cases_on `INDEX_FIND 0 P l` >> (
  ASM_SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) []
)
QED


Theorem INDEX_FIND_PRE:
  !i j P l x.
    (0 < i) ==>
    (INDEX_FIND i       P l = SOME (j, x)) ==>
    (INDEX_FIND (PRE i) P l = SOME (PRE j, x))
Proof
Induct_on `l` >- (
  FULL_SIMP_TAC std_ss [listTheory.INDEX_FIND_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [listTheory.INDEX_FIND_def] >>
Cases_on `P h` >> (
  FULL_SIMP_TAC std_ss []
) >>
PAT_X_ASSUM ``!i j P x. _``
            (fn thm => ASSUME_TAC (SPEC ``(SUC i):num`` thm)) >>
REV_FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``!j' P' x'. _`` (fn thm => IMP_RES_TAC thm) >>
REV_FULL_SIMP_TAC std_ss [arithmeticTheory.SUC_PRE]
QED


Theorem SEG_SUC_LENGTH:
  !l n m. (n + m < LENGTH l) ==>
          (SEG (SUC n) m l = (EL m l)::SEG n (SUC m) l)
Proof
SIMP_TAC arith_ss [rich_listTheory.SEG_TAKE_DROP] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC list_ss [rich_listTheory.DROP_EL_CONS, arithmeticTheory.ADD1]
QED

Theorem INDEX_FIND_SUFFIX:
!P n i x_list x.
i < n ==>
INDEX_FIND 0 P x_list = SOME (PRE n, x) ==>
INDEX_FIND 0 P (DROP i x_list) = SOME (PRE (n - i), x)
Proof
rpt strip_tac >>
fs [INDEX_FIND_EQ_SOME_0] >>
rpt strip_tac >| [
 subgoal `EL (PRE (n - i)) (DROP i x_list) = EL ((PRE (n - i)) + i) x_list` >- (
  irule listTheory.EL_DROP >>
  fs []
 ) >>
 fs [] >>
 `i + PRE (n - i) = PRE n` suffices_by (
  rpt strip_tac >>
  fs []
 ) >>
 fs [],

 subgoal `j' + i < PRE n` >- (
  fs [arithmeticTheory.LESS_MONO_ADD_EQ]
 ) >>
 Q.SUBGOAL_THEN `EL j' (DROP i x_list) = EL (j' + i) x_list` (fn thm => fs [thm]) >- (
  irule listTheory.EL_DROP >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!j'. j' < PRE n ==> ~P (EL j' x_list)`` [`i + j'`] >>
 fs []
]
QED



(* -------------------------------------------------------------------------- *)
(* pred_set lemmata                                                           *)
(* -------------------------------------------------------------------------- *)

Theorem INFINITE_SUBSET_WITH_CARD_EXISTS:
  !s. INFINITE s ==> (!c. ?t. FINITE t /\ (CARD t = c) /\ t SUBSET s)
Proof
REPEAT STRIP_TAC >>
Induct_on `c` >- (
  Q.EXISTS_TAC `{}` >>
  ASM_SIMP_TAC std_ss [FINITE_EMPTY, CARD_EMPTY, EMPTY_SUBSET]
) >>
FULL_SIMP_TAC std_ss [] >>
`?e. e IN (s DIFF t)` by METIS_TAC[MEMBER_NOT_EMPTY, INFINITE_DIFF_FINITE] >>
Q.EXISTS_TAC `e INSERT t` >>
FULL_SIMP_TAC std_ss [IN_DIFF, FINITE_INSERT, INSERT_SUBSET,
  CARD_INSERT]
QED


Theorem IN_UNION_ABSORB_thm:
  ! l ls. (l IN ls) ==> (({l} UNION ls) = ls)
Proof
METIS_TAC [ABSORPTION,
           GSYM INSERT_SING_UNION]
QED


Theorem SINGLETONS_UNION_thm:
  ! l e. ({l} UNION {e}) = {l;e}
Proof
METIS_TAC [INSERT_SING_UNION]
QED


Theorem INTER_SUBSET_EMPTY_thm:
  !s t v.
    s SUBSET t ==>
    (v INTER t = EMPTY) ==>
    (v INTER s = EMPTY)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.INTER_DEF, pred_setTheory.EMPTY_DEF, FUN_EQ_THM]  >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >>
METIS_TAC []
QED

Theorem SUBSET_EQ_UNION_thm:
  !s t.
    s SUBSET t ==>
    (? v. t = s UNION v)
Proof
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `t` >>
METIS_TAC [pred_setTheory.SUBSET_UNION_ABSORPTION]
QED

Theorem IN_NOT_IN_NEQ_thm:
  !x y z.
    x IN z ==>
    ~(y IN z) ==>
    (x <> y)
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
QED

Theorem SING_DISJOINT_SING_NOT_IN_thm:
  !x y.
    (x INTER {y} = EMPTY) ==>
    ~(y IN x)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss)
  [pred_setTheory.INTER_DEF] >>
FULL_SIMP_TAC std_ss [pred_setTheory.EMPTY_DEF] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
QSPECL_X_ASSUM ``!x.P`` [`y`] >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
QED

Theorem INTER_EMPTY_IN_NOT_IN_thm:
  !x y z.
    (x INTER y = EMPTY) ==>
    z IN x ==>
    ~(z IN y)
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss)
  [pred_setTheory.INTER_DEF] >>
FULL_SIMP_TAC std_ss [pred_setTheory.EMPTY_DEF] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
QSPECL_X_ASSUM ``!x.P`` [`z`] >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) [] >>
METIS_TAC []
QED

Theorem INTER_EMPTY_INTER_INTER_EMPTY_thm:
  !x y z.
    (x INTER y = EMPTY) ==>
    (x INTER (y INTER z) = EMPTY)
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [Once pred_setTheory.INTER_ASSOC] >>
FULL_SIMP_TAC std_ss [] >>
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_AC_ss++pred_setSimps.PRED_SET_ss) []
QED

Theorem UNION_INSERT:
  !x s t. t UNION (x INSERT s) = if x IN t then t UNION s else (x INSERT t) UNION s
Proof
METIS_TAC [
  pred_setTheory.INSERT_UNION,
  pred_setTheory.UNION_COMM,
  pred_setTheory.INSERT_UNION_EQ
]
QED

Theorem BIGUNION_IMAGE_BIGUNION_thm:
  !s.
  BIGUNION (IMAGE BIGUNION s) = BIGUNION (BIGUNION s)
Proof
  gen_tac >>
  rewrite_tac [BIGUNION_IMAGE] >>
  fs [BIGUNION, EXTENSION] >>
  metis_tac []
QED

(* -------------------------------------------------------------------------- *)
(* lat_setlist (flat to set) computation helper                               *)
(* -------------------------------------------------------------------------- *)

Definition flat_setlist_def:
  flat_setlist l <=>
  FOLDL (\acc x. x UNION acc) EMPTY l
End

Theorem flat_setlist_thm:
  !l.
  flat_setlist l = BIGUNION (set l)
Proof
  GEN_TAC >>
  REWRITE_TAC [flat_setlist_def] >>
  REWRITE_TAC [(REWRITE_RULE [combinTheory.I_THM] o CONV_RULE (LAND_CONV (REWRITE_CONV [Once UNION_COMM])) o Q.SPECL [‘I’, ‘l’, ‘EMPTY’] o INST_TYPE [alpha |-> ``:'b -> bool``]) FOLDL_UNION_BIGUNION] >>
  fs []
QED

Theorem flat_setlist_thm2:
  flat_setlist = BIGUNION o set
Proof
  fs [FUN_EQ_THM, flat_setlist_thm]
QED

(* -------------------------------------------------------------------------- *)
(* Arithmetic                                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem MOD_ADD_EQ_SUB:
  !x1 x2 y. x1 < y /\ x2 < y /\ (y <= x1 + x2) ==>
            ((x1 + x2) MOD y = (x1 + x2) - y)
Proof
REPEAT STRIP_TAC >>
`?i. x1 + x2 = y + i` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MODULUS]
QED

Theorem NUM_LSONE_EQZ:
  !(n:num). (n < 1) <=> (n = 0)
Proof
FULL_SIMP_TAC arith_ss []
QED

Theorem NUM_PRE_LT:
  !(a:num). (a > 0) ==> PRE a < a
Proof
FULL_SIMP_TAC arith_ss []
QED

(* -------------------------------------------------------------------------- *)
(* While lemmata                                                              *)
(* -------------------------------------------------------------------------- *)

Theorem LEAST_SUC:
  !P. ~(P 0) /\ (?i. P i) ==> ((LEAST i. P i) = SUC (LEAST i. P (SUC i)))
Proof
REPEAT STRIP_TAC >>
`?i'. i = SUC i'` by (
  Cases_on `i` >> FULL_SIMP_TAC arith_ss []
) >>
BasicProvers.VAR_EQ_TAC >>
DEEP_INTRO_TAC whileTheory.LEAST_ELIM >>
REPEAT STRIP_TAC >- METIS_TAC[] >>
DEEP_INTRO_TAC whileTheory.LEAST_ELIM >>
REPEAT STRIP_TAC >- METIS_TAC[] >>
rename1 `n1' = SUC n2` >>
`?n1. n1' = SUC n1` by (
  Cases_on `n1'` >> FULL_SIMP_TAC arith_ss []
) >>
BasicProvers.VAR_EQ_TAC >>

`~(SUC n2 < SUC n1)` by METIS_TAC[] >>
`~(n1 < n2)` by METIS_TAC[] >>
DECIDE_TAC
QED

Theorem MEM_OLEAST:
 !l x.
 MEM x l ==>
 ?i. (OLEAST i. oEL i l = SOME x) = SOME i
Proof
Induct >> (
 fs [listTheory.MEM, listTheory.LENGTH]
) >>
rpt strip_tac >| [
 qexists_tac `0` >>
 fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM],

 qpat_assum `!x. _` (fn thm => imp_res_tac thm) >>
 Cases_on `h = x` >- (
  qexists_tac `0` >>
  fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM]
 ) >>
 qexists_tac `SUC i` >>
 fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM] >>
 rpt strip_tac >>
 Cases_on `i'` >- (
  fs []
 ) >>
 QSPECL_X_ASSUM ``!i'. _`` [`n`] >>
 gs []
]
QED

Theorem FILTER_HD_OLEAST:
 !P l l'.
 FILTER P l = l' ==>
 LENGTH l' > 0 ==>
 ?i. (OLEAST i. oEL i l = SOME (HD l')) = SOME i
Proof
rpt strip_tac >>
subgoal `MEM (HD l') l'` >- (
 Cases_on `l'` >> (
  fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
 )
) >>
subgoal `MEM (HD l') l` >- (
 metis_tac [listTheory.MEM_FILTER]
) >>
imp_res_tac MEM_OLEAST >>
qexists_tac `i` >>
fs []
QED


(* -------------------------------------------------------------------------- *)
(* Optional Minimum                                                           *)
(* -------------------------------------------------------------------------- *)

Definition OPT_NUM_MIN_def:
  (OPT_NUM_MIN NONE no2 = no2) /\
   (OPT_NUM_MIN no1 NONE = no1) /\
   (OPT_NUM_MIN (SOME n1) (SOME n2) = SOME (MIN n1 n2))
End


Theorem OPT_NUM_MIN_REWRS:
  (!no. (OPT_NUM_MIN NONE no = no)) /\
   (!no. (OPT_NUM_MIN no NONE = no)) /\
   (!n1 n2. (OPT_NUM_MIN (SOME n1) (SOME n2) = SOME (MIN n1 n2)))
Proof
REPEAT CONJ_TAC >> REPEAT Cases >>
SIMP_TAC std_ss [OPT_NUM_MIN_def]
QED


Theorem OPT_NUM_MIN_COMM:
  !no1 no2. (OPT_NUM_MIN no1 no2 = OPT_NUM_MIN no2 no1)
Proof
Cases >> Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
METIS_TAC[arithmeticTheory.MIN_COMM]
QED


Theorem OPT_NUM_MIN_ASSOC:
  !no1 no2 no3. (OPT_NUM_MIN no1 (OPT_NUM_MIN no2 no3)) = OPT_NUM_MIN (OPT_NUM_MIN no1 no2) no3
Proof
Cases >> Cases >> Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
METIS_TAC[arithmeticTheory.MIN_ASSOC]
QED


Theorem OPT_NUM_MIN_SOME0:
  (!no. (OPT_NUM_MIN no (SOME 0)) = SOME 0) /\
  (!no. (OPT_NUM_MIN (SOME 0) no) = SOME 0)
Proof
REPEAT CONJ_TAC >> (
  Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS]
)
QED


Theorem OPT_NUM_MIN_CASES:
  !no1 no2. (OPT_NUM_MIN no1 no2 = no1) \/
            (OPT_NUM_MIN no1 no2 = no2)
Proof
REPEAT Cases >>
SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, arithmeticTheory.MIN_DEF] >>
METIS_TAC[]
QED



Definition OPT_NUM_PRE_def:
  OPT_NUM_PRE = OPTION_MAP PRE
End
Definition OPT_NUM_SUC_def:
  OPT_NUM_SUC = OPTION_MAP SUC
End

Theorem OPT_NUM_PRE_SUC:
  !no. OPT_NUM_PRE (OPT_NUM_SUC no) = no
Proof
Cases >> SIMP_TAC std_ss [OPT_NUM_PRE_def, OPT_NUM_SUC_def]
QED


Theorem OPT_NUM_MIN_SOME_SUC_aux[local]:
  (!no n. (OPT_NUM_MIN no (SOME (SUC n))) = if (no = SOME 0) then SOME 0 else
     SOME (SUC (THE (OPT_NUM_MIN (OPT_NUM_PRE no) (SOME n)))))
Proof
Cases >> (
  SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, arithmeticTheory.MIN_DEF, OPT_NUM_PRE_def]
) >>
GEN_TAC >>
rename1 `x < SUC n` >>
Cases_on `x` >> SIMP_TAC arith_ss []
QED


Theorem OPT_NUM_MIN_SOME_SUC = CONJ OPT_NUM_MIN_SOME_SUC_aux
       (ONCE_REWRITE_RULE [OPT_NUM_MIN_COMM] OPT_NUM_MIN_SOME_SUC_aux)



Theorem OPT_NUM_MIN_OPT_NUM_SUC_aux[local]:
  (!no1 no2. (OPT_NUM_MIN no1 (OPT_NUM_SUC no2)) = if (no1 = SOME 0) then SOME 0 else
     OPT_NUM_SUC (OPT_NUM_MIN (OPT_NUM_PRE no1) no2))
Proof
Cases_on `no2` >- (
  Cases_on `no1` >> (
    SIMP_TAC std_ss [OPT_NUM_SUC_def, OPT_NUM_PRE_def, OPT_NUM_MIN_REWRS]
  ) >>
  rename1 `SOME n  = _` >> Cases_on `n` >> SIMP_TAC arith_ss []
) >>
SIMP_TAC std_ss [OPT_NUM_SUC_def, OPT_NUM_MIN_SOME_SUC] >>
Cases_on `no1` >> (
   SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, OPT_NUM_PRE_def, OPT_NUM_SUC_def]
)
QED

Theorem OPT_NUM_MIN_OPT_NUM_SUC = CONJ OPT_NUM_MIN_OPT_NUM_SUC_aux
       (ONCE_REWRITE_RULE [OPT_NUM_MIN_COMM] OPT_NUM_MIN_OPT_NUM_SUC_aux)


Definition OPT_CONS_def:
  OPT_CONS eo l = option_CASE eo l (\e. CONS e l)
End

Theorem OPT_CONS_REWRS:
  (!l. OPT_CONS NONE l = l) /\
    (!e l. OPT_CONS (SOME e) l = e::l)
Proof
SIMP_TAC std_ss [OPT_CONS_def]
QED


Theorem OPT_CONS_APPEND:
  !eo l1 l2. (OPT_CONS eo l1) ++ l2 =
      OPT_CONS eo (l1 ++ l2)
Proof
Cases >> SIMP_TAC list_ss [OPT_CONS_REWRS]
QED


Theorem OPT_CONS_REVERSE:
  !eo l. REVERSE (OPT_CONS eo l) = REVERSE l ++ OPT_CONS eo []
Proof
Cases >> SIMP_TAC list_ss [OPT_CONS_REWRS]
QED


(*******************)
(*   FUNPOW_OPT    *)
(*******************)
(* TODO: How about renaming this to oFUNPOW? Similar to oEL, OLEAST, ... *)

Definition FUNPOW_OPT_def:
  FUNPOW_OPT (r : 'a -> 'a option) n x =
  FUNPOW (\x. option_CASE x NONE r) n (SOME x)
End

Theorem FUNPOW_OPT_REWRS:
  (!r x. (FUNPOW_OPT r 0 x = SOME x)) /\
  (!r x n. (FUNPOW_OPT r (SUC n) x =
            case r x of NONE => NONE
                      | SOME x' => FUNPOW_OPT r n x'))
Proof
SIMP_TAC std_ss [FUNPOW_OPT_def, arithmeticTheory.FUNPOW] >>
REPEAT STRIP_TAC >>
Cases_on `r x` >> SIMP_TAC std_ss [] >>
Induct_on `n` >> (
  ASM_SIMP_TAC std_ss [arithmeticTheory.FUNPOW]
)
QED

Theorem FUNPOW_OPT_compute = CONV_RULE (numLib.SUC_TO_NUMERAL_DEFN_CONV) FUNPOW_OPT_REWRS


Theorem FUNPOW_OPT_ADD_thm:
  !f n n' ms ms' ms''.
    (FUNPOW_OPT f n ms = SOME ms') ==>
    (FUNPOW_OPT f n' ms' = SOME ms'') ==> 
    (FUNPOW_OPT f (n'+n) ms = SOME ms'')
Proof
METIS_TAC [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_OPT_next_1_NONE:
  !step_fun n s.
    (FUNPOW_OPT step_fun n s = NONE) ==>
    (FUNPOW_OPT step_fun (SUC n) s = NONE)
Proof
Induct_on `n` >| [
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS],

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS] >>
  Cases_on `step_fun s` >| [
    FULL_SIMP_TAC std_ss [],

    FULL_SIMP_TAC std_ss []
  ]
]
QED

Theorem FUNPOW_OPT_next_n_NONE:
  !step_fun n n' s.
   (FUNPOW_OPT step_fun n s = NONE) ==>
   (FUNPOW_OPT step_fun (n + n') s = NONE)
Proof
Induct_on `n'` >| [
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [FUNPOW_OPT_REWRS],

  REPEAT STRIP_TAC >>
  QSPECL_X_ASSUM ``!step_fun n s. _`` [`step_fun`, `SUC n`, `s`] >>
  IMP_RES_TAC FUNPOW_OPT_next_1_NONE >>
  FULL_SIMP_TAC arith_ss [arithmeticTheory.ADD_CLAUSES]
]
QED

Theorem FUNPOW_OPT_prev_EXISTS:
  !step_fun n n' s s'.
   n > 0 ==>
   (FUNPOW_OPT step_fun n s = SOME s') ==>
   n' < n ==>
   ?s''.
   (FUNPOW_OPT step_fun n' s = SOME s'')
Proof
REPEAT STRIP_TAC >>
Cases_on `FUNPOW_OPT step_fun n' s` >| [
  subgoal `?n''. n = n' + n''` >- (
    `n' <= n` by FULL_SIMP_TAC arith_ss [] >>
    METIS_TAC [arithmeticTheory.LESS_EQ_EXISTS]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC FUNPOW_OPT_next_n_NONE >>
  QSPECL_X_ASSUM ``!n''. _`` [`n''`] >>
  FULL_SIMP_TAC std_ss [],

  METIS_TAC []
]
QED

Theorem FUNPOW_ASSOC:
 !f m n x.
 FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
Proof
fs [GSYM arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_OPT_step:
 !f n x x' x''.
 FUNPOW_OPT f (SUC n) x = SOME x'' ==>
 f x = SOME x' ==>
 FUNPOW_OPT f n x' = SOME x''
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_REWRS]
QED

Theorem FUNPOW_OPT_PRE:
 !f n x x' x''.
 n > 0 ==>
 FUNPOW_OPT f n x = SOME x' ==>
 f x = SOME x'' ==>
 FUNPOW_OPT f (PRE n) x'' = SOME x'
Proof
rpt strip_tac >>
Cases_on `n` >> (
 fs [FUNPOW_OPT_REWRS]
)
QED

(* TODO: Use FUNPOW_OPT_next_n_NONE instead of this *)
Theorem FUNPOW_OPT_ADD_NONE:
 !f n n' ms ms'.
 FUNPOW_OPT f n ms = SOME ms' ==>
 FUNPOW_OPT f n' ms' = NONE ==> 
 FUNPOW_OPT f (n'+n) ms = NONE
Proof
metis_tac [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_OPT_INTER:
 !f n n' ms ms' ms''.
 FUNPOW_OPT f n ms = SOME ms' ==>
 FUNPOW_OPT f (n'+n) ms = SOME ms'' ==>
 FUNPOW_OPT f n' ms' = SOME ms''
Proof
metis_tac [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_SUB:
 !f m n x.
 m > n ==>
 FUNPOW f (m - n) (FUNPOW f n x) = FUNPOW f m x
Proof
fs [GSYM arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_OPT_split:
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n - n') s = SOME s'' ==>
FUNPOW_OPT f n' s'' = SOME s'
Proof
rpt strip_tac >>
irule FUNPOW_OPT_INTER >>
qexistsl_tac [`s`, `n - n'`] >>
fs []
QED

Theorem FUNPOW_OPT_split2:
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f n' s = SOME s'' ==>
FUNPOW_OPT f (n - n') s'' = SOME s'
Proof
rpt strip_tac >>
metis_tac [FUNPOW_SUB, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
QED

(* TODO: Relax the first OLEAST? *)
Theorem FUNPOW_OPT_cycle:
 !f s s' n n'.
 (OLEAST n. n > 0 /\ FUNPOW_OPT f n s = SOME s) = SOME n ==>
 s <> s' ==>
 (OLEAST n'. FUNPOW_OPT f n' s = SOME s') = SOME n' ==>
 n' < n
Proof
rpt strip_tac >>
CCONTR_TAC >>
Cases_on `n' = n` >- (
 fs [whileTheory.OLEAST_EQ_SOME]
) >>
subgoal `n' > n` >- (
 gs []
) >>
subgoal `FUNPOW_OPT f (n' - n) s = SOME s'` >- (
 irule FUNPOW_OPT_split2 >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `s` >>
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT f n'' s <> SOME s'`` [`n' - n`] >>
gs []
QED


(* -------------------------------------------------------------------------- *)
(* lazy lists                                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem LGENLIST_UNFOLD_NONE:
  !f. LGENLIST f NONE = (f 0) ::: (LGENLIST (f o SUC) NONE)
Proof
SIMP_TAC arith_ss [llistTheory.LGENLIST_EQ_CONS,
  combinTheory.o_DEF, GSYM arithmeticTheory.ADD1]
QED


Theorem LGENLIST_UNFOLD_NEQ_SOME0:
  !no f. (no <> SOME 0) ==> (LGENLIST f no = (f 0) ::: (LGENLIST (f o SUC) (OPT_NUM_PRE no)))
Proof
Cases >- (
  SIMP_TAC std_ss [OPT_NUM_PRE_def] >>
  METIS_TAC[LGENLIST_UNFOLD_NONE]
) >>
rename1 `SOME n <> SOME 0` >>
Cases_on `n` >- (
  SIMP_TAC std_ss []
) >>
rename1 `SOME (SUC n') <> SOME 0` >>
SIMP_TAC std_ss [llistTheory.LGENLIST_SOME, OPT_NUM_PRE_def]
QED


Definition OPT_LCONS_def:
  OPT_LCONS eo l = option_CASE eo l (\e. LCONS e l)
End

Theorem OPT_LCONS_REWRS:
  (!ll. OPT_LCONS NONE ll = ll) /\
    (!e ll. OPT_LCONS (SOME e) ll = e:::ll)
Proof
SIMP_TAC std_ss [OPT_LCONS_def]
QED


Theorem OPT_CONS_fromList:
  !eo l. fromList (OPT_CONS eo l) = OPT_LCONS eo (fromList l)
Proof
Cases >> SIMP_TAC std_ss [OPT_CONS_REWRS, OPT_LCONS_REWRS, llistTheory.fromList_def]
QED


Theorem LMAP_EQ_LNIL:
  !f ll. (LMAP f ll = LNIL) <=> (ll = LNIL)
Proof
Cases_on `ll` >> (
  SIMP_TAC std_ss [llistTheory.LMAP, llistTheory.LCONS_NOT_NIL]
)
QED


(* -------------------------------------------------------------------------- *)
(* Word lemmata                                                               *)
(* -------------------------------------------------------------------------- *)

Theorem w2w_n2w:
  !n. (w2w ((n2w n):'a word)):'b word = (n2w (n MOD dimword (:'a)))
Proof
SIMP_TAC std_ss [w2w_def, w2n_n2w]
QED

Theorem align_n2w:
  !n m. align n ((n2w m):'a word) =
        n2w ((m MOD dimword (:'a)) DIV 2 ** n * 2 ** n)
Proof
SIMP_TAC std_ss [alignmentTheory.align_w2n, w2n_n2w]
QED

Theorem w2n_MOD_2EXP_ID:
  !(w:'a word). (MOD_2EXP (dimindex (:'a)) (w2n w)) = w2n w
Proof
SIMP_TAC std_ss [GSYM wordsTheory.MOD_2EXP_DIMINDEX, wordsTheory.w2n_lt]
QED

Theorem word_extract_bits_w2w:
  !h l a. ((h >< l) (a:'a word)) = w2w ((h -- l) a)
Proof
SIMP_TAC std_ss [wordsTheory.word_extract_w2w_mask, wordsTheory.word_bits_mask]
QED

Theorem sw2sw_w2w_downcast:
  !w.
  (dimindex (:'b) <= dimindex (:'a)) ==> ((sw2sw (w : 'a word) : 'b word) = w2w w)
Proof
REPEAT STRIP_TAC >>
`(2**dimindex (:'b) <= 2**dimindex (:'a))` by METIS_TAC[bitTheory.TWOEXP_MONO2] >>
`(2**dimindex (:'b) - 2**dimindex (:'a)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [sw2sw_def,
  bitTheory.SIGN_EXTEND_def, LET_DEF, w2w_def,
  wordsTheory.w2n_lt, GSYM wordsTheory.dimword_def
]
QED


Theorem fixwidth_fixwidth_le:
  !v n m. n <= m ==> (fixwidth n (fixwidth m v) = fixwidth n v)
Proof
REPEAT STRIP_TAC >>
`LENGTH (fixwidth m v) = m` by SIMP_TAC std_ss [length_fixwidth] >>
FULL_SIMP_TAC list_ss [LET_DEF, fixwidth_def] >>
REPEAT COND_CASES_TAC >| [
  FULL_SIMP_TAC list_ss [zero_extend_def, listTheory.PAD_LEFT,
    rich_listTheory.DROP_APPEND1, DROP_GENLIST, combinTheory.K_DEF],

  FULL_SIMP_TAC list_ss [zero_extend_def, listTheory.PAD_LEFT,
    rich_listTheory.DROP_APPEND2],

  FULL_SIMP_TAC arith_ss [],

  ASM_SIMP_TAC arith_ss [rich_listTheory.DROP_DROP_T]
]
QED


Theorem w2v_word_join:
  FINITE univ(:'a) /\ FINITE univ(:'b) ==>
  !w1:'a word w2:'b word. w2v (word_join w1 w2) = (w2v w1 ++ w2v w2)
Proof
REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp,
  word_join_v2w, fcpTheory.index_sum]
QED


Theorem w2v_word_concat:
  FINITE univ(:'a) /\ FINITE univ(:'b) /\ (dimindex (:'c) = dimindex (:'a) + dimindex (:'b)) ==>
  !w1:'a word w2:'b word. w2v ((w1 @@ w2):'c word) = (w2v w1 ++ w2v w2)
Proof
REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp, word_concat_def,
  word_join_v2w, fcpTheory.index_sum, w2w_def, w2n_v2w, bitTheory.MOD_2EXP_def] >>
`v2n (v ++ v') < 2 ** (LENGTH v + LENGTH v')` by (
  METIS_TAC[bitstringTheory.v2n_lt, listTheory.LENGTH_APPEND]
) >>
ASM_SIMP_TAC list_ss [n2w_v2n, w2v_v2w, fixwidth_id_imp]
QED


val w2v_word_concat_SYM_REWRS = save_thm ("w2v_word_concat_SYM_REWRS",
let
  val words_sizes = [1,8,16,32,64]
  val max_ws = last words_sizes

  val thm_idx = LIST_CONJ (for 1 (max_ws+max_ws) (fn i => fcpLib.DIMINDEX (Arbnum.fromInt i)))
  val thm_fin = LIST_CONJ (for 1 max_ws (fn i => fcpLib.FINITE (Arbnum.fromInt i)))

  val rewr_tac = REWRITE_TAC [thm_fin, thm_idx];

  val thm0 = GSYM w2v_word_concat
  fun inst_w2v_word_concat n m = let
    val n_ty = fcpLib.index_type (Arbnum.fromInt n);
    val m_ty = fcpLib.index_type (Arbnum.fromInt m);
    val nm_ty = fcpLib.index_type (Arbnum.fromInt (n+m));

    val thm1a = INST_TYPE [``:'a`` |-> n_ty, ``:'b`` |-> m_ty, ``:'c`` |-> nm_ty] thm0
    val (pre, _) = dest_imp (concl(thm1a))
    val pre_thm = prove (pre, rewr_tac >> DECIDE_TAC)
    val thm1 = MP thm1a pre_thm
  in thm1 end

  fun words_sizes_combs_n s c = (if (c+s) <= max_ws then (s, c)::(c,s)::words_sizes_combs_n s (c+s) else [])
  val words_sizes_combs = flatten (map (fn n => words_sizes_combs_n n n) words_sizes)

  val thm1 = LIST_CONJ (map (fn (n, m) => inst_w2v_word_concat m n) words_sizes_combs)
in
  thm1
end)


Theorem word1_dichotomy:
  !v:word1. (v = 1w) \/ (v = 0w)
Proof
Cases >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.n2w_11] >>
DECIDE_TAC
QED

Theorem word1_distinct:
  (1w:word1) <> 0w
Proof
SIMP_TAC (std_ss++wordsLib.WORD_ss) []
QED

Theorem word1_neg:
  (~(0w:word1) = 1w) /\ (~(1w:word1) = 0w)
Proof
SIMP_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_BIT_EQ_ss) []
QED


Theorem BIT_ADD_WORD_CARRY:
  !w0:'a word (w1:'a word).
  BIT (dimindex (:'a)) (w2n w0 + w2n (w1)) <=>
  ~(w2n w0 + w2n w1 < dimword (:'a))
Proof
REPEAT GEN_TAC >>
EQ_TAC >> REPEAT STRIP_TAC >- (
  `dimword (:'a) <= w2n w0 + w2n w1` by METIS_TAC[bitTheory.BIT_IMP_GE_TWOEXP, dimword_def] >>
  DECIDE_TAC
) >>
`?m. (m < dimword (:'a)) /\ (w2n w0 + w2n w1 = m + dimword (:'a))` by (
  FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS] >>
  `?m. w2n w0 + w2n w1 = dimword (:'a) + m` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
  Q.EXISTS_TAC `m` >>
  `(w2n (w0:'a word) < dimword (:'a)) /\ (w2n (w1:'a word) < dimword (:'a))` by METIS_TAC[w2n_lt] >>
  ASM_SIMP_TAC arith_ss []
) >>

MP_TAC (SPECL [``dimindex (:'a)``, ``SUC (dimindex (:'a))``, ``m + dimword (:'a)``] bitTheory.EXISTS_BIT_IN_RANGE) >>
ASM_SIMP_TAC arith_ss [dimword_def, arithmeticTheory.EXP, GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
METIS_TAC[arithmeticTheory.LESS_EQUAL_ANTISYM]
QED



Theorem word_sub_n2w:
  !n m. (n2w n - n2w m):'a word = n2w (if m <= n then (n - m) else
            dimword (:'a) - (m - n) MOD dimword (:'a))
Proof
REPEAT GEN_TAC >>
Cases_on `m <= n` >- (
  ASM_SIMP_TAC std_ss [n2w_sub]
) >>
ASM_SIMP_TAC arith_ss [GSYM word_2comp_n2w, n2w_sub, WORD_NEG_SUB]
QED


Theorem WORD_SUB_RZERO_IFF:
  !(a : 'a word) b. ((a - b = a)) <=> (b = 0w)
Proof
REPEAT GEN_TAC >>
Tactical.REVERSE EQ_TAC >- (
  SIMP_TAC arith_ss [WORD_SUB_RZERO]
) >>
STRIP_TAC >>
`(-a) + (a - b) = (-a) + a` by METIS_TAC[wordsTheory.WORD_EQ_ADD_LCANCEL] >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) []
QED


Theorem WORD_LS_NOT:
  !w1 (w2:'a word). (~w1 <=+ ~w2) <=> (w2 <=+ w1)
Proof
REPEAT Cases >>
ASM_SIMP_TAC arith_ss [word_1comp_n2w, word_ls_n2w]
QED


Theorem aligned_neg:
  !p (a:'a word). aligned p (-a) <=> aligned p a
Proof
`!p (a:'a word). aligned p a ==> aligned p (-a)` suffices_by METIS_TAC[WORD_NEG_NEG] >>
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `(-a) = 0w - a` SUBST1_TAC >- SIMP_TAC (std_ss++wordsLib.WORD_ss) [] >>
ASM_SIMP_TAC std_ss [alignmentTheory.aligned_add_sub, alignmentTheory.aligned_0]
QED


Theorem align_aligned_add:
  !p (a:'a word) b. aligned p b ==>
                    ((align p (a + b) = ((align p a) + b)))
Proof
REPEAT STRIP_TAC >>
Cases_on `dimindex (:'a) <= p` >- (
  `b = 0w` by METIS_TAC [alignmentTheory.aligned_ge_dim]>>
  ASM_SIMP_TAC std_ss [wordsTheory.WORD_ADD_0]
) >>
FULL_SIMP_TAC std_ss [alignmentTheory.align_sub, alignmentTheory.aligned_def] >>
REPEAT GEN_TAC >>
Cases_on `p = 0` >> FULL_SIMP_TAC std_ss [] >>
ASM_SIMP_TAC arith_ss [Once (GSYM wordsTheory.WORD_EXTRACT_OVER_ADD2)] >>
FULL_SIMP_TAC arith_ss [WORD_SUB_RZERO_IFF, WORD_ADD_0, WORD_EXTRACT_COMP_THM,
  arithmeticTheory.MIN_DEF] >>
SIMP_TAC (std_ss++wordsLib.WORD_ss) []
QED


Theorem align_aligned_sub:
  !p (a:'a word) b. aligned p b ==>
                    ((align p (a - b) = ((align p a) - b)))
Proof
METIS_TAC[aligned_neg, word_sub_def, align_aligned_add]
QED


Theorem testbit_el_iff:
  !v i. testbit i v = ((i < LENGTH v) /\ EL (LENGTH v - 1 - i) v)
Proof
REPEAT GEN_TAC >>
Cases_on `i < LENGTH v` >> (
  ASM_SIMP_TAC arith_ss [testbit_el, testbit_geq_len]
)
QED

Theorem w2w_32_64:
 !(b1:word32). w2w ((w2w b1):word64) = b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11] >>
  IMP_RES_TAC (DECIDE ``n < 4294967296 ==> n < 18446744073709551616:num``) >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
QED

Theorem n2w_w2n_w2w_32_64:
 !(b1:word32). n2w ((w2n b1)) = (w2w:word32 -> word64) b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

Theorem w2w_n2w_w2n_64_32:
 !(b1:word64). (w2w:word64 -> word32) b1 = n2w ((w2n b1))
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

Theorem if_bool_1w:
 !b. ((if b then 1w else 0w) = 1w) = b
Proof
 rw []
QED

(* -------------------------------------------------------------------------- *)
(* Fresh variable names                                                       *)
(* -------------------------------------------------------------------------- *)

Definition FRESH_INDEXED_STRING_MK_def:
  FRESH_INDEXED_STRING_MK pre n =
  (pre ++ (num_to_dec_string n))
End

Theorem FRESH_INDEXED_STRING_MK_11:
  !pre n1 n2. (FRESH_INDEXED_STRING_MK pre n1 = FRESH_INDEXED_STRING_MK pre n2) <=> (n1 = n2)
Proof
SIMP_TAC list_ss [FRESH_INDEXED_STRING_MK_def, toString_11]
QED

Definition FRESH_INDEXED_STRING_AUX_def:
  FRESH_INDEXED_STRING_AUX pre n s = (LEAST x. (n <= x) /\ ~((FRESH_INDEXED_STRING_MK pre x) IN s))
End

Definition FRESH_INDEXED_STRING_def:
  FRESH_INDEXED_STRING pre n s = (FRESH_INDEXED_STRING_MK pre (FRESH_INDEXED_STRING_AUX pre n s))
End

Definition FRESH_INDEXED_STRINGS_def:
  (FRESH_INDEXED_STRINGS pre n s 0 = []) /\
  (FRESH_INDEXED_STRINGS pre n s (SUC m) =
   let ns = (FRESH_INDEXED_STRING_AUX pre n s) in
   let ss = FRESH_INDEXED_STRING_MK pre ns in
   (ss::FRESH_INDEXED_STRINGS pre (SUC ns) s m))
End


Theorem FRESH_INDEXED_STRING_AUX_PROPS[local]:
  !s pre n i.
  FINITE s ==>
  let i = FRESH_INDEXED_STRING_AUX pre n s in
  (n <= i) /\ ~(FRESH_INDEXED_STRING_MK pre i IN s) /\
  (!i'. (n <= i' /\ i' < i) ==> ((FRESH_INDEXED_STRING_MK pre i') IN s))
Proof
SIMP_TAC std_ss [LET_THM, FRESH_INDEXED_STRING_AUX_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
numLib.LEAST_ELIM_TAC >>
REPEAT STRIP_TAC >| [
  ALL_TAC,
  ASM_REWRITE_TAC[],
  METIS_TAC[]
] >>

Q.ABBREV_TAC `S0 = count n` >>
Q.ABBREV_TAC `S1 = (UNIV:num set) DIFF S0` >>
Q.ABBREV_TAC `S2 = (IMAGE (FRESH_INDEXED_STRING_MK pre) S1)` >>


`INFINITE S1` by METIS_TAC[FINITE_DIFF_down, FINITE_COUNT, INFINITE_NUM_UNIV] >>
`INFINITE S2` by METIS_TAC[FRESH_INDEXED_STRING_MK_11, IMAGE_11_INFINITE] >>

`?ns. ns IN S2 /\ ~(ns IN s)` by METIS_TAC[pred_setTheory.IN_INFINITE_NOT_FINITE] >>
UNABBREV_ALL_TAC >>
FULL_SIMP_TAC arith_ss [IN_IMAGE, IN_DIFF, IN_COUNT, IN_UNIV, arithmeticTheory.NOT_LESS] >>
METIS_TAC[]
QED



Theorem FRESH_INDEXED_STRING_NOT_IN:
  !s pre n. FINITE s ==> ~(FRESH_INDEXED_STRING pre n s IN s)
Proof
SIMP_TAC std_ss [FRESH_INDEXED_STRING_def] >>
METIS_TAC[FRESH_INDEXED_STRING_AUX_PROPS]
QED


Theorem FRESH_INDEXED_STRINGS_PROPS_INDICES:
  !s pre l n. FINITE s ==> (
       ?nl. (FRESH_INDEXED_STRINGS pre n s l = MAP (FRESH_INDEXED_STRING_MK pre) nl) /\
            (LENGTH nl = l) /\
            (ALL_DISTINCT nl) /\
            (EVERY ($<= n) nl) /\
            (EVERY (\n. ~((FRESH_INDEXED_STRING_MK pre n) IN s)) nl))
Proof
GEN_TAC >> GEN_TAC >>
Induct >> (
  SIMP_TAC list_ss [FRESH_INDEXED_STRINGS_def, LET_THM]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `n' = FRESH_INDEXED_STRING_AUX pre n s` >>
Q.PAT_X_ASSUM `!n. _` (STRIP_ASSUME_TAC o Q.SPEC `SUC n'`) >>
Q.EXISTS_TAC `n'::nl` >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM] >>
`n <= n' /\ ~(FRESH_INDEXED_STRING_MK pre n' IN s)` by METIS_TAC[FRESH_INDEXED_STRING_AUX_PROPS] >>
ASM_REWRITE_TAC[] >>
REPEAT STRIP_TAC >| [
  `SUC n' <= n'` by PROVE_TAC[] >>
  DECIDE_TAC,

  `SUC n' <= e` by PROVE_TAC[] >>
  DECIDE_TAC
]
QED


Theorem FRESH_INDEXED_STRINGS_PROPS:
  !s pre l n. FINITE s ==> (
      (LENGTH (FRESH_INDEXED_STRINGS pre n s l) = l) /\
      ALL_DISTINCT (FRESH_INDEXED_STRINGS pre n s l) /\
      (EVERY (\n. ~(n IN s)) (FRESH_INDEXED_STRINGS pre n s l)))
Proof
REPEAT GEN_TAC >>
ASSUME_TAC (Q.SPECL [`s`, `pre`, `l`, `n`] FRESH_INDEXED_STRINGS_PROPS_INDICES) >>
STRIP_TAC >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MAP] >>
MATCH_MP_TAC listTheory.ALL_DISTINCT_MAP_INJ >>
ASM_SIMP_TAC std_ss [FRESH_INDEXED_STRING_MK_11]
QED


(* -------------------------------------------------------------------------- *)
(* Miscellaneous                                                              *)
(* -------------------------------------------------------------------------- *)

Theorem noteq_trans_impl:
  !A B x.
    (A <> B) ==>
    (((x = A) /\ (x = B)) <=> F)
Proof
REPEAT STRIP_TAC >>
RW_TAC std_ss [] >>
CCONTR_TAC >>
FULL_SIMP_TAC std_ss [] >>
RW_TAC std_ss []
QED


(* -------------------------------------------------------------------------- *)
(* Helper to split up lists into its elements (for example for bir programs)  *)
(* -------------------------------------------------------------------------- *)

Definition SPLIT_ELs_def:
  (SPLIT_ELs _ []      _ = T) /\
  (SPLIT_ELs l (h::t)  i = ((EL i l = h) /\ (SPLIT_ELs l t (i + 1))))
End

Theorem SPLIT_ELs_GEN_thm:
!i h x t.
  SPLIT_ELs t x i =
  SPLIT_ELs (h::t) x (i + 1)
Proof
  Induct_on ‘x’ >> (
    gs [SPLIT_ELs_def]
  ) >>
  rpt strip_tac >>
  POP_ASSUM ((fn t => REWRITE_TAC [Once t]) o Q.SPECL [‘i+1’, ‘h'’, ‘t’]) >>
  gs [] >>
  REWRITE_TAC [GSYM arithmeticTheory.ADD1, listTheory.EL, listTheory.TL]
QED

Theorem SPLIT_ELs_0_thm:
!l. SPLIT_ELs l l 0
Proof
  Induct >> (
    gs [SPLIT_ELs_def]
  ) >>
  ASM_REWRITE_TAC [(GSYM o EVAL_RULE o Q.SPEC ‘0’) SPLIT_ELs_GEN_thm]
QED

val _ = export_theory();
