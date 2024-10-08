open HolKernel Parse boolLib bossLib;
open bir_immTheory bir_expTheory
open bir_nzcv_expTheory holba_auxiliaryTheory
open HolBACoreSimps
open bir_expTheory bir_typing_expTheory bir_valuesTheory
open wordsTheory

(* In BIR developments we need to deal with intervals of machine
   words. The most common case is reasoning about memory
   regions. This theory provides some infrastructure for machine word
   intervals as well as expressions checking various properties of
   such intervals (e.g. disjointness, being subsumed, membership,
   ... )
*)

val _ = new_theory "bir_interval_exp";


(*********************)
(* Basic Definitions *)
(*********************)

(* We can represent intervals by either a start value and an end value
   (start one inclusive, end one exclusive), or a start value and a
   length. Here we use the end value representation and provide a
   translation of the length representation into it.

   Since we are dealing with machine words, modulo arithmetic
   applies. for simplicity, we demand that the end value is not
   smaller than the start one. This implies that we prohibit
   wrap-arounds. *)

Datatype:
  word_interval_t = WI_end ('a word) ('a word)
End
val word_interval_11 = DB.fetch "-" "word_interval_t_11";

Definition WI_size_def:
  WI_size s sz = WI_end s (sz + s)
End

(* Well formed intervals have always the end larger than this start *)
Definition WI_wf_def:
  WI_wf (WI_end b e) <=> (b <=+ e)
End
Definition WI_MEM_def:
  WI_MEM w (WI_end b e) <=> (b <=+ w) /\ (w <+ e)
End


(*****************)
(* Basic Lemmata *)
(*****************)

Theorem WI_MEM_implies_wf:
  !w i. WI_MEM w i ==> WI_wf i
Proof
Cases_on `i` >> SIMP_TAC arith_ss [WI_MEM_def, WI_wf_def, WORD_LS, WORD_LO]
QED

Theorem WI_wf_size:
  !b sz. (WI_wf (WI_size (b:'a word) sz) <=> ~(nzcv_BIR_ADD_C b sz))
Proof
REPEAT Cases >>
ASM_SIMP_TAC arith_ss [WI_wf_def, WI_size_def, WORD_LS, word_add_n2w, w2n_n2w,
  nzcv_BIR_ADD_C_CARRY_DEF, awc_BIR_C_def, add_with_carry_def, LET_THM] >>
rename1 `(n1:num) + n2` >>
REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >> (
  ASM_SIMP_TAC arith_ss []
) >>
CCONTR_TAC >>
`?m. (m < dimword (:'a)) /\ (n1 + n2 = m + dimword (:'a))` by (
  FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS] >>
  `?m. (n1+n2) = dimword (:'a) + m` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
  Q.EXISTS_TAC `m` >>
  ASM_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC arith_ss [ZERO_LT_dimword, arithmeticTheory.ADD_MODULUS]
QED


Theorem WI_wf_size_compute:
  !b sz. (WI_wf (WI_size (b:'a word) sz) <=> (b <=+ ~sz))
Proof
SIMP_TAC std_ss [WI_wf_size, nzcv_BIR_ADD_NZCV_REWRS, WORD_NOT_LOWER]
QED


Theorem WI_wf_size_SUM_LT:
  !(b:'a word) sz.
    WI_wf (WI_size b sz) <=>
    w2n b + w2n sz < dimword (:'a)
Proof
SIMP_TAC std_ss [WI_wf_size, bir_nzcv_expTheory.nzcv_BIR_ADD_C_CARRY_DEF,
  bir_nzcv_expTheory.awc_BIR_C_def, add_with_carry_def, LET_THM, w2n_n2w] >>
REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC >- (
  POP_ASSUM (SUBST1_TAC o GSYM) >>
  SIMP_TAC arith_ss [ZERO_LT_dimword]
) >- (
  ASM_SIMP_TAC arith_ss []
)
QED


Theorem WI_size_INTRO:
  !s e. ((WI_end s e) = (WI_size s (e - s)))
Proof
SIMP_TAC std_ss [WI_size_def, WORD_SUB_ADD]
QED



(************************)
(* Enumerating elements *)
(************************)

Definition WI_ELEM_LIST_def:
  (WI_ELEM_LIST b 0 = []) /\
  (WI_ELEM_LIST b (SUC n) = b::(WI_ELEM_LIST (b+1w) n))
End

val WI_ELEM_LIST_compute = DB.fetch "-" "WI_ELEM_LIST_compute";


Theorem WI_MEM_WI_size:
  !sz b (w:'a word).
    WI_wf (WI_size b sz) ==> (
     (WI_MEM w (WI_size b sz)) <=>
      MEM w (WI_ELEM_LIST b (w2n sz)))
Proof
ASM_SIMP_TAC arith_ss [WI_wf_size] >>
REPEAT Cases >>
FULL_SIMP_TAC arith_ss [w2n_n2w, WI_size_def, WI_MEM_def, WORD_LO,
  word_add_n2w, WORD_LS, nzcv_BIR_ADD_C_CARRY_DEF, awc_BIR_C_def, add_with_carry_def,
  LET_THM] >>
REPEAT (POP_ASSUM MP_TAC) >>
rename1 `((b:num) <= w) /\ (w < sz + b)` >>
Q.ID_SPEC_TAC `b` >>
Induct_on `sz` >- (
  SIMP_TAC list_ss [WI_ELEM_LIST_def]
) >>
REPEAT STRIP_TAC >>
Q.PAT_X_ASSUM `!b. _` (MP_TAC o GSYM o Q.SPEC `SUC b`) >>
ASM_SIMP_TAC list_ss [WI_ELEM_LIST_def, n2w_SUC,
  n2w_11]
QED


Theorem WI_MEM_WI_end:
  !b e (w:'a word).
    WI_wf (WI_end b e) ==> (
     (WI_MEM w (WI_end b e)) <=>
      MEM w (WI_ELEM_LIST b (w2n (e - b))))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [WI_size_INTRO, WI_MEM_WI_size]
QED


Theorem WI_ELEM_LIST_ADD:
  !b:'a word n1 n2. WI_ELEM_LIST b (n1 + n2) =
                   (WI_ELEM_LIST b n1) ++ (WI_ELEM_LIST (b + n2w n1) n2)
Proof
Induct_on `n1` >> (
  SIMP_TAC list_ss [WI_ELEM_LIST_def, WORD_ADD_0]
) >>
ASM_SIMP_TAC (list_ss++wordsLib.WORD_ss) [WI_ELEM_LIST_def, arithmeticTheory.ADD_CLAUSES, n2w_SUC]
QED



(*******************)
(* empty intervals *)
(*******************)

Definition WI_is_empty_def:
  WI_is_empty i <=> !w. ~(WI_MEM w i)
End

(* Often we want to talk about wellformed, non-empty intervals. This
   is as common that it justifies a special definition. *)
Definition WI_wfe_def:
  WI_wfe i <=> (WI_wf i /\ ~(WI_is_empty i))
End

(* ALL not well-formed intervals are empty *)
Theorem WI_not_wf_empty:
  !i. ~(WI_wf i) ==> WI_is_empty i
Proof
SIMP_TAC std_ss [WI_is_empty_def] >>
METIS_TAC[WI_MEM_implies_wf]
QED


(* So the definition can actually be much simplified. *)
Theorem WI_wfe_NOT_EMPTY:
  !i. WI_wfe i <=> ~(WI_is_empty i)
Proof
METIS_TAC[WI_not_wf_empty, WI_wfe_def]
QED

Theorem WI_is_empty_NOT_WFE:
  !i. (WI_is_empty i) <=> ~(WI_wfe i)
Proof
METIS_TAC[WI_not_wf_empty, WI_wfe_def]
QED


(* Let's provide some nice rewrite rules *)
Theorem WI_wf_is_empty_End:
  !b e. WI_wf (WI_end b e) ==> (WI_is_empty (WI_end b e) <=> (b = e))
Proof
REPEAT Cases >>
ASM_SIMP_TAC arith_ss [WI_wf_def, WORD_LO,
  WI_is_empty_def, WI_MEM_def, n2w_11, WORD_LS, w2n_n2w] >>
REPEAT STRIP_TAC >>
rename1 `bn <= (en:num)` >>
EQ_TAC >> SIMP_TAC arith_ss [] >>
STRIP_TAC >>
Q.PAT_X_ASSUM `!w. _` (MP_TAC o Q.SPEC `n2w bn`) >>
ASM_SIMP_TAC arith_ss [w2n_n2w]
QED


Theorem WI_wfe_End:
  !b e. WI_wfe (WI_end b e) <=> (b <+ e)
Proof
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WI_wfe_def, WI_wf_is_empty_End] >>
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WI_wf_def, WORD_LOWER_OR_EQ] >>
METIS_TAC[WORD_NOT_LOWER_EQ]
QED


Theorem WI_is_empty_End:
  !b e. WI_is_empty (WI_end b e) <=> (e <=+ b)
Proof
SIMP_TAC std_ss [WI_is_empty_NOT_WFE, WI_wfe_End, WORD_NOT_LOWER]
QED


Theorem WI_wf_is_empty_Size:
  !b sz. WI_wf (WI_size b sz) ==> (WI_is_empty (WI_size b sz) <=> (sz = 0w))
Proof
SIMP_TAC std_ss [WI_size_def, WI_wf_is_empty_End] >>
REPEAT STRIP_TAC >>
MP_TAC (ISPECL [``0w:'a word``, ``b:'a word``, ``sz:'a word``] WORD_EQ_ADD_RCANCEL) >>
ASM_SIMP_TAC std_ss [WORD_ADD_0] >>
METIS_TAC[]
QED


Theorem WI_wfe_Size:
  !b sz. WI_wfe (WI_size b sz) <=> (b <=+ ~sz /\ sz <> 0w)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WI_wfe_def, WI_wf_is_empty_Size] >>
SIMP_TAC std_ss [WI_wf_size_compute]
QED


(**********************)
(* some trivial props *)
(**********************)

Theorem WI_empty_interval_End_Props:
  (!b. WI_wf (WI_end b b)) /\
    (!b. WI_is_empty (WI_end b b)) /\
    (!b w. ~(WI_MEM w (WI_end b b)))
Proof
SIMP_TAC std_ss [WI_wf_def, WORD_LOWER_EQ_REFL, WI_is_empty_End,
  GSYM WI_is_empty_def]
QED


Theorem WI_empty_interval_Size_Props:
  (!b. WI_wf (WI_size b 0w)) /\
    (!b. WI_is_empty (WI_size b 0w))
Proof
SIMP_TAC std_ss [WI_size_def, WORD_ADD_0, WI_empty_interval_End_Props]
QED

Theorem WI_sing_interval_Size_Props:
  !b:'a word.
       (1 < dimword (:'a)) ==>
       b <=+ ~1w ==> (

       (WI_wf (WI_size b 1w)) /\
       (~(WI_is_empty (WI_size b 1w))) /\
       (!w. (WI_MEM w (WI_size b 1w) <=> (w = b))))
Proof
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [WI_MEM_WI_size, WI_is_empty_def,
  w2n_n2w, WI_ELEM_LIST_compute] >>
SIMP_TAC std_ss [WI_wf_size_compute]
QED


Theorem WI_NOT_EMPTY_BEGIN_IN:
  !b e. WI_is_empty (WI_end b e) <=> ~ (WI_MEM b (WI_end b e))
Proof
SIMP_TAC std_ss [WI_is_empty_End, WI_MEM_def, WORD_LOWER_EQ_REFL, WORD_NOT_LOWER]
QED


Theorem WI_NOT_EMPTY_BEGIN_IN_size:
  !b sz. WI_is_empty (WI_size b sz) <=> ~ (WI_MEM b (WI_size b sz))
Proof
SIMP_TAC std_ss [WI_size_def, WI_NOT_EMPTY_BEGIN_IN]
QED


Theorem WI_MEM_characterisation:
  !i1 i2. WI_wf i1 ==> WI_wf i2 ==> ~(WI_is_empty i1 /\ WI_is_empty i2) ==> (

    (i1 = i2) <=> (!w. WI_MEM w i1 <=> WI_MEM w i2))
Proof
REPEAT Cases >>
rename1 `WI_end b1 e1 = WI_end b2 e2` >>
REPEAT STRIP_TAC >> EQ_TAC >> SIMP_TAC std_ss [] >>
STRIP_TAC >>
Q.PAT_ASSUM `!w. _` (MP_TAC o Q.SPEC `b1`) >>
Q.PAT_ASSUM `!w. _` (MP_TAC o Q.SPEC `b2`) >>
Q.PAT_ASSUM `!w. _` (MP_TAC o Q.SPEC `e2`) >>
Q.PAT_X_ASSUM `!w. _` (MP_TAC o Q.SPEC `e1`) >>
Cases_on `b1` >> Cases_on `e1` >>
Cases_on `b2` >> Cases_on `e2` >>
FULL_SIMP_TAC arith_ss [WI_MEM_def, word_interval_11, WI_wf_def, WI_wfe_def,
  WI_is_empty_End, WORD_LS, WORD_LO, w2n_n2w, n2w_11]
QED


Theorem WI_wf_size_LOWER_EQ:
  !b sz1 sz2. (sz2 <=+ sz1) ==>
              (WI_wf (WI_size (b:'a word) sz1)) ==>
              (WI_wf (WI_size b sz2))
Proof
SIMP_TAC std_ss [WI_wf_size_compute] >>
REPEAT STRIP_TAC >>
METIS_TAC[wordsTheory.WORD_LOWER_EQ_TRANS, WORD_LS_NOT]
QED



(****************)
(* Subintervals *)
(****************)

Definition WI_is_sub_def:
  WI_is_sub i1 i2 <=> (!w. WI_MEM w i1 ==> WI_MEM w i2)
End

Theorem WI_is_sub_ANTISYM:
  !i1 i2. WI_wf i1 /\ WI_wf i2 ==> WI_is_sub i1 i2 ==> WI_is_sub i2 i1 ==> ((i1 = i2) \/ (WI_is_empty i1 /\ WI_is_empty i2))
Proof
METIS_TAC [WI_MEM_characterisation, WI_is_sub_def]
QED

Theorem WI_is_sub_EMPTY:
  (!i1 i2. WI_is_empty i1 ==> (WI_is_sub i1 i2)) /\
  (!i1 i2. WI_is_empty i2 ==> (WI_is_sub i1 i2 <=> (WI_is_empty i1)))
Proof
METIS_TAC[WI_is_sub_def, WI_is_empty_def]
QED


Theorem WI_is_sub_compute:
  !b1 e1 b2 e2.
     WI_wf (WI_end b1 e1) ==>
     WI_wf (WI_end b2 e2) ==> (
     WI_is_sub (WI_end b1 e1) (WI_end b2 e2) <=>
     (b1 = e1) \/ ((b2 <=+ b1) /\ (e1 <=+ e2)))
Proof
REPEAT Cases >>
rename1 `(n2w b2 <=+ n2w b1) /\ (n2w e1 <=+ n2w e2)` >>
ASM_SIMP_TAC std_ss [WI_is_sub_def, WI_MEM_def, WORD_LO, WORD_LS, w2n_n2w, WI_wf_def, n2w_11] >>
REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >| [
  Cases_on `b1 = e1` >> ASM_REWRITE_TAC[] >>
  Q.PAT_ASSUM `!w. _ ` (MP_TAC o Q.SPEC `n2w b1`)  >>
  Q.PAT_X_ASSUM `!w. _ ` (MP_TAC o Q.SPEC `n2w e2`)  >>
  ASM_SIMP_TAC arith_ss [w2n_n2w],

  ASM_SIMP_TAC arith_ss [],

  Cases >> ASM_SIMP_TAC arith_ss [w2n_n2w]
]
QED


Theorem WI_is_sub_compute_NOT_EMPTY:
  !b1 e1 b2 e2.
     WI_wfe (WI_end b1 e1) ==>
     WI_wfe (WI_end b2 e2) ==> (
     WI_is_sub (WI_end b1 e1) (WI_end b2 e2) <=>
     (b2 <=+ b1) /\ (e1 <=+ e2))
Proof
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WI_wf_is_empty_End, WI_wfe_def, WI_is_sub_compute]
QED



(************)
(* Overlaps *)
(************)

Definition WI_overlap_def:
  WI_overlap i1 i2 <=> (?w. WI_MEM w i1 /\ WI_MEM w i2)
End

Theorem WI_overlap_SYM:
  !i1 i2. WI_overlap i1 i2 <=> WI_overlap i2 i1
Proof
METIS_TAC[WI_overlap_def]
QED

Theorem WI_overlap_EMPTY:
  (!i1 i2. WI_is_empty i1 ==> ~(WI_overlap i1 i2)) /\
  (!i1 i2. WI_is_empty i2 ==> ~(WI_overlap i1 i2))
Proof
METIS_TAC[WI_overlap_def, WI_is_empty_def]
QED


Theorem WI_overlap_compute:
  !b1 e1 b2 e2.
     WI_wf (WI_end b1 e1) ==>
     WI_wf (WI_end b2 e2) ==> (
     WI_overlap (WI_end b1 e1) (WI_end b2 e2) <=>
     (b1 <+ e1) /\ (b2 <+ e2) /\ (((b2 <=+ b1 /\ b1 <+ e2) \/ (b1 <=+ b2 /\ b2 <+ e1))))
Proof
REPEAT Cases >>
ASM_SIMP_TAC std_ss [WI_wf_def, WI_overlap_def, WORD_LS, WORD_LO, w2n_n2w] >>
rename1 `(b1 < (e1:num)) /\ (b2 < (e2:num)) /\ _` >>
REPEAT STRIP_TAC >>
`(b1 < e1) <=> ~(b1 = e1)` by DECIDE_TAC >>
`(b2 < e2) <=> ~(b2 = e2)` by DECIDE_TAC >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `b1 = e1` >- ASM_SIMP_TAC std_ss [WI_empty_interval_End_Props] >>
Cases_on `b2 = e2` >- ASM_SIMP_TAC std_ss [WI_empty_interval_End_Props] >>
FULL_SIMP_TAC arith_ss [WI_MEM_def] >>
EQ_TAC >| [
  SIMP_TAC std_ss [PULL_EXISTS] >>
  Cases >>
  ASM_SIMP_TAC arith_ss [WORD_LO, WORD_LS, w2n_n2w],

  STRIP_TAC >| [
    Q.EXISTS_TAC `n2w b1` >>
    ASM_SIMP_TAC arith_ss [WORD_LO, WORD_LS, w2n_n2w],

    Q.EXISTS_TAC `n2w b2` >>
    ASM_SIMP_TAC arith_ss [WORD_LO, WORD_LS, w2n_n2w]
  ]
]
QED


Theorem WI_overlap_compute_NOT_EMPTY:
  !b1 e1 b2 e2.
     WI_wfe (WI_end b1 e1) ==>
     WI_wfe (WI_end b2 e2) ==> (
     WI_overlap (WI_end b1 e1) (WI_end b2 e2) <=>
     (((b2 <=+ b1 /\ b1 <+ e2) \/ (b1 <=+ b2 /\ b2 <+ e1))))
Proof
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [WI_wfe_def, WI_overlap_compute,
  WI_is_empty_End, WORD_NOT_LOWER_EQUAL]
QED


(************)
(* Distinct *)
(************)

Definition WI_distinct_def:
  WI_distinct i1 i2 <=> ~(WI_overlap i1 i2)
End

Theorem WI_distinct_ALT_DEF:
  !(i1:'a word_interval_t) i2. WI_distinct i1 i2 <=> !w. ~(WI_MEM w i1) \/ ~(WI_MEM w i2)
Proof
SIMP_TAC std_ss [WI_distinct_def, WI_overlap_def] >>
METIS_TAC[]
QED

Theorem WI_distinct_SYM:
  !i1 i2. WI_distinct i1 i2 <=> WI_distinct i2 i1
Proof
METIS_TAC[WI_distinct_ALT_DEF]
QED

Theorem WI_distinct_EMPTY:
  (!i1 i2. WI_is_empty i1 ==> (WI_distinct i1 i2)) /\
  (!i1 i2. WI_is_empty i2 ==> (WI_distinct i1 i2))
Proof
SIMP_TAC std_ss [WI_distinct_def, WI_overlap_EMPTY]
QED

Theorem WI_distinct_WI_MEM_L:
  !i1 i2. WI_distinct i1 i2 <=> (!w. WI_MEM w i1 ==> ~(WI_MEM w i2))
Proof
METIS_TAC [WI_distinct_ALT_DEF]
QED

Theorem WI_distinct_WI_MEM_R:
  !i1 i2. WI_distinct i1 i2 <=> (!w. WI_MEM w i2 ==> ~(WI_MEM w i1))
Proof
METIS_TAC [WI_distinct_ALT_DEF]
QED


Theorem WI_distinct_compute:
  !b1 e1 b2 e2.
     WI_wf (WI_end b1 e1) ==>
     WI_wf (WI_end b2 e2) ==> (
     WI_distinct (WI_end b1 e1) (WI_end b2 e2) <=>
     ((e1 <=+ b1) \/ (e2 <=+ b2) \/ (((b1 <+ b2 \/ e2 <=+ b1) /\ (b2 <+ b1 \/ e1 <=+ b2)))))
Proof
SIMP_TAC std_ss [WI_distinct_def, WI_overlap_compute,
  WORD_NOT_LOWER_EQUAL, WORD_NOT_LOWER]
QED


Theorem WI_distinct_compute_NOT_EMPTY:
  !b1 e1 b2 e2.
     WI_wfe (WI_end b1 e1) ==>
     WI_wfe (WI_end b2 e2) ==> (
     WI_distinct (WI_end b1 e1) (WI_end b2 e2) <=>
     (((b1 <+ b2 \/ e2 <=+ b1) /\ (b2 <+ b1 \/ e1 <=+ b2))))
Proof
SIMP_TAC std_ss [WI_distinct_def, WI_overlap_compute_NOT_EMPTY,
  WORD_NOT_LOWER_EQUAL, WORD_NOT_LOWER]
QED



(***************************************)
(* Distinct to unchanged memory region *)
(***************************************)

(* A special case as needed for showing that a given fixed interval (mb, me) is
   disjoint from an interval written too (wb, sz) *)
Definition WI_distinct_MEM_UNCHANGED_COMPUTE_def:
  WI_distinct_MEM_UNCHANGED_COMPUTE (mb : 'a word) (me : 'a word) (wb : 'a word) sz =
    (wb <=+ n2w ((dimword (:'a) - 1) - sz) /\
    ((mb <+ wb \/ (n2w sz + wb <=+ mb)) /\
    ((wb <+ mb \/ me <=+ wb))))
End


Theorem WI_distinct_compute_MEM_UNCHANGED:
  !(mb:'a word) me.
     WI_wfe (WI_end (mb:'a word) me) ==>

    !(wb:'a word) sz. (sz < dimword (:'a)) /\ (sz <> 0) ==>
    (WI_distinct_MEM_UNCHANGED_COMPUTE mb me wb sz <=>
     (WI_wfe (WI_size wb (n2w sz))) /\ (WI_distinct (WI_end mb me) (WI_size wb (n2w sz))))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WI_distinct_compute_NOT_EMPTY, WI_size_def,
  WI_distinct_MEM_UNCHANGED_COMPUTE_def] >>
SIMP_TAC std_ss [GSYM WI_wf_size_compute, GSYM WI_size_def, WI_wfe_Size] >>
ASM_SIMP_TAC std_ss [WI_wf_size_compute, n2w_11, ZERO_LT_dimword] >>
FULL_SIMP_TAC std_ss [WI_wfe_End, word_1comp_n2w]
QED



Theorem WI_distinct_compute_MEM_UNCHANGED_COND_REWRITE:
  !(wb:'a word) mb me sz.
    (mb MOD dimword (:'a) < me MOD dimword (:'a) /\ sz < dimword (:'a) /\ sz <> 0) ==>
    (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb) (n2w me) wb sz <=>
     (WI_wfe (WI_size wb (n2w sz))) /\
     WI_wfe (WI_end ((n2w mb):'a word) (n2w me)) /\
     (WI_distinct (WI_end ((n2w mb):'a word) (n2w me)) (WI_size wb (n2w sz))))
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`n2w mb`, `n2w me`] WI_distinct_compute_MEM_UNCHANGED) >>
ASM_SIMP_TAC std_ss [WI_wfe_End, word_lo_n2w]
QED



Definition BExp_unchanged_mem_interval_distinct_def:
  BExp_unchanged_mem_interval_distinct sz mb_n me_n wb_e isz =
     (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessOrEqual wb_e
           (BExp_Const (n2bs ((2 ** (size_of_bir_immtype sz) − 1 − isz)) sz)))
        (BExp_BinExp BIExp_And
           (BExp_BinExp BIExp_Or
              (BExp_BinPred BIExp_LessThan (BExp_Const (n2bs mb_n sz))
                 wb_e)
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_BinExp BIExp_Plus (BExp_Const (n2bs isz sz))
                    wb_e) (BExp_Const (n2bs mb_n sz))))
           (BExp_BinExp BIExp_Or
              (BExp_BinPred BIExp_LessThan wb_e
                 (BExp_Const (n2bs mb_n sz)))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (n2bs me_n sz)) wb_e))))
End



Theorem BExp_unchanged_mem_interval_distinct_eval:
  !sz mb_n me_n wb_e isz env.
  (bir_eval_exp (BExp_unchanged_mem_interval_distinct sz mb_n me_n wb_e isz) env =
     case (sz, bir_eval_exp wb_e env) of
         (Bit1, SOME (BVal_Imm (Imm1 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | (Bit8, SOME (BVal_Imm (Imm8 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | (Bit16, SOME (BVal_Imm (Imm16 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | (Bit32, SOME (BVal_Imm (Imm32 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | (Bit64, SOME (BVal_Imm (Imm64 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | (Bit128, SOME (BVal_Imm (Imm128 wb))) =>
            SOME (BVal_Imm (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz)))
       | _ => NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [WI_distinct_MEM_UNCHANGED_COMPUTE_def,
  BExp_unchanged_mem_interval_distinct_def] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [
     bir_bool_expTheory.bir_bin_exp_BOOL_OPER_EVAL]
)
QED


Theorem BExp_unchanged_mem_interval_distinct_type_of:
  !sz mb_n me_n wb_e isz.
  (type_of_bir_exp (BExp_unchanged_mem_interval_distinct sz mb_n me_n wb_e isz) =
   if (type_of_bir_exp wb_e = SOME (BType_Imm sz)) then
    SOME BType_Bool else NONE)
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_unchanged_mem_interval_distinct_def,
  type_of_bir_exp_def, pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def]
)
QED


Theorem BExp_unchanged_mem_interval_distinct_vars_of:
  !sz mb_n me_n wb_e isz.
  (bir_vars_of_exp (BExp_unchanged_mem_interval_distinct sz mb_n me_n wb_e isz) =
   bir_vars_of_exp wb_e)
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_unchanged_mem_interval_distinct_def,
  pred_setTheory.UNION_EMPTY, pred_setTheory.UNION_IDEMPOT]
QED


(* For computing the intervals, some extra syntax is handy *)

Definition FUNS_EQ_OUTSIDE_WI_size_def:
  FUNS_EQ_OUTSIDE_WI_size (b:'a word) (sz : num) (f1 : 'a word -> 'b) (f2 : 'a word -> 'b) <=>
  ((WI_wf (WI_size b (n2w sz))) ==>
  (!a. ~(WI_MEM a (WI_size b (n2w sz))) ==>
       (f1 a = f2 a)))
End


val _ = export_theory();
