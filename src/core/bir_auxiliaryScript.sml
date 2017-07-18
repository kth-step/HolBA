open HolKernel Parse boolLib bossLib;

val _ = new_theory "bir_auxiliary";

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;


(* -------------------------------------------------------------------------- *)
(* List lemmata                                                               *)
(* -------------------------------------------------------------------------- *)

val LAST_FILTER_EL = store_thm ("LAST_FILTER_EL",
  ``!P l. (FILTER P l <> []) ==> (
          (?i. (i < LENGTH l) /\ (LAST (FILTER P l) = EL i l) /\ P (EL i l) /\
               (!j. i < j /\ j < LENGTH l ==> ~(P (EL j l)))))``,
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
]);


val LENGTH_LASTN_LE = store_thm ("LENGTH_LASTN_LE",
  ``!n l. LENGTH (LASTN n l) <= LENGTH l``,

SIMP_TAC list_ss [rich_listTheory.LASTN_def,
  listTheory.LENGTH_TAKE_EQ]);


val dropWhile_MAP = store_thm ("dropWhile_MAP",
  ``!P f l. dropWhile P (MAP f l) =
            MAP f (dropWhile (P o f) l)``,

GEN_TAC >> GEN_TAC >>
Induct >> ASM_SIMP_TAC list_ss [] >>
GEN_TAC >> COND_CASES_TAC >> (
  SIMP_TAC list_ss []
))

val DROP_GENLIST = store_thm ("DROP_GENLIST",
  ``!n (f:num->'a) m.
      DROP n (GENLIST f m) =
      GENLIST (\n'. (f (n' + n))) (m - n)``,
Induct >- (
  SIMP_TAC (list_ss++boolSimps.ETA_ss) []
) >>
GEN_TAC >> Cases >- (
  SIMP_TAC list_ss []
) >>
ASM_SIMP_TAC list_ss [listTheory.GENLIST_CONS, arithmeticTheory.ADD_CLAUSES])


val INDEX_FIND_EQ_NONE = store_thm ("INDEX_FIND_EQ_NONE",
  ``!l i P. (INDEX_FIND i P l = NONE) <=> (~(EXISTS P l))``,
Induct >> SIMP_TAC list_ss [listTheory.INDEX_FIND_def] >>
REPEAT GEN_TAC >> COND_CASES_TAC >> ASM_SIMP_TAC list_ss []);


val INDEX_FIND_EQ_SOME = store_thm ("INDEX_FIND_EQ_SOME",
  ``!l i P j e. (INDEX_FIND i P l = SOME (j, e)) <=> (
       (i <= j) /\ (j - i < LENGTH l) /\
       (EL (j - i) l = e) /\ P e /\
       (!j'. (i <= j' /\ j' < j) ==> ~(P (EL (j' - i) l))))``,

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
]);


val INDEX_FIND_EQ_SOME_0 = store_thm ("INDEX_FIND_EQ_SOME_0",
  ``!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [INDEX_FIND_EQ_SOME] >>
Cases_on `LENGTH l` >> SIMP_TAC std_ss []);


val SEG_SUC_LENGTH = store_thm ("SEG_SUC_LENGTH",
``!l n m. (n + m < LENGTH l) ==>
          (SEG (SUC n) m l = (EL m l)::SEG n (SUC m) l)``,

SIMP_TAC arith_ss [rich_listTheory.SEG_TAKE_BUTFISTN] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC list_ss [rich_listTheory.DROP_EL_CONS, arithmeticTheory.ADD1]);


(* -------------------------------------------------------------------------- *)
(* Word lemmata                                                               *)
(* -------------------------------------------------------------------------- *)


val w2n_MOD_2EXP_ID = store_thm ("w2n_MOD_2EXP_ID",
  ``!(w:'a word). (MOD_2EXP (dimindex (:'a)) (w2n w)) = w2n w``,
SIMP_TAC std_ss [GSYM wordsTheory.MOD_2EXP_DIMINDEX, wordsTheory.w2n_lt]);

val word_extract_bits_w2w = store_thm ("word_extract_bits_w2w",
  ``!h l a. ((h >< l) (a:'a word)) = w2w ((h -- l) a)``,
SIMP_TAC std_ss [wordsTheory.word_extract_w2w_mask, wordsTheory.word_bits_mask])

val sw2sw_w2w_downcast = store_thm ("sw2sw_w2w_downcast", ``!w.
  (dimindex (:'b) <= dimindex (:'a)) ==> ((sw2sw (w : 'a word) : 'b word) = w2w w)``,

REPEAT STRIP_TAC >>
`(2**dimindex (:'b) <= 2**dimindex (:'a))` by METIS_TAC[bitTheory.TWOEXP_MONO2] >>
`(2**dimindex (:'b) - 2**dimindex (:'a)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [sw2sw_def,
  bitTheory.SIGN_EXTEND_def, LET_DEF, w2w_def,
  wordsTheory.w2n_lt, GSYM wordsTheory.dimword_def
]);


val fixwidth_fixwidth_le = store_thm ("fixwidth_fixwidth_le",
  ``!v n m. n <= m ==> (fixwidth n (fixwidth m v) = fixwidth n v)``,

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
]);


val w2v_word_join = store_thm ("w2v_word_join",
``FINITE univ(:'a) /\ FINITE univ(:'b) ==>
  !w1:'a word w2:'b word. w2v (word_join w1 w2) = (w2v w1 ++ w2v w2)``,

REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp,
  word_join_v2w, fcpTheory.index_sum]);


val w2v_word_concat = store_thm ("w2v_word_concat",
``FINITE univ(:'a) /\ FINITE univ(:'b) /\ (dimindex (:'c) = dimindex (:'a) + dimindex (:'b)) ==>
  !w1:'a word w2:'b word. w2v ((w1 @@ w2):'c word) = (w2v w1 ++ w2v w2)``,

REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp, word_concat_def,
  word_join_v2w, fcpTheory.index_sum, w2w_def, w2n_v2w, bitTheory.MOD_2EXP_def] >>
`v2n (v ++ v') < 2 ** (LENGTH v + LENGTH v')` by (
  METIS_TAC[bitstringTheory.v2n_lt, listTheory.LENGTH_APPEND]
) >>
ASM_SIMP_TAC list_ss [n2w_v2n, w2v_v2w, fixwidth_id_imp]);


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


val _ = export_theory();
