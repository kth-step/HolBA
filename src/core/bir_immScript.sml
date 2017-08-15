open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory;

val _ = new_theory "bir_imm";

(* ------------------------------------------------------------------------- *)
(*  Immediates                                                               *)
(* ------------------------------------------------------------------------- *)

(* Immediates can be words of various sizes *)
val _ = Datatype `bir_imm_t =
    Imm1  bool[1]
  | Imm8  bool[8]
  | Imm16 bool[16]
  | Imm32 bool[32]
  | Imm64 bool[64]
`;


(* It is handy to keep track of the size via both a special datatype and a number *)
val _ = Datatype `bir_immtype_t =
  | Bit1
  | Bit8
  | Bit16
  | Bit32
  | Bit64
`;

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));


val fold_bir_immtype_THM = store_thm ("fold_bir_immtype_THM",
  ``!P. ((P Bit1 /\ P Bit8 /\ P Bit16 /\ P Bit32 /\ P Bit64) <=> (!ty. P ty))``,
    SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) []);


val type_of_bir_imm_def = Define `
  (type_of_bir_imm (Imm1  _) = Bit1) /\
  (type_of_bir_imm (Imm8  _) = Bit8) /\
  (type_of_bir_imm (Imm16 _) = Bit16) /\
  (type_of_bir_imm (Imm32 _) = Bit32) /\
  (type_of_bir_imm (Imm64 _) = Bit64)`;

val size_of_bir_immtype_def = Define `
  (size_of_bir_immtype Bit1  = 1) /\
  (size_of_bir_immtype Bit8  = 8) /\
  (size_of_bir_immtype Bit16 = 16) /\
  (size_of_bir_immtype Bit32 = 32) /\
  (size_of_bir_immtype Bit64 = 64)`

val bir_immtype_of_size_def = Define `
  bir_immtype_of_size n = (
         if n = 1  then SOME Bit1
    else if n = 8  then SOME Bit8
    else if n = 16 then SOME Bit16
    else if n = 32 then SOME Bit32
    else if n = 64 then SOME Bit64
    else NONE)`;

val is_valid_bir_immtype_size_def = Define `
  is_valid_bir_immtype_size n = ?b. n = size_of_bir_immtype b`;

(* A few sanity checks *)
val size_of_bir_immtype_INJ = store_thm ("size_of_bir_immtype_INJ",
  ``!b1 b2. (size_of_bir_immtype b1 = size_of_bir_immtype b2) <=> (b1 = b2)``,
Cases >> Cases >> SIMP_TAC (std_ss++bir_imm_ss) [size_of_bir_immtype_def]);

val size_of_bir_immtype_NEQ_0 = store_thm ("size_of_bir_immtype_NEQ_0",
  ``!b. size_of_bir_immtype b <> 0``,
Cases >> SIMP_TAC arith_ss [size_of_bir_immtype_def])

val is_valid_bir_immtype_size_REWRS = save_thm ("is_valid_bir_immtype_size_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [size_of_bir_immtype_def] is_valid_bir_immtype_size_def);


val size_of_bir_immtype_EQ_REWRS0 = prove (
  ``!ty n. is_valid_bir_immtype_size n ==>
           ((size_of_bir_immtype ty = n) <=> (ty = THE (bir_immtype_of_size n)))``,
Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [is_valid_bir_immtype_size_REWRS, DISJ_IMP_THM, FORALL_AND_THM,
    bir_immtype_of_size_def, size_of_bir_immtype_def]
));

val size_of_bir_immtype_EQ_REWRS = save_thm("size_of_bir_immtype_EQ_REWRS",
  SIMP_RULE std_ss [size_of_bir_immtype_def, is_valid_bir_immtype_size_REWRS, DISJ_IMP_THM,
    FORALL_AND_THM, bir_immtype_of_size_def]
    size_of_bir_immtype_EQ_REWRS0);

val is_valid_bir_immtype_size_IMP = save_thm ("is_valid_bir_immtype_size_IMP",
  snd (EQ_IMP_RULE (SPEC_ALL is_valid_bir_immtype_size_REWRS)));

val is_valid_bir_immtype_size_IS_SOME = store_thm ("is_valid_bir_immtype_size_IS_SOME",
  ``!n. is_valid_bir_immtype_size n <=> IS_SOME (bir_immtype_of_size n)``,
SIMP_TAC std_ss [is_valid_bir_immtype_size_REWRS, bir_immtype_of_size_def] >>
METIS_TAC[optionTheory.IS_SOME_DEF]);

val bir_immtype_of_num_inv = store_thm ("bir_immtype_of_num_inv",
  ``(!brt. bir_immtype_of_size (size_of_bir_immtype brt) = SOME brt) /\
    (!n brt. (bir_immtype_of_size n = SOME brt) ==>
             (size_of_bir_immtype brt = n))``,
REPEAT CONJ_TAC >| [
  Cases >> SIMP_TAC std_ss [size_of_bir_immtype_def, bir_immtype_of_size_def],

  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_immtype_of_size_def, DISJ_IMP_THM, FORALL_AND_THM,
    COND_EXPAND_OR, LEFT_AND_OVER_OR, size_of_bir_immtype_def]
]);


val bir_immtype_of_size_REWRS_SOME = save_thm ("bir_immtype_of_size_REWRS_SOME",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``])
            [size_of_bir_immtype_def] (CONJUNCT1 bir_immtype_of_num_inv));


val bir_immtype_of_size_REWRS_NONE = save_thm ("bir_immtype_of_size_REWRS_NONE",
let
  val thm_none_aux = prove (``!n. ~(is_valid_bir_immtype_size n) ==> (bir_immtype_of_size n = NONE)``,
    SIMP_TAC std_ss [is_valid_bir_immtype_size_IS_SOME]);
  val thm_none = SIMP_RULE std_ss [is_valid_bir_immtype_size_REWRS] thm_none_aux
in
  thm_none
end);


(* ------------------------------------------------------------------------- *)
(*  Transformation between immediates and numbers                            *)
(* ------------------------------------------------------------------------- *)
val b2n_def = Define `
  (b2n ( Imm1  w ) = w2n w) /\
  (b2n ( Imm8  w ) = w2n w) /\
  (b2n ( Imm16 w ) = w2n w) /\
  (b2n ( Imm32 w ) = w2n w) /\
  (b2n ( Imm64 w ) = w2n w)
`;

val n2bs_def = Define `
  (n2bs n Bit1  = Imm1  (n2w n)) /\
  (n2bs n Bit8  = Imm8  (n2w n)) /\
  (n2bs n Bit16 = Imm16 (n2w n)) /\
  (n2bs n Bit32 = Imm32 (n2w n)) /\
  (n2bs n Bit64 = Imm64 (n2w n))`

val n2b_1_def  = Define `n2b_1  n = n2bs n Bit1`;
val n2b_8_def  = Define `n2b_8  n = n2bs n Bit8`;
val n2b_16_def = Define `n2b_16 n = n2bs n Bit16`;
val n2b_32_def = Define `n2b_32 n = n2bs n Bit32`;
val n2b_64_def = Define `n2b_64 n = n2bs n Bit64`;

val _ = add_bare_numeral_form (#"x", SOME "n2b_64");
val _ = add_bare_numeral_form (#"e", SOME "n2b_32");
val _ = add_bare_numeral_form (#"d", SOME "n2b_16");
val _ = add_bare_numeral_form (#"c", SOME "n2b_8");
val _ = add_bare_numeral_form (#"b", SOME "n2b_1");

val n2b_fixed_DEFS = save_thm ("n2b_fixed_DEFS",
    LIST_CONJ [n2b_1_def, n2b_8_def, n2b_16_def, n2b_32_def, n2b_64_def]);

val b2n_n2bs = store_thm ("b2n_n2bs",
  ``!bt n. b2n (n2bs n bt) = MOD_2EXP (size_of_bir_immtype bt) n``,
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2n_def, n2bs_def, w2n_n2w,
    size_of_bir_immtype_def, bitTheory.MOD_2EXP_def]
));

val b2n_n2b_fixed = store_thm ("b2n_n2b_fixed",
  ``(!n. b2n (n2b_1 n)  = n MOD 2) /\
    (!n. b2n (n2b_8 n)  = n MOD 2**8) /\
    (!n. b2n (n2b_16 n) = n MOD 2**16) /\
    (!n. b2n (n2b_32 n) = n MOD 2**32) /\
    (!n. b2n (n2b_64 n) = n MOD 2**64) /\
    (!n bt. b2n (n2bs n bt) = n MOD 2**(size_of_bir_immtype bt))``,

SIMP_TAC std_ss [n2b_fixed_DEFS, b2n_n2bs, size_of_bir_immtype_def,
  bitTheory.MOD_2EXP_def]);

val n2bs_b2n = store_thm ("n2bs_b2n",
  ``!b s. (s = type_of_bir_imm b) ==> (n2bs (b2n b) s = b)``,
Cases >> (
  SIMP_TAC std_ss [b2n_def, n2bs_def, type_of_bir_imm_def, n2w_w2n]
));

val w2n_lt_trans = prove (``!w:'a word. dimword (:'a) <= m ==> (w2n w < m)``,
METIS_TAC[w2n_lt, arithmeticTheory.LESS_LESS_EQ_TRANS]);

val b2n_lt = store_thm ("b2n_lt",
  ``!b. b2n b < 2 ** (size_of_bir_immtype (type_of_bir_imm b))``,
Cases >> (
  SIMP_TAC std_ss [b2n_def, type_of_bir_imm_def, size_of_bir_immtype_def] >>
  MATCH_MP_TAC w2n_lt_trans >>
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
));


val b2n_lt_REWRS = save_thm ("b2n_lt_REWRS",
SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_imm_t``]) [
  type_of_bir_imm_def, size_of_bir_immtype_def] b2n_lt);


val b2n_MOD_2EXP = store_thm ("b2n_MOD_2EXP",
  ``!i n. ((size_of_bir_immtype (type_of_bir_imm i)) = n) ==>
          (MOD_2EXP n (b2n i) = b2n i)``,
SIMP_TAC std_ss [bitTheory.MOD_2EXP_def, b2n_lt]);


val type_of_n2bs = store_thm ("type_of_n2bs",
``!s n. type_of_bir_imm (n2bs n s) = s``,
Cases >> SIMP_TAC std_ss [n2bs_def, type_of_bir_imm_def]);


val type_of_n2b_fixed = save_thm ("type_of_n2b_fixed",
SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
  GSYM n2b_fixed_DEFS] type_of_n2bs);


val type_of_bir_imm_n2bs_INTRO = store_thm ("type_of_bir_imm_n2bs_INTRO",
  ``!s b. (type_of_bir_imm b = s) <=> (?n. b = n2bs n s)``,

REPEAT GEN_TAC >> EQ_TAC >> STRIP_TAC >| [
  Q.EXISTS_TAC `b2n b` >>
  ASM_SIMP_TAC std_ss [n2bs_b2n],

  ASM_SIMP_TAC std_ss [type_of_n2bs]
]);


val n2bs_MOD_size_of_bir_immtype = store_thm ("n2bs_MOD_size_of_bir_immtype",
  ``!s n. n2bs (MOD_2EXP (size_of_bir_immtype s) n) s = n2bs n s``,

REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `n2bs n s = n2bs (b2n (n2bs n s)) s` SUBST1_TAC >- METIS_TAC[n2bs_b2n, type_of_n2bs] >>
SIMP_TAC std_ss [b2n_n2bs]);


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and words                              *)
(* ------------------------------------------------------------------------- *)

val b2w_def = Define `b2w bi = n2w (b2n bi)`;

val b2w_REWRS = store_thm ("b2w_REWRS",
``(!w. (b2w ( Imm1  w ) = w2w w)) /\
  (!w. (b2w ( Imm8  w ) = w2w w)) /\
  (!w. (b2w ( Imm16 w ) = w2w w)) /\
  (!w. (b2w ( Imm32 w ) = w2w w)) /\
  (!w. (b2w ( Imm64 w ) = w2w w))``,
REWRITE_TAC[b2w_def, b2n_def, w2w_def]);

val w2bs_def = Define `w2bs w s = n2bs (w2n w) s`

val w2bs_REWRS = store_thm ("w2bs_REWRS",
``(!w. (w2bs w Bit1  = Imm1  (w2w w))) /\
  (!w. (w2bs w Bit8  = Imm8  (w2w w))) /\
  (!w. (w2bs w Bit16 = Imm16 (w2w w))) /\
  (!w. (w2bs w Bit32 = Imm32 (w2w w))) /\
  (!w. (w2bs w Bit64 = Imm64 (w2w w)))``,
SIMP_TAC std_ss [w2bs_def,n2bs_def, w2w_def]);


val w2bs_b2w = store_thm ("w2bs_b2w",
  ``!b s. ((s = type_of_bir_imm b) /\ size_of_bir_immtype (type_of_bir_imm b) <= dimindex (:'a)) ==>
          (w2bs ((b2w b):'a word) s = b)``,
SIMP_TAC std_ss [w2bs_def, b2w_def, w2n_n2w] >>
REPEAT STRIP_TAC >>
`b2n b MOD (dimword (:'a)) = b2n b` by (
  MATCH_MP_TAC arithmeticTheory.LESS_MOD >>
  ASSUME_TAC (Q.SPEC `b` b2n_lt) >>
  FULL_SIMP_TAC arith_ss [dimword_def] >>
  `2 ** size_of_bir_immtype (type_of_bir_imm b) <= 2 ** dimindex (:'a)` by
     METIS_TAC[bitTheory.TWOEXP_MONO2] >>
  DECIDE_TAC
) >>
ASM_SIMP_TAC std_ss [n2bs_b2n])

val type_of_w2bs = store_thm ("type_of_w2bs",
``!s w. type_of_bir_imm (w2bs w s) = s``,
SIMP_TAC std_ss [w2bs_def, type_of_n2bs]);


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and bool                               *)
(* ------------------------------------------------------------------------- *)

val b2bool_def = Define `b2bool bi = (b2n bi <> 0)`;

val b2bool_REWRS = save_thm ("b2bool_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_imm_t``]) [
    b2n_def, w2n_eq_0]
    b2bool_def);

val bool2w_def = Define `bool2w b = (if b then 1w else 0w):word1`;
val bool2b_def = Define `bool2b b = Imm1 (bool2w b)`;

val bool2b_inv = store_thm ("bool2b_inv",
  ``(!b. (b2bool (bool2b b) = b)) /\
    (!w. ((bool2b (b2bool (Imm1 w))) = Imm1 w))``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss)
  [b2bool_def, bool2b_def, b2n_def, w2n_eq_0, bool2w_def] >>
Cases >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [] >>
`(n = 0) \/ (n = 1)` by DECIDE_TAC >> (
  ASM_SIMP_TAC std_ss []
));

val type_of_bool2b = store_thm ("type_of_bool2b",
  ``!b. type_of_bir_imm (bool2b b) = Bit1``,
SIMP_TAC std_ss [bool2b_def, type_of_bir_imm_def]);

val bool2w_EQ_ELIMS = store_thm ("bool2w_EQ_ELIMS",
  ``(!b. (bool2w b = 1w) <=> b) /\
    (!b. (bool2w b = 0w) <=> ~b) /\
    (!b. (1w = bool2w b) <=> b) /\
    (!b. (0w = bool2w b) <=> ~b)``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++bir_imm_ss++wordsLib.WORD_ss) [bool2w_def]);


val bool2b_EQ_IMM1_ELIMS = store_thm ("bool2b_EQ_IMM1_ELIMS",
  ``(!b. (bool2b b = Imm1 1w) <=> b) /\
    (!b. (bool2b b = Imm1 0w) <=> ~b) /\
    (!b. (Imm1 1w = bool2b b) <=> b) /\
    (!b. (Imm1 0w = bool2b b) <=> ~b)``,

SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def, bool2w_EQ_ELIMS]);


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and bitstrings                         *)
(* ------------------------------------------------------------------------- *)

val v2bs_def = Define `v2bs v s = n2bs (v2n v) s`;

val v2bs_REWRS = save_thm ("v2bs_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_immtype_t``]) [
    n2bs_def, FORALL_AND_THM, n2w_v2n] v2bs_def);

val b2v_def = Define `
  (b2v ( Imm1  w ) = w2v w) /\
  (b2v ( Imm8  w ) = w2v w) /\
  (b2v ( Imm16 w ) = w2v w) /\
  (b2v ( Imm32 w ) = w2v w) /\
  (b2v ( Imm64 w ) = w2v w)
`;

val b2v_LENGTH = store_thm ("b2v_LENGTH",
  ``!r. LENGTH (b2v r) = size_of_bir_immtype (
        type_of_bir_imm r)``,
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2v_def, type_of_bir_imm_def,
    size_of_bir_immtype_def, length_w2v]
));

val v2n_w2v = store_thm ("v2n_w2v",
``!w:'a word. (v2n (w2v w) = w2n w)``,
GEN_TAC >>
bitstringLib.Cases_on_v2w `w` >>
ASM_SIMP_TAC std_ss [w2n_v2w, w2v_v2w,
  fixwidth_id_imp, bitTheory.MOD_2EXP_def, v2n_lt]
);

val v2n_b2v = store_thm ("v2n_b2v",
  ``!r. v2n (b2v r) = b2n r``,
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2n_def, b2v_def, v2n_w2v]
));


val type_of_v2bs = store_thm ("type_of_v2bs",
``!s v. type_of_bir_imm (v2bs v s) = s``,
SIMP_TAC std_ss [v2bs_def, type_of_n2bs]);


val v2w_fixwidth_imp = store_thm ("v2w_fixwidth_imp",
  ``!v w. ((dimindex (:'a)) <= w) ==>
          ((v2w (fixwidth w v) = ((v2w v):'a word)))``,
REPEAT STRIP_TAC >>
`fixwidth (dimindex (:'a)) (fixwidth w v) = fixwidth (dimindex (:'a)) v` by (
  METIS_TAC[fixwidth_fixwidth_le]
) >>
METIS_TAC[v2w_fixwidth]);


val v2bs_fixwidth = store_thm ("v2bs_fixwidth",
``!v vty w. (size_of_bir_immtype vty <= w) ==>
            (v2bs (fixwidth w v) vty = v2bs v vty)``,

GEN_TAC >> Cases >>
SIMP_TAC (std_ss++wordsLib.WORD_ss) [v2bs_def, n2bs_def, n2w_v2n,
  v2w_fixwidth_imp, size_of_bir_immtype_def]);

val v2bs_n2v = store_thm ("v2bs_n2v",
  ``!n. v2bs (n2v n) = n2bs n``,
SIMP_TAC std_ss [FUN_EQ_THM, v2bs_def, v2n_n2v]);



val n2v_v2n = store_thm ("n2v_v2n",
``!v n. (LENGTH v = n) ==> (fixwidth n (n2v (v2n v)) = v)``,

GEN_TAC >>
SIMP_TAC list_ss [v2n_def, n2v_def, numposrepTheory.num_from_bin_list_def,
    numposrepTheory.num_to_bin_list_def] >>
`EVERY ($> 2) (bitify [] v)` by (
   SIMP_TAC list_ss [bitify_reverse_map, listTheory.EVERY_MEM,
     listTheory.MEM_MAP, GSYM LEFT_FORALL_IMP_THM] >>
   Cases >> SIMP_TAC std_ss []
) >>

FULL_SIMP_TAC list_ss [numposrepTheory.n2l_l2n, numposrepTheory.l2n_eq_0,
  boolify_reverse_map, bitify_reverse_map, listTheory.EVERY_MEM,
  listTheory.MEM_MAP, GSYM LEFT_FORALL_IMP_THM] >>
POP_ASSUM (K ALL_TAC) >>
SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [listTheory.MAP_TAKE,
  rich_listTheory.MAP_REVERSE, listTheory.MAP_MAP_o, combinTheory.o_DEF,
  GSYM rich_listTheory.LASTN_def] >>
COND_CASES_TAC >- (
  SIMP_TAC list_ss [fixwidth_def, LET_DEF, zero_extend_def,
    listTheory.PAD_LEFT] >>
  Cases_on `v` >> FULL_SIMP_TAC list_ss [] >>
  rename1 `LENGTH v` >>
  Cases_on `v` >> FULL_SIMP_TAC list_ss [GSYM rich_listTheory.REPLICATE_GENLIST] >>
  rename1 `LENGTH v` >>

  `[F] = REPLICATE (SUC 0) F` by SIMP_TAC list_ss [rich_listTheory.REPLICATE] >>
  ASM_REWRITE_TAC[rich_listTheory.REPLICATE_APPEND, arithmeticTheory.ADD_CLAUSES] >>
  SIMP_TAC list_ss [rich_listTheory.REPLICATE] >>
  Induct_on `v` >> (
    ASM_SIMP_TAC list_ss [rich_listTheory.REPLICATE]
  )
) >>


Q.SUBGOAL_THEN `(LOG 2 (l2n 2 (REVERSE (MAP (\b. if b then 1 else 0) v)))) =
  PRE (LENGTH (dropWhile ($= 0) (REVERSE (REVERSE (MAP (\b. if b then 1 else 0) v)))))` SUBST1_TAC >- (
   MATCH_MP_TAC numposrepTheory.LOG_l2n_dropWhile >>
   ASM_SIMP_TAC list_ss [listTheory.EXISTS_MEM, listTheory.EVERY_MEM,
     listTheory.MEM_MAP, GSYM LEFT_FORALL_IMP_THM] >>
   FULL_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [GSYM LEFT_EXISTS_AND_THM] >>
   Q.EXISTS_TAC `1` >> ASM_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [dropWhile_MAP, combinTheory.o_DEF] >>

Q.SUBGOAL_THEN `(SUC (PRE (LENGTH (dropWhile (\b. ~b) v)))) = (LENGTH (dropWhile (\b. ~b) v))`
  SUBST1_TAC >- (
  Cases_on `dropWhile (\b. ~b) v` >> SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [listTheory.dropWhile_eq_nil, listTheory.EVERY_MEM]
) >>
POP_ASSUM (K ALL_TAC) >>

SIMP_TAC list_ss [fixwidth_def, LET_DEF, rich_listTheory.LENGTH_LASTN,
  listTheory.LENGTH_dropWhile_LESS_EQ] >>
COND_CASES_TAC >| [
  SIMP_TAC list_ss [zero_extend_def, listTheory.PAD_LEFT,
    GSYM rich_listTheory.REPLICATE_GENLIST,
    rich_listTheory.LENGTH_LASTN, listTheory.LENGTH_dropWhile_LESS_EQ] >>
  POP_ASSUM (K ALL_TAC) >>
  Induct_on `v` >- SIMP_TAC list_ss [rich_listTheory.REPLICATE, rich_listTheory.LASTN] >>
  Cases >- (
    SIMP_TAC list_ss [rich_listTheory.LASTN_CONS, rich_listTheory.REPLICATE] >>
    `SUC (LENGTH v) = LENGTH (T::v)` by SIMP_TAC list_ss [] >>
    ASM_REWRITE_TAC[rich_listTheory.LASTN_LENGTH_ID]
  ) >>

  `LENGTH (dropWhile (\b. ~b) v) <= LENGTH v` by MATCH_ACCEPT_TAC listTheory.LENGTH_dropWhile_LESS_EQ >>
  ASM_SIMP_TAC list_ss [arithmeticTheory.SUB, rich_listTheory.REPLICATE,
    rich_listTheory.LASTN_CONS],


  `LENGTH (dropWhile (\b. ~b) v) <= LENGTH v` by MATCH_ACCEPT_TAC listTheory.LENGTH_dropWhile_LESS_EQ >>
  `LENGTH (dropWhile (\b. ~b) v) = LENGTH v` by DECIDE_TAC >>
  ASM_SIMP_TAC list_ss [rich_listTheory.LASTN_LENGTH_ID]
]);

val _ = export_theory();
