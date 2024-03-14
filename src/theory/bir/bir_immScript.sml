open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory pred_setTheory listTheory;
open bir_auxiliaryTheory;

val _ = new_theory "bir_imm";

(* ------------------------------------------------------------------------- *)
(*  Immediates                                                               *)
(* ------------------------------------------------------------------------- *)

(* Immediates can be words of various sizes *)
Datatype:
  bir_imm_t =
    Imm1   (bool[1])
  | Imm8   (bool[8])
  | Imm16  (bool[16])
  | Imm32  (bool[32])
  | Imm64  (bool[64])
  | Imm128 (bool[128])
End


(* It is handy to keep track of the size via both a special datatype and a number *)
Datatype:
  bir_immtype_t =
  | Bit1
  | Bit8
  | Bit16
  | Bit32
  | Bit64
  | Bit128
End

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));


Theorem fold_bir_immtype_THM:
  !P. ((P Bit1 /\ P Bit8 /\ P Bit16 /\ P Bit32 /\ P Bit64 /\ P Bit128) <=> (!ty. P ty))
Proof
SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) []
QED


Definition type_of_bir_imm_def:
  (type_of_bir_imm (Imm1  _)  = Bit1) /\
  (type_of_bir_imm (Imm8  _)  = Bit8) /\
  (type_of_bir_imm (Imm16 _)  = Bit16) /\
  (type_of_bir_imm (Imm32 _)  = Bit32) /\
  (type_of_bir_imm (Imm64 _)  = Bit64) /\
  (type_of_bir_imm (Imm128 _) = Bit128)
End

Definition size_of_bir_immtype_def:
  (size_of_bir_immtype Bit1   = 1) /\
  (size_of_bir_immtype Bit8   = 8) /\
  (size_of_bir_immtype Bit16  = 16) /\
  (size_of_bir_immtype Bit32  = 32) /\
  (size_of_bir_immtype Bit64  = 64) /\
  (size_of_bir_immtype Bit128 = 128)
End

Definition bir_immtype_of_size_def:
  bir_immtype_of_size n = (
         if n = 1   then SOME Bit1
    else if n = 8   then SOME Bit8
    else if n = 16  then SOME Bit16
    else if n = 32  then SOME Bit32
    else if n = 64  then SOME Bit64
    else if n = 128 then SOME Bit128
    else NONE)
End

Definition is_valid_bir_immtype_size_def:
  is_valid_bir_immtype_size n = ?b. n = size_of_bir_immtype b
End

(* A few sanity checks *)
Theorem size_of_bir_immtype_INJ:
  !b1 b2. (size_of_bir_immtype b1 = size_of_bir_immtype b2) <=> (b1 = b2)
Proof
Cases >> Cases >> SIMP_TAC (std_ss++bir_imm_ss) [size_of_bir_immtype_def]
QED

Theorem size_of_bir_immtype_NEQ_0:
  !b. size_of_bir_immtype b <> 0
Proof
Cases >> SIMP_TAC arith_ss [size_of_bir_immtype_def]
QED

val is_valid_bir_immtype_size_REWRS = save_thm ("is_valid_bir_immtype_size_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [size_of_bir_immtype_def] is_valid_bir_immtype_size_def);


Theorem size_of_bir_immtype_EQ_REWRS0[local]:
  !ty n. is_valid_bir_immtype_size n ==>
           ((size_of_bir_immtype ty = n) <=> (ty = THE (bir_immtype_of_size n)))
Proof
Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [is_valid_bir_immtype_size_REWRS, DISJ_IMP_THM, FORALL_AND_THM,
    bir_immtype_of_size_def, size_of_bir_immtype_def]
)
QED

val size_of_bir_immtype_EQ_REWRS = save_thm("size_of_bir_immtype_EQ_REWRS",
  SIMP_RULE std_ss [size_of_bir_immtype_def, is_valid_bir_immtype_size_REWRS, DISJ_IMP_THM,
    FORALL_AND_THM, bir_immtype_of_size_def]
    size_of_bir_immtype_EQ_REWRS0);

val is_valid_bir_immtype_size_IMP = save_thm ("is_valid_bir_immtype_size_IMP",
  snd (EQ_IMP_RULE (SPEC_ALL is_valid_bir_immtype_size_REWRS)));

Theorem is_valid_bir_immtype_size_IS_SOME:
  !n. is_valid_bir_immtype_size n <=> IS_SOME (bir_immtype_of_size n)
Proof
SIMP_TAC std_ss [is_valid_bir_immtype_size_REWRS, bir_immtype_of_size_def] >>
METIS_TAC[optionTheory.IS_SOME_DEF]
QED

Theorem bir_immtype_of_num_inv:
  (!brt. bir_immtype_of_size (size_of_bir_immtype brt) = SOME brt) /\
    (!n brt. (bir_immtype_of_size n = SOME brt) ==>
             (size_of_bir_immtype brt = n))
Proof
REPEAT CONJ_TAC >| [
  Cases >> SIMP_TAC std_ss [size_of_bir_immtype_def, bir_immtype_of_size_def],

  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_immtype_of_size_def, DISJ_IMP_THM, FORALL_AND_THM,
    COND_EXPAND_OR, LEFT_AND_OVER_OR, size_of_bir_immtype_def]
]
QED


val bir_immtype_of_size_REWRS_SOME = save_thm ("bir_immtype_of_size_REWRS_SOME",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``])
            [size_of_bir_immtype_def] (CONJUNCT1 bir_immtype_of_num_inv));


val bir_immtype_of_size_REWRS_NONE = save_thm ("bir_immtype_of_size_REWRS_NONE",
let
Theorem thm_none_aux[local]:
  !n. ~(is_valid_bir_immtype_size n) ==> (bir_immtype_of_size n = NONE)
Proof
SIMP_TAC std_ss [is_valid_bir_immtype_size_IS_SOME]
QED
  val thm_none = SIMP_RULE std_ss [is_valid_bir_immtype_size_REWRS] thm_none_aux
in
  thm_none
end);


(* ------------------------------------------------------------------------- *)
(*  Transformation between immediates and numbers                            *)
(* ------------------------------------------------------------------------- *)
Definition b2n_def:
  (b2n ( Imm1   w ) = w2n w) /\
  (b2n ( Imm8   w ) = w2n w) /\
  (b2n ( Imm16  w ) = w2n w) /\
  (b2n ( Imm32  w ) = w2n w) /\
  (b2n ( Imm64  w ) = w2n w) /\
  (b2n ( Imm128 w ) = w2n w)
End

Definition n2bs_def:
  (n2bs n Bit1   = Imm1   (n2w n)) /\
  (n2bs n Bit8   = Imm8   (n2w n)) /\
  (n2bs n Bit16  = Imm16  (n2w n)) /\
  (n2bs n Bit32  = Imm32  (n2w n)) /\
  (n2bs n Bit64  = Imm64  (n2w n)) /\
  (n2bs n Bit128 = Imm128 (n2w n))
End

Definition n2b_1_def:
  n2b_1  n  = n2bs n Bit1
End
Definition n2b_8_def:
  n2b_8  n  = n2bs n Bit8
End
Definition n2b_16_def:
  n2b_16 n  = n2bs n Bit16
End
Definition n2b_32_def:
  n2b_32 n  = n2bs n Bit32
End
Definition n2b_64_def:
  n2b_64 n  = n2bs n Bit64
End
Definition n2b_128_def:
  n2b_128 n = n2bs n Bit128
End

val _ = add_bare_numeral_form (#"y", SOME "n2b_128");
val _ = add_bare_numeral_form (#"x", SOME "n2b_64");
val _ = add_bare_numeral_form (#"e", SOME "n2b_32");
val _ = add_bare_numeral_form (#"d", SOME "n2b_16");
val _ = add_bare_numeral_form (#"c", SOME "n2b_8");
val _ = add_bare_numeral_form (#"b", SOME "n2b_1");

val n2b_fixed_DEFS = save_thm ("n2b_fixed_DEFS",
    LIST_CONJ [n2b_1_def, n2b_8_def, n2b_16_def, n2b_32_def, n2b_64_def, n2b_128_def]);

Theorem b2n_n2bs:
  !bt n. b2n (n2bs n bt) = MOD_2EXP (size_of_bir_immtype bt) n
Proof
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2n_def, n2bs_def, w2n_n2w,
    size_of_bir_immtype_def, bitTheory.MOD_2EXP_def]
)
QED

Theorem b2n_n2b_fixed:
  (!n. b2n (n2b_1 n)  = n MOD 2) /\
    (!n. b2n (n2b_8 n)  = n MOD 2**8) /\
    (!n. b2n (n2b_16 n) = n MOD 2**16) /\
    (!n. b2n (n2b_32 n) = n MOD 2**32) /\
    (!n. b2n (n2b_64 n) = n MOD 2**64) /\
    (!n. b2n (n2b_128 n) = n MOD 2**128) /\
    (!n bt. b2n (n2bs n bt) = n MOD 2**(size_of_bir_immtype bt))
Proof
SIMP_TAC std_ss [n2b_fixed_DEFS, b2n_n2bs, size_of_bir_immtype_def,
  bitTheory.MOD_2EXP_def]
QED

val b2n_n2w_REWRS = save_thm ("b2n_n2w_REWRS",
SIMP_RULE std_ss [n2b_fixed_DEFS, n2bs_def] (
prove (``(!n. b2n (n2b_1 n)  = n MOD 2) /\
    (!n. b2n (n2b_8 n)  = n MOD 2**8) /\
    (!n. b2n (n2b_16 n) = n MOD 2**16) /\
    (!n. b2n (n2b_32 n) = n MOD 2**32) /\
    (!n. b2n (n2b_64 n) = n MOD 2**64) /\
    (!n. b2n (n2b_128 n) = n MOD 2**128)``, SIMP_TAC std_ss [b2n_n2b_fixed])))


Theorem n2bs_b2n:
  !b s. (s = type_of_bir_imm b) ==> (n2bs (b2n b) s = b)
Proof
Cases >> (
  SIMP_TAC std_ss [b2n_def, n2bs_def, type_of_bir_imm_def, n2w_w2n]
)
QED

Theorem w2n_lt_trans[local]:
  !w:'a word. dimword (:'a) <= m ==> (w2n w < m)
Proof
METIS_TAC[w2n_lt, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem b2n_lt:
  !b. b2n b < 2 ** (size_of_bir_immtype (type_of_bir_imm b))
Proof
Cases >> (
  SIMP_TAC std_ss [b2n_def, type_of_bir_imm_def, size_of_bir_immtype_def] >>
  MATCH_MP_TAC w2n_lt_trans >>
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
)
QED


val b2n_lt_REWRS = save_thm ("b2n_lt_REWRS",
SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_imm_t``]) [
  type_of_bir_imm_def, size_of_bir_immtype_def] b2n_lt);


Theorem b2n_MOD_2EXP:
  !i n. ((size_of_bir_immtype (type_of_bir_imm i)) = n) ==>
          (MOD_2EXP n (b2n i) = b2n i)
Proof
SIMP_TAC std_ss [bitTheory.MOD_2EXP_def, b2n_lt]
QED


Theorem type_of_n2bs:
  !s n. type_of_bir_imm (n2bs n s) = s
Proof
Cases >> SIMP_TAC std_ss [n2bs_def, type_of_bir_imm_def]
QED


val type_of_n2b_fixed = save_thm ("type_of_n2b_fixed",
SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
  GSYM n2b_fixed_DEFS] type_of_n2bs);


Theorem type_of_bir_imm_n2bs_INTRO:
  !s b. (type_of_bir_imm b = s) <=> (?n. b = n2bs n s)
Proof
REPEAT GEN_TAC >> EQ_TAC >> STRIP_TAC >| [
  Q.EXISTS_TAC `b2n b` >>
  ASM_SIMP_TAC std_ss [n2bs_b2n],

  ASM_SIMP_TAC std_ss [type_of_n2bs]
]
QED


Theorem n2bs_MOD_size_of_bir_immtype:
  !s n. n2bs (MOD_2EXP (size_of_bir_immtype s) n) s = n2bs n s
Proof
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `n2bs n s = n2bs (b2n (n2bs n s)) s` SUBST1_TAC >- METIS_TAC[n2bs_b2n, type_of_n2bs] >>
SIMP_TAC std_ss [b2n_n2bs]
QED



Theorem n2bs_CASE:
  !b. (?n. (n < 2 ** (size_of_bir_immtype (type_of_bir_imm b))) /\
             (b = n2bs n (type_of_bir_imm b)))
Proof
REPEAT STRIP_TAC >>
`?n. b = n2bs n (type_of_bir_imm b)` by METIS_TAC[type_of_bir_imm_n2bs_INTRO] >>
Q.EXISTS_TAC `(MOD_2EXP (size_of_bir_immtype (type_of_bir_imm b)) n)` >>
ASM_SIMP_TAC std_ss [n2bs_MOD_size_of_bir_immtype, bitTheory.MOD_2EXP_def]
QED



(* ---------------------------- *)
(*  finiteness of the datatypes *)
(* ---------------------------- *)

Definition bir_immtype_t_LIST_def:
  bir_immtype_t_LIST = ^(listSyntax.mk_list (TypeBase.constructors_of ``:bir_immtype_t``, ``:bir_immtype_t``))
End


Theorem bir_immtype_t_LIST_THM:
  !s. MEM s bir_immtype_t_LIST
Proof
Cases >> SIMP_TAC list_ss [bir_immtype_t_LIST_def]
QED

Theorem bir_immtype_t_UNIV_SPEC:
  (UNIV:bir_immtype_t set) = set bir_immtype_t_LIST
Proof
SIMP_TAC list_ss [EXTENSION, bir_immtype_t_LIST_THM, IN_UNIV]
QED

Theorem bir_immtype_t_FINITE_UNIV:
  FINITE (UNIV : (bir_immtype_t set))
Proof
REWRITE_TAC[bir_immtype_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]
QED


Definition bir_imm_t_LIST_def:
  bir_imm_t_LIST =
     FLAT (MAP (\s. MAP (\n. n2bs n s) (COUNT_LIST (2 ** size_of_bir_immtype s))) bir_immtype_t_LIST)
End


Theorem bir_imm_t_LIST_THM:
  !i. MEM i bir_imm_t_LIST
Proof
SIMP_TAC list_ss [bir_imm_t_LIST_def, MEM_FLAT, MEM_MAP,
  PULL_EXISTS, rich_listTheory.MEM_COUNT_LIST, bir_immtype_t_LIST_THM] >>
METIS_TAC [n2bs_CASE]
QED


Theorem bir_imm_t_UNIV_SPEC:
  (UNIV:bir_imm_t set) = set bir_imm_t_LIST
Proof
SIMP_TAC list_ss [EXTENSION, bir_imm_t_LIST_THM, IN_UNIV]
QED

Theorem bir_imm_t_FINITE_UNIV:
  FINITE (UNIV : (bir_imm_t set))
Proof
REWRITE_TAC[bir_imm_t_UNIV_SPEC, listTheory.FINITE_LIST_TO_SET]
QED


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and words                              *)
(* ------------------------------------------------------------------------- *)

Definition b2w_def:
  b2w bi = n2w (b2n bi)
End

Theorem b2w_REWRS:
  (!w. (b2w ( Imm1  w )  = w2w w)) /\
  (!w. (b2w ( Imm8  w )  = w2w w)) /\
  (!w. (b2w ( Imm16 w )  = w2w w)) /\
  (!w. (b2w ( Imm32 w )  = w2w w)) /\
  (!w. (b2w ( Imm64 w )  = w2w w)) /\
  (!w. (b2w ( Imm128 w ) = w2w w))
Proof
REWRITE_TAC[b2w_def, b2n_def, w2w_def]
QED

Definition w2bs_def:
  w2bs w s = n2bs (w2n w) s
End

Theorem w2bs_REWRS:
  (!w. (w2bs w Bit1   = Imm1   (w2w w))) /\
  (!w. (w2bs w Bit8   = Imm8   (w2w w))) /\
  (!w. (w2bs w Bit16  = Imm16  (w2w w))) /\
  (!w. (w2bs w Bit32  = Imm32  (w2w w))) /\
  (!w. (w2bs w Bit64  = Imm64  (w2w w))) /\
  (!w. (w2bs w Bit128 = Imm128 (w2w w)))
Proof
SIMP_TAC std_ss [w2bs_def,n2bs_def, w2w_def]
QED


Theorem w2bs_b2w:
  !b s. ((s = type_of_bir_imm b) /\ size_of_bir_immtype (type_of_bir_imm b) <= dimindex (:'a)) ==>
          (w2bs ((b2w b):'a word) s = b)
Proof
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
ASM_SIMP_TAC std_ss [n2bs_b2n]
QED

Theorem type_of_w2bs:
  !s w. type_of_bir_imm (w2bs w s) = s
Proof
SIMP_TAC std_ss [w2bs_def, type_of_n2bs]
QED


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and bool                               *)
(* ------------------------------------------------------------------------- *)

Definition b2bool_def:
  b2bool bi = (b2n bi <> 0)
End

val b2bool_REWRS = save_thm ("b2bool_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_imm_t``]) [
    b2n_def, w2n_eq_0]
    b2bool_def);

Definition bool2w_def:
  bool2w b = (if b then 1w else 0w):word1
End
Definition bool2b_def:
  bool2b b = Imm1 (bool2w b)
End

Theorem bool2b_inv:
  (!b. (b2bool (bool2b b) = b)) /\
    (!w. ((bool2b (b2bool (Imm1 w))) = Imm1 w))
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss)
  [b2bool_def, bool2b_def, b2n_def, w2n_eq_0, bool2w_def] >>
Cases >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [] >>
`(n = 0) \/ (n = 1)` by DECIDE_TAC >> (
  ASM_SIMP_TAC std_ss []
)
QED

Theorem type_of_bool2b:
  !b. type_of_bir_imm (bool2b b) = Bit1
Proof
SIMP_TAC std_ss [bool2b_def, type_of_bir_imm_def]
QED

Theorem bool2w_EQ_ELIMS:
  (!b. (bool2w b = 1w) <=> b) /\
    (!b. (bool2w b = 0w) <=> ~b) /\
    (!b. (1w = bool2w b) <=> b) /\
    (!b. (0w = bool2w b) <=> ~b)
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++bir_imm_ss++wordsLib.WORD_ss) [bool2w_def]
QED

Theorem bool2w_11:
  !b1 b2. (bool2w b1 = bool2w b2) <=> (b1 = b2)
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++bir_imm_ss++wordsLib.WORD_ss) [bool2w_def]
QED


Theorem bool2b_EQ_IMM1_ELIMS:
  (!b. (bool2b b = Imm1 1w) <=> b) /\
    (!b. (bool2b b = Imm1 0w) <=> ~b) /\
    (!b. (Imm1 1w = bool2b b) <=> b) /\
    (!b. (Imm1 0w = bool2b b) <=> ~b)
Proof
SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def, bool2w_EQ_ELIMS]
QED


Theorem bool2b_NEQ_IMM_ELIMS_AUX[local]:
  (!i b. (type_of_bir_imm i <> Bit1) ==> (bool2b b <> i))
Proof
Cases >> SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def, type_of_bir_imm_def]
QED

val bool2b_NEQ_IMM_ELIMS = save_thm ("bool2b_NEQ_IMM_ELIMS",
  SIMP_RULE (std_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_imm_t``]) [
    type_of_bir_imm_def]
    bool2b_NEQ_IMM_ELIMS_AUX);

Theorem bool2b_11:
  !b1 b2. (bool2b b1 = bool2b b2) <=> (b1 = b2)
Proof
SIMP_TAC (std_ss++bir_imm_ss) [bool2b_def, bool2w_11]
QED


(* ------------------------------------------------------------------------- *)
(*  transformation between immediates and bitstrings                         *)
(* ------------------------------------------------------------------------- *)

Definition v2bs_def:
  v2bs v s = n2bs (v2n v) s
End

val v2bs_REWRS = save_thm ("v2bs_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_immtype_t``]) [
    n2bs_def, FORALL_AND_THM, n2w_v2n] v2bs_def);

Definition b2v_def:
  (b2v ( Imm1   w ) = w2v w) /\
  (b2v ( Imm8   w ) = w2v w) /\
  (b2v ( Imm16  w ) = w2v w) /\
  (b2v ( Imm32  w ) = w2v w) /\
  (b2v ( Imm64  w ) = w2v w) /\
  (b2v ( Imm128 w ) = w2v w)
End

Theorem b2v_LENGTH:
  !r. LENGTH (b2v r) = size_of_bir_immtype (
        type_of_bir_imm r)
Proof
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2v_def, type_of_bir_imm_def,
    size_of_bir_immtype_def, length_w2v]
)
QED

Theorem v2n_w2v:
  !w:'a word. (v2n (w2v w) = w2n w)
Proof
GEN_TAC >>
bitstringLib.Cases_on_v2w `w` >>
ASM_SIMP_TAC std_ss [w2n_v2w, w2v_v2w,
  fixwidth_id_imp, bitTheory.MOD_2EXP_def, v2n_lt]
QED

Theorem v2n_b2v:
  !r. v2n (b2v r) = b2n r
Proof
Cases >> (
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [b2n_def, b2v_def, v2n_w2v]
)
QED


Theorem type_of_v2bs:
  !s v. type_of_bir_imm (v2bs v s) = s
Proof
SIMP_TAC std_ss [v2bs_def, type_of_n2bs]
QED


Theorem v2w_fixwidth_imp:
  !v w. ((dimindex (:'a)) <= w) ==>
          ((v2w (fixwidth w v) = ((v2w v):'a word)))
Proof
REPEAT STRIP_TAC >>
`fixwidth (dimindex (:'a)) (fixwidth w v) = fixwidth (dimindex (:'a)) v` by (
  METIS_TAC[fixwidth_fixwidth_le]
) >>
METIS_TAC[v2w_fixwidth]
QED


Theorem v2bs_fixwidth:
  !v vty w. (size_of_bir_immtype vty <= w) ==>
            (v2bs (fixwidth w v) vty = v2bs v vty)
Proof
GEN_TAC >> Cases >>
SIMP_TAC (std_ss++wordsLib.WORD_ss) [v2bs_def, n2bs_def, n2w_v2n,
  v2w_fixwidth_imp, size_of_bir_immtype_def]
QED

Theorem v2bs_n2v:
  !n. v2bs (n2v n) = n2bs n
Proof
SIMP_TAC std_ss [FUN_EQ_THM, v2bs_def, v2n_n2v]
QED



Theorem n2v_v2n:
  !v n. (LENGTH v = n) ==> (fixwidth n (n2v (v2n v)) = v)
Proof
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
]
QED



val _ = export_theory();
