open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_exp_liftingTheory
open arm8_stepTheory
open bir_lifter_general_auxTheory;

open bir_interval_expTheory bir_extra_expsTheory
open bitstringTheory
open bir_exp_immTheory

(* In order to produce decent BIR code from step theorems,
   the concepts described by the step theorems need to be
   made very explicit. This is mostly due to the fact that
   the step theorems result from partially evaluating the
   machine definitions. However, translating a partial evaluation
   literally is often more cumbersome that translating the abstract
   concept.

   The work for the conditional execution flags is so extensive, that
   it is handled in bir_nzcv_introsScript.sml. Moreover, this theory
   only contains the arm8 specific stuff. *)

val _ = new_theory "bir_arm8_extras";


(*********************************)
(* Some silly auxiliary rewrites *)
(*********************************)

val shift_neg1w_rewr = prove (
``(-1w << n):'a word = -(n2w (2**n))``,
METIS_TAC[WORD_NEG_MUL, WORD_MUL_LSL, WORD_MULT_COMM])

val shift_neg1w_rewr2 = prove (
``(-1w << n):'a word = (n2w (dimword (:'a) - 2 ** n MOD dimword (:'a)))``,

SIMP_TAC std_ss [shift_neg1w_rewr] >>
SIMP_TAC std_ss [word_2comp_n2w]);


val shift_neg1w_rewr3 = prove (
``~(-1w << n):'a word =
n2w
  (dimword (:'a) -
   ((dimword (:'a) - 2 ** n MOD dimword (:'a)) MOD dimword (:'a) + 1))``,
SIMP_TAC arith_ss [shift_neg1w_rewr2, word_1comp_n2w]);


val SHIFT_ZERO_bv = prove (
  ``(!a. a <<~ 0w = a) /\ (!a. a >>~ 0w = a) /\ (!a. a >>>~ 0w = a) /\
    (!a. a #<<~ 0w = a) /\ (!a. a #>>~ 0w = a)``,

  SIMP_TAC arith_ss [SHIFT_ZERO, word_lsl_bv_def, w2n_n2w, ZERO_LT_dimword,
    word_lsr_bv_def, word_asr_bv_def, word_rol_bv_def, word_ror_bv_def]);

val MOD_DIMINDEX_DIMWORD = prove (
``!m. ((m MOD dimindex (:'a)) MOD dimword (:'a)) =
      (m MOD dimindex (:'a))``,
GEN_TAC >>
`m MOD dimindex (:'a) < dimindex (:'a)` by
  ASM_SIMP_TAC arith_ss [DIMINDEX_GT_0] >>
`m MOD dimindex (:'a) < dimword (:'a)` by
  METIS_TAC [dimindex_lt_dimword, arithmeticTheory.LESS_TRANS] >>
ASM_SIMP_TAC arith_ss []);


(***********************)
(* Evaluate "w && -1w" *)
(***********************)

val arm8_and_neg_1w_GEN = prove (``
  (!w:'a word. (w && -1w) = w) /\
  (!w:'a word. (-1w && w) = w)``,

SIMP_TAC std_ss [WORD_NEG_1, WORD_AND_CLAUSES]);


val arm8_and_neg_1w_FOLDS = save_thm ("arm8_and_neg_1w_FOLDS",
let
  fun inst wty =
    INST_TYPE [``:'a`` |-> wty] arm8_and_neg_1w_GEN;

  val thm1 = LIST_CONJ ([inst ``:32``, inst ``:64``, inst ``:16``])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_2comp_n2w] thm1
in
  thm2
end)



(***********************)
(* FOLD "w <<~ n2w x"  *)
(***********************)

val arm8_lsl_FOLD_GEN = prove (
``!n w.  n < dimword (:'a) ==>
(((((w:'a word) #>> (dimindex (:'a) - n)) && (-1w << n))) =
 (w <<~ n2w n))``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [word_and_def, fcpTheory.FCP_BETA,
  word_lsl_def, WORD_NEG_1_T, word_ror_def, word_lsl_bv_def, w2n_n2w,
  dimindex_lt_dimword] >>
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `i + dimindex (:'a) - n = dimindex (:'a) + (i - n)` SUBST1_TAC >- DECIDE_TAC >>
SIMP_TAC std_ss [DIMINDEX_GT_0, arithmeticTheory.ADD_MODULUS] >>
ASM_SIMP_TAC arith_ss []);


val arm8_lsl_FOLDS = save_thm ("arm8_lsl_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsl_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 32, inst ``:64`` 64, inst ``:16`` 16])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2] thm1
in
  thm2
end)





val arm8_lsl_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 << (w2n w2 MOD dimindex (:'a))) = (w1 <<~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_lsl_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);


val arm8_lsl_no_imm_FOLDS = save_thm ("arm8_lsl_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsl_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end
  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)



(***********************)
(* FOLD "w >>>~ n2w x" *)
(***********************)

val arm8_lsr_FOLD_GEN = prove (
``!n w.  n < dimword (:'a) ==>
(((((w:'a word) #>> n) && ~(-1w << (dimindex (:'a) - n)))) =
 (w >>>~ n2w n))``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss) [word_and_def, fcpTheory.FCP_BETA,
  word_lsr_def, WORD_NEG_1_T, word_ror_def, word_lsr_bv_def, w2n_n2w,
  dimindex_lt_dimword, word_lsl_def, arithmeticTheory.NOT_LESS_EQUAL,
  word_1comp_def]);


val arm8_lsr_FOLDS = save_thm ("arm8_lsr_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsr_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 32, inst ``:64`` 64, inst ``:16`` 16])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)



val arm8_lsr_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 >>> (w2n w2 MOD dimindex (:'a))) = (w1 >>>~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_lsr_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);




val arm8_lsr_no_imm_FOLDS = save_thm ("arm8_lsr_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_lsr_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end

  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end)





(**********************)
(* FOLD "w >>~ n2w x" *)
(**********************)

val arm8_asr_FOLD_GEN = prove (
``!n (w:'a word).  n < dimindex (:'a) ==>

((((if word_bit (dimindex (:'a) - 1) w then -1w else 0w) &&
   ~~(-1w << (dimindex (:'a) - n))) || (w >>>~ n2w n)) =
(w >>~ n2w n))
``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
`dimindex (:'a) < dimword (:'a)` by METIS_TAC[dimindex_lt_dimword] >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [word_or_def, fcpTheory.FCP_BETA,
  word_and_def, WORD_NEG_1_T, word_0, word_lsl_def, word_asr_def,
  word_asr_bv_def, word_lsr_bv_def, w2n_n2w, GSYM word_msb,
  word_lsr_def, word_1comp_def, word_msb_def]);


val arm8_asr_FOLDS = save_thm ("arm8_asr_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_asr_FOLD_GEN
  in
     (List.tabulate (n, fn i => SPEC (numSyntax.term_of_int i) thm0))
  end

  val thm1 = LIST_CONJ (flatten [inst ``:32`` 33, inst ``:64`` 65, inst ``:16`` 17])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr3] thm1
  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [WORD_NEG_1, word_T_def, UINT_MAX_def,
    SHIFT_ZERO_bv] thm2
in
  thm3
end);



val arm8_asr_FOLD_NO_IMM_GEN = prove (
``!(n:num) (w1:'a word) (w2:'a word). (2 ** n = (dimindex (:'a))) ==>
  ((w1 >> (w2n w2 MOD dimindex (:'a))) = (w1 >>~ (w2 && n2w (2 ** n - 1))))``,

REPEAT STRIP_TAC >>
Cases_on `w2` >> rename1 `m < dimword (:'a)` >>
ASM_SIMP_TAC arith_ss [WORD_AND_EXP_SUB1, word_asr_bv_def, w2n_n2w,
  MOD_DIMINDEX_DIMWORD]);


val arm8_asr_no_imm_FOLDS = save_thm ("arm8_asr_no_imm_FOLDS",
let
  fun inst wty n = let
    val thm0 = INST_TYPE [``:'a`` |-> wty] arm8_asr_FOLD_NO_IMM_GEN
    val thm1 = SPEC (numSyntax.term_of_int n) thm0
  in
    thm1
  end

  val thm1 = LIST_CONJ ([inst ``:32`` 5, inst ``:64`` 6, inst ``:16`` 4])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr2, word_1comp_n2w] thm1
in
  thm2
end);



(****************)
(* FOLD for ror *)
(****************)

val arm8_ror_MOD_FOLDS = save_thm ("arm8_ror_MOD_FOLDS",
let
  val thms0 = map (fn ty => INST_TYPE [``:'a`` |-> ty] wordsTheory.ROR_MOD) [``:8``, ``:16``, ``:32``, ``:64``]
  val thm1 = LIST_CONJ thms0
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm1
in thm2 end);


(*****************)
(* FOLD for extr *)
(*****************)

val arm8_extr_FOLD0 = prove (
``!(w1:'a word) (w2:'a word) n.
   (MEM n (COUNT_LIST (dimindex(:'a)))) ==> (
   (v2w (BUTLASTN n (w2v w1 ++ w2v w2))): 'a word =
   word_shift_extract w1 w2 n)``,

ONCE_REWRITE_TAC[fcpTheory.CART_EQ] >>
REWRITE_TAC[bitstringTheory.word_index_v2w, rich_listTheory.MEM_COUNT_LIST] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [word_shift_extract_def,
  word_or_def, fcpTheory.FCP_BETA, word_lsl_def, word_lsr_def] >>
ASM_SIMP_TAC list_ss [rich_listTheory.LENGTH_BUTLASTN,
    bitstringTheory.testbit_el, length_w2v, rich_listTheory.BUTLASTN_def,
    listTheory.EL_REVERSE, GSYM arithmeticTheory.ADD1] >>
Q.SUBGOAL_THEN `PRE ((i + SUC n) - n) = i` SUBST1_TAC >- DECIDE_TAC >>

ASM_SIMP_TAC list_ss [listTheory.REVERSE_APPEND, rich_listTheory.DROP_APPEND1,
  length_w2v, listTheory.EL_APPEND_EQN, listTheory.EL_REVERSE,
  el_w2v, rich_listTheory.EL_DROP, GSYM arithmeticTheory.ADD1] >>
Cases_on ` i < dimindex (:'a) - n` >- (
  ASM_SIMP_TAC arith_ss [] >>
  AP_TERM_TAC >>
  DECIDE_TAC
) >- (
  ASM_SIMP_TAC arith_ss [] >>
  AP_TERM_TAC >>
  DECIDE_TAC
));


val arm8_extr_FOLD1 = prove (
``!(w1:'a word) (w2:'a word) n.
   (dimindex (:'a) < dimindex (:'b)) ==>
   (MEM n (COUNT_LIST (dimindex(:'a)))) ==> (
   (v2w (LASTN (dimindex (:'a)) ((BUTLASTN n (w2v w1 ++ w2v w2))))): 'b word =
   w2w (word_shift_extract w1 w2 n))``,

ONCE_REWRITE_TAC[fcpTheory.CART_EQ] >>
REWRITE_TAC[bitstringTheory.word_index_v2w, rich_listTheory.MEM_COUNT_LIST] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss) [word_shift_extract_def,
  word_or_def, fcpTheory.FCP_BETA, word_lsl_def, word_lsr_def, w2w] >>
ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [rich_listTheory.LENGTH_BUTLASTN,
    bir_auxiliaryTheory.testbit_el_iff, length_w2v, rich_listTheory.BUTLASTN_def,
    listTheory.EL_REVERSE, GSYM arithmeticTheory.ADD1, rich_listTheory.LASTN_REVERSE,
    rich_listTheory.EL_TAKE] >>
STRIP_TAC >>
ASM_SIMP_TAC list_ss [listTheory.REVERSE_APPEND, rich_listTheory.DROP_APPEND1,
  length_w2v, listTheory.EL_APPEND_EQN, listTheory.EL_REVERSE,
  el_w2v, rich_listTheory.EL_DROP, GSYM arithmeticTheory.ADD1] >>

Cases_on ` i + n < dimindex (:'a)` >- (
  ASM_SIMP_TAC arith_ss [] >>
  AP_TERM_TAC >>
  DECIDE_TAC
) >- (
  ASM_SIMP_TAC arith_ss [] >>
  AP_TERM_TAC >>
  DECIDE_TAC
));


val arm8_extr_FOLDS = save_thm ("arm8_extr_FOLDS",
let
  val thm0a = INST_TYPE [``:'a`` |-> ``:64``] arm8_extr_FOLD0
  val thm0b = INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:64``] arm8_extr_FOLD1

  val thm1 = CONJ thm0a thm0b
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, w2v_def,
    listTheory.GENLIST_GENLIST_AUX, listTheory.GENLIST_AUX_compute, listTheory.APPEND] thm1
  val thm3 = SIMP_RULE std_ss [rich_listTheory.BUTLASTN_def,rich_listTheory.LASTN_def,
    listTheory.REVERSE_REVERSE] thm2
  val thm4 = SIMP_RULE std_ss [listTheory.REVERSE_REV, listTheory.REV_DEF] thm3
  val thm5 = SIMP_RULE std_ss [listTheory.MEM, DISJ_IMP_THM, FORALL_AND_THM,
    listTheory.DROP_compute, listTheory.TAKE_compute, listTheory.REV_DEF] thm4
  val thm6 = SIMP_RULE (arith_ss++wordsLib.SIZES_ss) [word_shift_extract_LIMIT, word_shift_extract_0] thm5

in thm6 end);



(**************************)
(* Sign cast 32 -> 64 bit *)
(**************************)

val arm8_sxtw_FOLD_GEN = prove (
``!w.

  ((if word_bit (dimindex (:'a) - 1) (w:'b word) then (-1w) else (0w:'b word)) &&
    ~~((-1w << (dimindex (:'a)))) || (w && ~(-1w << (dimindex (:'a)))) && ~((-1w << (dimindex (:'a))))) =
  sw2sw ((w2w w):'a word)``,


REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
`dimindex (:'a) <> 0` by METIS_TAC [DIMINDEX_GT_0, prim_recTheory.LESS_REFL] >>
Cases_on `w` >>

ASM_SIMP_TAC (arith_ss++boolSimps.CONJ_ss) [word_or_def, fcpTheory.FCP_BETA,
  word_and_def, word_1comp_def, word_lsl_def, WORD_NEG_1_T,
  sw2sw_def, word_index, bitTheory.BIT_SIGN_EXTEND, DIMINDEX_GT_0,
  w2w_def, w2n_n2w, GSYM dimword_def, arithmeticTheory.MOD_MOD,
  ZERO_LT_dimword, w2n_lt, wordsTheory.MOD_DIMINDEX, bitTheory.BIT_OF_BITS_THM,
  word_bit_def] >>
REPEAT STRIP_TAC >>
Cases_on `BIT (dimindex (:'a) - 1) n` >> Cases_on `dimindex (:'a) <= dimindex (:'b)` >> (
  ASM_SIMP_TAC arith_ss [WORD_NEG_1_T, word_0, arithmeticTheory.NOT_LESS_EQUAL] >>
  METIS_TAC[arithmeticTheory.NOT_LESS_EQUAL]
));



val arm8_sxtw_FOLDS = save_thm ("arm8_sxtw_FOLDS",
let
  fun inst wty1 wty2 = let
    val thm0 = INST_TYPE [``:'a`` |-> wty1, ``:'b`` |-> wty2] arm8_sxtw_FOLD_GEN
  in
    thm0
  end

  val thm1 = LIST_CONJ ([inst ``:32`` ``:64``, inst ``:16`` ``:64``, inst ``:8`` ``:64``, inst ``:16`` ``:32``])

  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [shift_neg1w_rewr3,
    WORD_NEG_1, word_T_def] thm1
in
  thm2
end);



(*************************)
(* Lifting Load for arm8 *)
(*************************)



val arm8_LIFT_LOAD_DWORD = store_thm ("arm8_LIFT_LOAD_DWORD",
``!env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit64)
       (Imm64 (mem_dword ms.MEM va))``,
SIMP_TAC std_ss [mem_dword_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]);


val arm8_LIFT_LOAD_WORD = store_thm ("arm8_LIFT_LOAD_WORD",
``!env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit32)
       (Imm32 (mem_word ms.MEM va))``,
SIMP_TAC std_ss [mem_word_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]);



val arm8_LIFT_LOAD_HALF = store_thm ("arm8_LIFT_LOAD_HALF",
``!env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit16)
       (Imm16 (mem_half ms.MEM va))``,
SIMP_TAC std_ss [mem_half_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]);


val arm8_LIFT_LOAD_BYTE = store_thm ("arm8_LIFT_LOAD_BYTE",
``!env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit8)
       (Imm8 (ms.MEM va))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_is_lifted_imm_exp_LOAD_NO_ENDIAN]);



(******************)
(* Store for arm8 *)
(******************)

val mem_store_dword_def = Define `mem_store_dword (a:word64) (w:word64) (mmap : (word64 -> word8)) =
   (a + 7w =+ (63 >< 56) w)
  ((a + 6w =+ (55 >< 48) w)
  ((a + 5w =+ (47 >< 40) w)
  ((a + 4w =+ (39 >< 32) w)
  ((a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w  =+ (7  >< 0)  w) mmap)))))))`;

val mem_store_word_def = Define `mem_store_word (a:word64) (w:word32) (mmap : (word64 -> word8)) =
   (a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)))`;

val mem_store_half_def = Define `mem_store_half (a:word64) (w:word16) (mmap : (word64 -> word8)) =
   (a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)`;

val mem_store_byte_def = Define `mem_store_byte (a:word64) (w:word8) (mmap : (word64 -> word8)) =
  ((a      =+ w) mmap)`;

val elim_zero_for_def_thm = GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``a + 0w  =+ w``);


val arm8_mem_store_FOLDS = save_thm ("arm8_mem_store_FOLDS",
let
  val thm0 = GSYM mem_store_byte_def
  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM mem_store_byte_def] (GSYM thm)

  val def_THMS_apz = LIST_CONJ [GSYM mem_store_byte_def,
     mk_thm_GEN mem_store_half_def,
     mk_thm_GEN mem_store_word_def,
     mk_thm_GEN mem_store_dword_def];

  val elim_zero_thm = GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``mem_store_byte (a+0w) w mmap``);
  val def_THMS = REWRITE_RULE [elim_zero_thm] def_THMS_apz;

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM mem_store_byte_def] tm))

  val zero_THM0 = mk_zero_thm mem_store_half_def ``mem_store_half a 0w mmap``;
  val zero_THM1 = REWRITE_RULE [zero_THM0] (mk_zero_thm mem_store_word_def ``mem_store_word a 0w mmap``);
  val zero_THM2 = REWRITE_RULE [zero_THM1, zero_THM0] (
     mk_zero_thm mem_store_dword_def ``mem_store_dword a 0w mmap``);

in LIST_CONJ [def_THMS_apz, def_THMS, zero_THM0, zero_THM1, zero_THM2] end);


val arm8_LIFT_STORE_DWORD = store_thm ("arm8_LIFT_STORE_DWORD",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_dword va vv mem_f)``,

SIMP_TAC std_ss [mem_store_dword_def, elim_zero_for_def_thm, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


val arm8_LIFT_STORE_WORD = store_thm ("arm8_LIFT_STORE_WORD",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_word va vv mem_f)``,

SIMP_TAC std_ss [mem_store_word_def, elim_zero_for_def_thm, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


val arm8_LIFT_STORE_HALF = store_thm ("arm8_LIFT_STORE_HALF",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_half va vv mem_f)``,

SIMP_TAC std_ss [mem_store_half_def, elim_zero_for_def_thm, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


val arm8_LIFT_STORE_BYTE = store_thm ("arm8_LIFT_STORE_BYTE",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_byte va vv mem_f)``,

SIMP_TAC std_ss [mem_store_byte_def, bir_is_lifted_mem_exp_STORE_NO_ENDIAN]);

val arm8_LIFT_STORE_DWORD_CHANGE_INTERVAL = store_thm ("arm8_LIFT_STORE_DWORD_CHANGE_INTERVAL",
``!va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 8 (mem_store_dword va vv mem_f) mem_f``,

SIMP_TAC (list_ss++wordsLib.WORD_ss) [mem_store_dword_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]);


val arm8_LIFT_STORE_WORD_CHANGE_INTERVAL = store_thm ("arm8_LIFT_STORE_WORD_CHANGE_INTERVAL",
``!va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 4 (mem_store_word va vv mem_f) mem_f``,

SIMP_TAC (list_ss++wordsLib.WORD_ss) [mem_store_word_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]);

val arm8_LIFT_STORE_HALF_CHANGE_INTERVAL = store_thm ("arm8_LIFT_STORE_HALF_CHANGE_INTERVAL",
``!va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 2 (mem_store_half va vv mem_f) mem_f``,
SIMP_TAC (list_ss++wordsLib.WORD_ss) [mem_store_half_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]);

val arm8_LIFT_STORE_BYTE_CHANGE_INTERVAL = store_thm ("arm8_LIFT_STORE_BYTE_CHANGE_INTERVAL",
``!va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 1 (mem_store_byte va vv mem_f) mem_f``,

SIMP_TAC (list_ss++wordsLib.WORD_ss) [mem_store_byte_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]);


(****************)
(* Add to sub   *)
(****************)

val word_add_to_sub_GEN = store_thm ("word_add_to_sub_GEN",
``!w:'a word n.

   INT_MAX (:'a) < n /\ n < dimword (:'a) ==>
   (w + n2w n = w - n2w (dimword (:'a) - n))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [wordsTheory.word_sub_def,
  wordsTheory.word_2comp_n2w]);


val word_add_to_sub_TYPES = save_thm ("word_add_to_sub_TYPES",
let
  fun inst wty =
    INST_TYPE [``:'a`` |-> wty] word_add_to_sub_GEN;

  val thm1 = LIST_CONJ ([inst ``:32``, inst ``:64``, inst ``:16``, inst ``:8``])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm1
in
  thm2
end)


(***************)
(* ExtendValue *)
(***************)

val Extend_ALT_DEF = store_thm ("Extend_ALT_DEF",
``!l unsigned.
     arm8$Extend (l,unsigned) : 'a word =
     if unsigned then v2w l
     else v2w (sign_extend (dimindex (:'a)) l)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [arm8Theory.Extend_def] >>
Cases_on `unsigned` >> ASM_REWRITE_TAC [] >>
Cases_on `HD l` >- (
  ASM_SIMP_TAC std_ss [sign_extend_def, word_len_def]
) >>
Cases_on `dimindex (:'a) <= LENGTH l` >- (
  `dimindex (:'a) - LENGTH l = 0` by DECIDE_TAC >>
  ASM_SIMP_TAC list_ss [listTheory.PAD_LEFT, sign_extend_def]
) >>
`PAD_LEFT F (dimindex (:'a)) l =
 fixwidth (dimindex (:'a)) l` by (
  ASM_SIMP_TAC arith_ss [fixwidth_def, LET_THM, zero_extend_def]
) >>
ASM_SIMP_TAC std_ss [v2w_fixwidth, sign_extend_def]);


val ExtendValue_REWR = save_thm ("ExtendValue_REWR",
  SIMP_RULE (std_ss) [LET_THM, Extend_ALT_DEF, word_len_def] (
    DatatypeSimps.cases_to_top_RULE arm8Theory.ExtendValue_def));


val ExtendValue_Unsigned_REWR = prove (
``(ExtendValue (w, ExtendType_UXTB, n) = (w2w ((w2w w):word8):word64) << n) /\
  (ExtendValue (w, ExtendType_UXTH, n) = (w2w ((w2w w):word16):word64) << n) /\
  (ExtendValue (w, ExtendType_UXTW, n) = (w2w ((w2w w):word32):word64) << n) /\
  (ExtendValue (w, ExtendType_UXTX, n) = (w << n))``,

SIMP_TAC (std_ss++wordsLib.SIZES_ss) [ExtendValue_REWR,
  GSYM bitstringTheory.word_lsl_v2w] >>
Q.SUBGOAL_THEN `w2v w = fixwidth (dimindex (:64)) (w2v w)` SUBST1_TAC >- (
  METIS_TAC[fixwidth_id_imp, length_w2v]
) >>
REWRITE_TAC [GSYM bitstringTheory.word_bits_v2w, v2w_w2v] >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [w2w,
  wordsTheory.word_bits_def, fcpTheory.FCP_BETA, word_lsl_def] >>
SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF]);

val ExtendValue_Unsigned_32_REWR = prove (
``(ExtendValue (w, ExtendType_UXTB, n) = (w2w ((w2w w):word8):word32) << n) /\
  (ExtendValue (w, ExtendType_UXTH, n) = (w2w ((w2w w):word16):word32) << n) /\
  (ExtendValue (w, ExtendType_UXTW, n) = (w << n))``,

SIMP_TAC (std_ss++wordsLib.SIZES_ss) [ExtendValue_REWR,
  GSYM bitstringTheory.word_lsl_v2w] >>
Q.SUBGOAL_THEN `w2v w = fixwidth (dimindex (:32)) (w2v w)` SUBST1_TAC >- (
  METIS_TAC[fixwidth_id_imp, length_w2v]
) >>
REWRITE_TAC [GSYM bitstringTheory.word_bits_v2w, v2w_w2v] >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [w2w,
  wordsTheory.word_bits_def, fcpTheory.FCP_BETA, word_lsl_def] >>
SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF]);


val ExtendValue_Signed_REWR_aux = prove (
``!n w. n < 64 ==> (dimindex(:'b) <= 64) ==> (
(v2w
   (sign_extend 64 (shiftl (field (MIN (dimindex(:'b)) (64 - n) - 1) 0 (w2v (w:word64))) n)):word64 =
 sw2sw ((w2w w):'b word) << n))``,

REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++wordsLib.SIZES_ss) [ExtendValue_REWR] >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REWRITE_TAC[word_index_v2w] >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [word_lsl_def, fcpTheory.FCP_BETA,
  sw2sw, w2w, testbit, sign_extend_def, listTheory.PAD_LEFT,
  shiftl_def, listTheory.PAD_RIGHT, length_field] >>
Q.ABBREV_TAC `m = MIN (dimindex (:'b)) (64 - n)` >>
`0 < m /\ m <= dimindex(:'b) /\ (n + m <= 64)` by (
  Q.UNABBREV_TAC `m` >>
  ASM_SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF, DIMINDEX_GT_0]
) >>
`SUC (m - 1) = m` by DECIDE_TAC >>

ASM_SIMP_TAC arith_ss [] >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [LET_THM, listTheory.EL_APPEND_EQN, listTheory.LENGTH_GENLIST,
  listTheory.LENGTH_APPEND, length_field, listTheory.EL_GENLIST,
  el_field, length_w2v] >>
REPEAT STRIP_TAC >>
`(64 < i + 65 - n <=> (n <= i))` by DECIDE_TAC >>

ASM_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [GSYM listTheory.EL,
  el_field, listTheory.EL_APPEND_EQN, length_field, length_w2v, el_w2v,
  word_msb_def, w2w] >>
Q.UNABBREV_TAC `m` >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [arithmeticTheory.MIN_DEF] >>
CCONTR_TAC >>
FULL_SIMP_TAC arith_ss [])



val ExtendValue_Signed_REWR = prove (
``(!w n. n < 64 ==> (ExtendValue (w, ExtendType_SXTB, n) = ((sw2sw ((w2w w):word8):word64) << n))) /\
  (!w n. n < 64 ==> (ExtendValue (w, ExtendType_SXTH, n) = ((sw2sw ((w2w w):word16):word64) << n))) /\
  (!w n. n < 64 ==> (ExtendValue (w, ExtendType_SXTW, n) = ((sw2sw ((w2w w):word32):word64) << n))) /\
  (!w:word64 n. n < 64 ==> (ExtendValue (w, ExtendType_SXTX, n) = (w << n)))``,

ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:8``] ExtendValue_Signed_REWR_aux) >>
ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:16``] ExtendValue_Signed_REWR_aux) >>
ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:32``] ExtendValue_Signed_REWR_aux) >>
ASSUME_TAC (INST_TYPE [``:'b`` |-> ``:64``] ExtendValue_Signed_REWR_aux) >>

FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [ExtendValue_REWR, w2w_id, sw2sw_id]);


val ExtendValue_REWRS = save_thm ("ExtendValue_REWRS", let
  val thm0 = CONJ (GEN_ALL ExtendValue_Unsigned_REWR) ExtendValue_Signed_REWR
  val thm1 = CONJ (GEN_ALL ExtendValue_Unsigned_32_REWR) thm0
  val thm2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] thm1
in thm2 end);



(********)
(* misc *)
(********)

val arm8_rev_folds = store_thm ("arm8_rev_folds",
`` (!(w :word64).
      (((((39 :num) >< (32 :num)) w :word8) @@
        (((((47 :num) >< (40 :num)) w :word8) @@
         (((((55 :num) >< (48 :num)) w :word8) @@
          (((((63 :num) >< (56 :num)) w :word8) @@
           (((((7 :num) >< (0 :num)) w :word8) @@
            (((((15 :num) >< (8 :num)) w :word8) @@
             (((((23 :num) >< (16 :num)) w :word8) @@
              (((31 :num) >< (24 :num)) w :word8))
                :word16))
               :word24))
              :word32))
             :40 word))
            :word48))
           :56 word))
         :word64) =
      word_reverse_32_64 (word_reverse_8_64 w)) /\
   (!(w :word64).
      (((((55 :num) >< (48 :num)) w :word8) @@
        (((((63 :num) >< (56 :num)) w :word8) @@
         (((((39 :num) >< (32 :num)) w :word8) @@
          (((((47 :num) >< (40 :num)) w :word8) @@
           (((((23 :num) >< (16 :num)) w :word8) @@
            (((((31 :num) >< (24 :num)) w :word8) @@
             (((((7 :num) >< (0 :num)) w :word8) @@
              (((15 :num) >< (8 :num)) w :word8))
                :word16))
               :word24))
              :word32))
             :40 word))
            :word48))
           :56 word))
         :word64) =
      word_reverse_16_64 (word_reverse_8_64 w)) /\
   (!(w :word32).
      (((((23 :num) >< (16 :num)) w :word8) @@
        (((((31 :num) >< (24 :num)) w :word8) @@
         (((((7 :num) >< (0 :num)) w :word8) @@
          (((15 :num) >< (8 :num)) w :word8))
            :word16))
           :word24))
         :word32) =
      word_reverse_16_32 (word_reverse_8_32 w))``,

ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_reverse_REWRS, word_concat_def, word_join_index, word_extract_def,
  w2w, word_bits_def, fcpTheory.FCP_BETA] >>
SIMP_TAC (arith_ss++ boolSimps.LIFT_COND_ss) []);

(*
val g_low_def = Define `g_low(x:word64) = 0xFFFFFFFFw && x`;
val g_high_def = Define `g_high(x:word64) = x >>> 32`;
val arm8_high_u_mul_internal = store_thm ("arm8_high_u_mul_internal",
``!w1:word64 w2:word64. ((127 >< 64) ((w2w (w1)):word128 * w2w (w2)))
= 
g_high(
   g_high (g_low(w1) * g_low(w2)) +
   g_low(g_high(w1) * g_low(w2)) + 
   g_low(g_low(w1) * g_high(w2))
  ) +
  g_high(g_high(w1) * g_low(w2)) + 
  g_high(g_low(w1) * g_high(w2)) +
(g_high(w1) * g_high(w2))
``,
 cheat);
val arm8_high_u_mul = REWRITE_RULE [g_low_def, g_high_def] arm8_high_u_mul_internal;
*)


val arm8_ngc64_fold = store_thm ("arm8_ngc64_fold",
 ``!w:word64 c.
     n2w (w2n (~w) + if c then 1 else 0) =
     ~w + w2w (bool2w c)``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.SIZES_ss) [GSYM word_add_n2w, n2w_w2n, bir_immTheory.bool2w_def,
  w2w_def, w2n_n2w]);

val arm8_ngc32_fold = store_thm ("arm8_ngc32_fold",
 ``!w:word32 c.
     n2w (BITS 31 0 (w2n (~w) + if c then 1 else 0)) =
     (w2w (~w + w2w (bool2w c))):word64``,

REPEAT STRIP_TAC >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:64``] w2w_n2w)) >>
SIMP_TAC (std_ss++wordsLib.SIZES_ss) [] >>
STRIP_TAC >> POP_ASSUM (K ALL_TAC) >>
SIMP_TAC std_ss [w2w_def, n2w_w2n, GSYM word_add_n2w] >>
Cases_on `c` >> (
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [bir_immTheory.bool2w_def, w2n_n2w]
));



val arm8_movk_fold_base_r = prove (
``!n (w:'a word).
   (FINITE univ(:'b)) ==>
   (FINITE univ(:'c)) ==>
   (dimindex (:'c) <= dimindex (:'a)) ==>
   (dimindex (:'b) = dimindex (:'a) - (dimindex (:'c))) ==>
   (dimindex (:('b + 'c)) = dimindex (:'a)) ==>
   (
    (((((dimindex (:'a) - 1) >< (dimindex (:'c))) w):'b word) @@ ((n2w n):'c word)):'a word =
     ((w && ~(n2w (2 ** (dimindex (:'c)) - 1))) || n2w (n MOD 2 ** (dimindex (:'c))))
   )
``,
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REWRITE_TAC [GSYM wordsTheory.WORD_AND_EXP_SUB1] >>
Q.ABBREV_TAC `ii = (2:num) ** (dimindex (:'c))` >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_concat_def, w2w, word_join_index, word_extract_def,
  word_bits_def, word_or_def, word_and_def, word_1comp_def,
  word_join_index] >>
REPEAT STRIP_TAC >>
`(n2w (ii - 1):'a word) ' i <=> (i < (dimindex (:'c)))` by (
  Q.UNABBREV_TAC `ii`  >>
  ASM_SIMP_TAC (bool_ss++wordsLib.SIZES_ss) [word_index, bitTheory.BIT_EXP_SUB1]
) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `i < (dimindex (:'c))` >> ASM_SIMP_TAC arith_ss [] >>
ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_index]
);


val arm8_movk_16_fold_base_l = prove (
``!n (w:'a word).
   (FINITE univ(:'b)) ==>
   (16 <= dimindex (:'a)) ==>
   (dimindex (:'b) = dimindex (:'a) - 16) ==>
   (dimindex (:('b + 16)) = dimindex (:'a)) ==>
   (dimindex (:(16 + 'b)) = dimindex (:'a)) ==>
   (
     ( ((n2w n):word16) @@ ((((dimindex (:'a) - 16 - 1) >< 0) w):'b word) ):'a word
     =
     ( ((n2w (n MOD 2 ** 16)) << (dimindex (:'a) - 16)) || (w && ~((n2w ((2 ** 16) - 1)) << (dimindex (:'a) - 16)) ) )
   )
``,
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REWRITE_TAC [GSYM wordsTheory.WORD_AND_EXP_SUB1] >>
Q.ABBREV_TAC `ii = (2:num) ** 16` >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_concat_def, w2w, word_join_index, word_extract_def,
  word_bits_def, word_or_def, word_and_def, word_1comp_def,
  word_join_index, word_lsl_def] >>
REPEAT STRIP_TAC >>
Q.ABBREV_TAC `ia = (i + 16 − dimindex (:α))` >>
`(i >= (dimindex (:'a) − 16)) ==> ((n2w (ii - 1):'a word) ' ia <=> (ia < 16))` by (
  STRIP_TAC >>
  Q.UNABBREV_TAC `ii`  >>
  Q.UNABBREV_TAC `ia`  >>
  `(i + 16 − dimindex (:'a)) < dimindex (:'a)` by (
    ASM_SIMP_TAC (arith_ss) []
  ) >>
  ASM_SIMP_TAC (bool_ss) [word_index, bitTheory.BIT_EXP_SUB1]
) >>
ASM_SIMP_TAC std_ss [] >>
Cases_on `i < dimindex (:'a) − 16` >> ASM_SIMP_TAC arith_ss [] >>

Q.UNABBREV_TAC `ia`  >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA, n2w_def]
);

val arm8_movk_16_fold_base_m = prove (
``!n (w:'a word).
   FINITE univ(:'b) ==>
   FINITE univ(:'c) ==>
   FINITE univ(:'d) ==>
   (16 <= dimindex (:'a)) ==>
   (dimindex (:'b) + dimindex (:'c) = dimindex (:'a) - 16) ==>
   (dimindex (:('b + 'c + 16)) = dimindex (:'a)) ==>
   (dimindex (:('b + 'd)) = dimindex (:'a)) ==>
   (dimindex (:'d) = 16 + dimindex (:'c)) ==>
   (dimindex (:(16 + 'c)) + dimindex (:'b) = dimindex (:'a)) ==>
   (
      ( ((((dimindex (:'a) - 1) >< (dimindex (:'d))) w):'b word) @@ (((n2w n):word16) @@ ((((dimindex (:'c) - 1) >< 0) w):'c word)):'d word ):'a word
      =
      ( (w && ((n2w (2 ** (dimindex (:'b)) - 1)) << (dimindex (:'d)))) || ((n2w (n MOD 2 ** 16)) << (dimindex (:'c))) || (w && (n2w (2 ** (dimindex (:'c)) - 1))) )
   )
``,
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REWRITE_TAC [GSYM wordsTheory.WORD_AND_EXP_SUB1] >>
Q.ABBREV_TAC `ii = (2:num) ** 16` >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_concat_def, w2w, word_join_index, word_extract_def,
  word_bits_def, word_or_def, word_and_def, word_1comp_def,
  word_join_index, word_lsl_def] >>
REPEAT STRIP_TAC >>

Q.ABBREV_TAC `iia = (2:num) ** (dimindex (:'b))` >>
Q.ABBREV_TAC `iaa = (i − (dimindex (:'c) + 16))` >>
`(dimindex (:'c) + 16 <= i) ==> (n2w (iia − 1) ' iaa <=> (iaa < (dimindex (:'b))))` by (
  STRIP_TAC >>
  `iaa < dimindex (:'a)` by (
    Q.UNABBREV_TAC `iaa`  >>
    ASM_SIMP_TAC (arith_ss) []
  ) >>
  Q.UNABBREV_TAC `iia`  >>
  ASM_SIMP_TAC (bool_ss) [word_index, bitTheory.BIT_EXP_SUB1]
) >>

`(n2w (2 ** dimindex (:'c) − 1) ' i) = (i < (dimindex (:'c)))` by (
  ASM_SIMP_TAC (bool_ss) [word_index, bitTheory.BIT_EXP_SUB1]
) >>


ASM_SIMP_TAC std_ss [] >>
Cases_on `i < dimindex (:'c) + 16` >> ASM_SIMP_TAC arith_ss [] >- (
  Cases_on `i < dimindex (:'c)` >> ASM_SIMP_TAC arith_ss [] >>

  Q.UNABBREV_TAC `ii`  >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA, n2w_def, bitTheory.BIT_EXP_SUB1]
) >>

ASM_SIMP_TAC std_ss [] >>
Q.UNABBREV_TAC `iaa`  >>

ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA, n2w_def] >>

Q.UNABBREV_TAC `ii`  >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA, n2w_def, bitTheory.BIT_EXP_SUB1]
);





val arm8_movk64_fold0  = save_thm  ("arm8_movk64_fold0",
  SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:64``, ``:'b`` |-> ``:48``, ``:'c`` |-> ``:16``] arm8_movk_fold_base_r));

val arm8_movk64_fold16 = store_thm ("arm8_movk64_fold16",
  ``!n (w:word64). ((63 >< 32) w : word32) @@ ((((n2w:num->word16) n) @@ ((15 >< 0) w : word16)): word32) = (w && 0xFFFFFFFF00000000w) || (((n2w:num->word64) (n MOD 65536)) << 16) || (w && 0x000000000000FFFFw)``,
  ASSUME_TAC ( SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:64``, ``:'b`` |-> ``:32``, ``:'c`` |-> ``:16``, ``:'d`` |-> ``:32``] arm8_movk_16_fold_base_m)) >>
  FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) []
);

val arm8_movk64_fold32 = store_thm ("arm8_movk64_fold32",
  ``!n (w:word64). ((63 >< 48) w : word16) @@ ((((n2w:num->word16) n) @@ ((31 >< 0) w : word32)) : word48) = (w && 0xFFFF000000000000w) || (((n2w:num->word64) (n MOD 65536)) << 32) || (w && 0x00000000FFFFFFFFw)``,
  ASSUME_TAC ( SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:64``, ``:'b`` |-> ``:16``, ``:'c`` |-> ``:32``, ``:'d`` |-> ``:48``] arm8_movk_16_fold_base_m)) >>
  FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) []
);

val arm8_movk64_fold48 = store_thm ("arm8_movk64_fold48",
  ``!n (w:word64). ((n2w:num->word16) n) @@ ((47 >< 0) w : word48) = (((n2w:num->word64) (n MOD 65536)) << 48) || (w && 0x0000FFFFFFFFFFFFw)``,
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [( SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:64``, ``:'b`` |-> ``:48``] arm8_movk_16_fold_base_l))]
);


val arm8_movk32_fold0  = save_thm  ("arm8_movk32_fold0",
  SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:16``, ``:'c`` |-> ``:16``] arm8_movk_fold_base_r));

val arm8_movk32_fold16 = store_thm ("arm8_movk32_fold16",
  ``!n (w:word32). ((n2w:num->word16) n) @@ ((15 >< 0) w : word16) = (((n2w:num->word32) (n MOD 65536)) << 16) || (w && 0x0000FFFFw)``,
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [( SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] (
     INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:16``] arm8_movk_16_fold_base_l))]
);

val arm8_movk32_folds = save_thm ("arm8_movk32_folds", LIST_CONJ [arm8_movk32_fold0, arm8_movk32_fold16]);
val arm8_movk64_folds = save_thm ("arm8_movk64_folds", LIST_CONJ [arm8_movk64_fold0, arm8_movk64_fold16, arm8_movk64_fold32, arm8_movk64_fold48]);


(****************)
(* Combinations *)
(****************)

val arm8_extra_LIFTS = save_thm ("arm8_extra_LIFTS",
  LIST_CONJ [
    arm8_LIFT_LOAD_BYTE,
    arm8_LIFT_LOAD_HALF,
    arm8_LIFT_LOAD_WORD,
    arm8_LIFT_LOAD_DWORD,
    arm8_LIFT_STORE_BYTE,
    arm8_LIFT_STORE_HALF,
    arm8_LIFT_STORE_WORD,
    arm8_LIFT_STORE_DWORD
]);

val arm8_CHANGE_INTERVAL_THMS = save_thm ("arm8_CHANGE_INTERVAL_THMS",
  LIST_CONJ [
    arm8_LIFT_STORE_DWORD_CHANGE_INTERVAL,
    arm8_LIFT_STORE_WORD_CHANGE_INTERVAL,
    arm8_LIFT_STORE_HALF_CHANGE_INTERVAL,
    arm8_LIFT_STORE_BYTE_CHANGE_INTERVAL]);


val arm8_count_leading_eq_bir = store_thm ("arm8_count_leading_eq_bir",
 ``!w:'a word. (arm8$CountLeadingZeroBits w = bir_CountLeadingZeroBits w) /\
               (arm8$CountLeadingSignBits w = bir_CountLeadingSignBits w)``,

  REWRITE_TAC [arm8Theory.CountLeadingZeroBits_def,
               arm8Theory.HighestSetBit_def,
               arm8Theory.CountLeadingSignBits_def,
               bir_CountLeadingZeroBits_def,
               bir_HighestSetBit_def,
               bir_CountLeadingSignBits_def]
);


val arm8_count_leading_zero = store_thm ("arm8_count_leading_zero",
 ``!w:'a word. (n2w (arm8$CountLeadingZeroBits w)) = bir_word_countleadingzeros w``,

  REWRITE_TAC [arm8_count_leading_eq_bir,
               bir_word_countleadingzeros_def]
);

val arm8_count_leading_sign = store_thm ("arm8_count_leading_sign",
 ``!w:'a word. (n2w (arm8$CountLeadingSignBits w)) = bir_word_countleadingsigns w``,

  REWRITE_TAC [arm8_count_leading_eq_bir,
               bir_word_countleadingsigns_def]
);

val cast_thm = prove (``
  !n. w2w (n2w n :word32) = (n2w (BITS 31 0 n) :word64)
``,
  REWRITE_TAC [wordsTheory.w2w_def, wordsTheory.w2n_n2w, bitTheory.BITS_ZERO3] >>
  SIMP_TAC (arith_ss++wordsLib.SIZES_ss) []
);

val arm8_count_leading_zero_32 = store_thm ("arm8_count_leading_zero_32",
 ``!w:word32. (n2w (BITS 31 0 (arm8$CountLeadingZeroBits w)) :word64) = w2w (bir_word_countleadingzeros w)``,

  REWRITE_TAC [arm8_count_leading_zero, GSYM cast_thm]
);

val arm8_count_leading_sign_32 = store_thm ("arm8_count_leading_sign_32",
 ``!w:word32. (n2w (BITS 31 0 (arm8$CountLeadingSignBits w)) :word64) = w2w (bir_word_countleadingsigns w)``,

  REWRITE_TAC [arm8_count_leading_sign, GSYM cast_thm]
);
      
val arm8_extra_FOLDS = save_thm ("arm8_extra_FOLDS",
  LIST_CONJ [arm8_lsl_FOLDS, arm8_and_neg_1w_FOLDS, arm8_lsr_FOLDS,
      arm8_asr_FOLDS, arm8_lsr_no_imm_FOLDS, arm8_asr_no_imm_FOLDS,
      arm8_lsl_no_imm_FOLDS, arm8_sxtw_FOLDS, w2w_REMOVE_FOLDS,
      arm8_mem_store_FOLDS, GSYM word_reverse_REWRS,
      ExtendValue_REWRS, arm8_rev_folds, arm8_ngc64_fold, arm8_ngc32_fold,
      arm8_ror_MOD_FOLDS, arm8_extr_FOLDS, word_shift_extract_ID,
      arm8_movk32_folds, arm8_movk64_folds,
(*      arm8_high_u_mul, *)
      arm8_count_leading_zero, arm8_count_leading_sign,
      arm8_count_leading_zero_32, arm8_count_leading_sign_32
]);

val _ = export_theory();
