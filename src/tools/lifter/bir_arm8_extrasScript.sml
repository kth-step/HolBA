open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_exp_liftingTheory
open arm8_stepTheory
open bir_lifting_machinesTheory;
open bir_interval_expTheory

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



(*******)
(* w2w *)
(*******)

val w2w_REMOVE_1 = prove (
  ``!w : 'a word.
           dimindex (:'a) < dimindex (:'b) ==>
           dimindex (:'b) <> dimindex (:'c) ==>
           (((w2w ((w2w w):'b word)):'c word) =
                  w2w w)``,

Cases >>
ASM_SIMP_TAC arith_ss [w2w_def,n2w_w2n, w2n_n2w,
  wordsTheory.dimindex_dimword_le_iso]);


val w2w_REMOVE_2 = prove (
  ``!w : 'a word.
           ~(dimindex (:'a) <= dimindex (:'b)) ==>
           dimindex (:'c) < dimindex (:'b) ==>

           (((w2w ((w2w w):'b word)):'c word) =
                  w2w w)``,

Cases >>
ASM_SIMP_TAC arith_ss [w2w_def,n2w_w2n, w2n_n2w,
  wordsTheory.dimindex_dimword_le_iso] >>
ONCE_REWRITE_TAC[GSYM wordsTheory.n2w_mod] >>
SIMP_TAC arith_ss [dimword_def] >>
REPEAT STRIP_TAC >>
`dimindex (:'c) <= dimindex (:'b)` by DECIDE_TAC >>
FULL_SIMP_TAC arith_ss [arithmeticTheory.LESS_EQ_EXISTS,
  arithmeticTheory.EXP_ADD] >>
METIS_TAC[bitTheory.ZERO_LT_TWOEXP, arithmeticTheory.MOD_MULT_MOD,
  DIMINDEX_GT_0, arithmeticTheory.MULT_COMM]);





val arm8_w2w_REMOVE_FOLDS = save_thm ("arm8_w2w_REMOVE_FOLDS",
let
  val ty_l = List.map fcpSyntax.mk_int_numeric_type bir_immSyntax.known_imm_sizes

  fun inst ty thmL =
    flatten (map (fn thm => (map (fn ty' => INST_TYPE [ty |-> ty'] thm) ty_l)) thmL)

  val thmL0 = [CONJ w2w_REMOVE_1 w2w_REMOVE_2]
  val thmL1 = inst ``:'a`` thmL0
  val thmL2 = inst ``:'b`` thmL1
  val thmL3 = inst ``:'c`` thmL2
  val thm0 = LIST_CONJ thmL3

  val thm1 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm0

  val thm2 = CONJ thm1 (LIST_CONJ (inst ``:'a`` [w2w_id]))
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
  ((a      =+ (7  >< 0)  w) mmap)))))))`;

val mem_store_word_def = Define `mem_store_word (a:word64) (w:word32) (mmap : (word64 -> word8)) =
   (a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a      =+ (7  >< 0)  w) mmap)))`;

val mem_store_half_def = Define `mem_store_half (a:word64) (w:word16) (mmap : (word64 -> word8)) =
   (a + 1w =+ (15 >< 8)  w)
  ((a      =+ (7  >< 0)  w) mmap)`;

val mem_store_byte_def = Define `mem_store_byte (a:word64) (w:word8) (mmap : (word64 -> word8)) =
  ((a      =+ w) mmap)`;


val arm8_mem_store_FOLDS = save_thm ("arm8_mem_store_FOLDS",
let
  val thm0 = GSYM mem_store_byte_def
  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM mem_store_byte_def] (GSYM thm)

  val def_THMS = LIST_CONJ [GSYM mem_store_byte_def,
     mk_thm_GEN mem_store_half_def,
     mk_thm_GEN mem_store_word_def,
     mk_thm_GEN mem_store_dword_def]

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM mem_store_byte_def] tm))

  val zero_THM0 = mk_zero_thm mem_store_half_def ``mem_store_half a 0w mmap``;
  val zero_THM1 = REWRITE_RULE [zero_THM0] (mk_zero_thm mem_store_word_def ``mem_store_word a 0w mmap``);
  val zero_THM2 = REWRITE_RULE [zero_THM1, zero_THM0] (
     mk_zero_thm mem_store_dword_def ``mem_store_dword a 0w mmap``);

in LIST_CONJ [def_THMS, zero_THM0, zero_THM1, zero_THM2] end);


val arm8_LIFT_STORE_DWORD = store_thm ("arm8_LIFT_STORE_DWORD",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_dword va vv mem_f)``,

SIMP_TAC std_ss [mem_store_dword_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


val arm8_LIFT_STORE_WORD = store_thm ("arm8_LIFT_STORE_WORD",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_word va vv mem_f)``,

SIMP_TAC std_ss [mem_store_word_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


val arm8_LIFT_STORE_HALF = store_thm ("arm8_LIFT_STORE_HALF",
``!env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (mem_store_half va vv mem_f)``,

SIMP_TAC std_ss [mem_store_half_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]);


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

val arm8_extra_FOLDS = save_thm ("arm8_extra_FOLDS",
  LIST_CONJ [arm8_lsl_FOLDS, arm8_and_neg_1w_FOLDS, arm8_lsr_FOLDS,
      arm8_asr_FOLDS, arm8_lsr_no_imm_FOLDS, arm8_asr_no_imm_FOLDS,
      arm8_lsl_no_imm_FOLDS, arm8_sxtw_FOLDS, arm8_w2w_REMOVE_FOLDS,
      arm8_mem_store_FOLDS])



val _ = export_theory();
