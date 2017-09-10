open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_nzcv_expTheory

(* ARM uses so called NZCV status flags for conditional execution. These were
   formalised in bir_nzcv_expTheory. However, the ARM step library partially evalutates
   such NZCV flag functions while generating step theorems. Therefore, we need special
   lemmata to reintroduce the simple NZCV defs.

*)

val _ = new_theory "bir_nzcv_intros";


(***************************)
(* ARM 8 general cmp / sub *)
(***************************)

val nzcv_SUB_SUM_REWR = prove (
``!w0 w1:'a word.
  (w2n w0 + w2n (~w1) + 1) =
  (if (w1 = 0w) then w2n w0 + dimword (:'a) else
    (w2n w0 + w2n (~w1 + 1w)))``,

REPEAT Cases >>
ASM_SIMP_TAC arith_ss [w2n_n2w, word_1comp_n2w, word_add_n2w, n2w_11] >>
CASE_TAC >>
ASM_SIMP_TAC arith_ss []);


val nzcv_SUB_SUM_REWR_MOD = prove (
``!w0 w1:'a word.
  (w2n w0 + w2n (~w1) + 1) MOD dimword (:'a) =
  (w2n w0 + w2n (~w1 + 1w)) MOD dimword (:'a)``,

SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) [nzcv_SUB_SUM_REWR,
  GSYM WORD_NEG, WORD_NEG_0, w2n_n2w, ZERO_LT_dimword,
  arithmeticTheory.ADD_MODULUS]);


val nzcv_SUB_V_fold_ARM8 = store_thm ("nzcv_SUB_V_fold_ARM8",
``!w1 w0:'a word.
  (word_msb w0 <=> word_msb (~w1)) /\
  (word_msb w0 <=/=> BIT  (dimindex (:'a) - 1) (w2n w0 + w2n (~w1) + 1)) =
  nzcv_BIR_SUB_V w0 w1``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [nzcv_def, LET_THM, nzcv_BIR_SUB_V_def,
 WORD_MSB_1COMP, GSYM word_msb_n2w, WORD_NEG] >>
`(n2w (w2n w0 + w2n (~w1) + 1)):'a word =
 n2w (w2n w0 + w2n (~w1 + 1w))` by
  METIS_TAC[n2w_mod, nzcv_SUB_SUM_REWR_MOD] >>
ASM_SIMP_TAC std_ss [] >>
METIS_TAC[]);


val nzcv_SUB_C_fold_ARM8 = store_thm ("nzcv_SUB_C_fold_ARM8",
``!w1 w0.
  ((if w2n w0 + w2n (~(w1:'a word)) + 1 < dimword (:'a) then w2n w0 + w2n (~w1) + 1
   else (w2n w0 + w2n (~w1) + 1) MOD (dimword (:'a))) <>
  w2n w0 + w2n (~w1) + 1) = nzcv_BIR_SUB_C w0 w1``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [nzcv_def, LET_THM, nzcv_BIR_SUB_C_def,
  WORD_MSB_1COMP, GSYM word_msb_n2w, WORD_NEG,
  nzcv_SUB_SUM_REWR] >>
Cases_on `w1 = 0w` >> (
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MODULUS, ZERO_LT_dimword, w2n_lt]
) >>
Q.ABBREV_TAC `nn = w2n w0 + w2n (~w1 + 1w)` >>
Cases_on `nn < dimword (:'a)` >- (
  ASM_SIMP_TAC arith_ss [] >>
  STRIP_TAC >>
  `dimword (:'a) <= nn` by METIS_TAC[bitTheory.BIT_IMP_GE_TWOEXP, dimword_def] >>
  DECIDE_TAC
) >>

`?m. (m < dimword (:'a)) /\ (nn = m + dimword (:'a))` by (
  FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS] >>
  `?m. nn = dimword (:'a) + m` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
  Q.EXISTS_TAC `m` >>
  ASM_SIMP_TAC arith_ss [] >>
  `nn < dimword (:'a) + dimword (:'a)` by (
    Q.UNABBREV_TAC `nn` >>
    MATCH_MP_TAC integerTheory.LT_ADD2 >>
    METIS_TAC[w2n_lt]
  ) >>
  DECIDE_TAC
) >>

ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MODULUS, ZERO_LT_dimword] >>

MP_TAC (SPECL [``dimindex (:'a)``, ``SUC (dimindex (:'a))``, ``m + dimword (:'a)``] bitTheory.EXISTS_BIT_IN_RANGE) >>
ASM_SIMP_TAC arith_ss [dimword_def, arithmeticTheory.EXP, GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
METIS_TAC[arithmeticTheory.LESS_EQUAL_ANTISYM]);


val nzcv_SUB_Z_fold_ARM8 = store_thm ("nzcv_SUB_Z_fold_ARM8",
``!w1 w0. ((w0:'a word - w1) = 0w) = nzcv_BIR_SUB_Z w0 w1``,
SIMP_TAC std_ss [nzcv_def, LET_THM, nzcv_BIR_SUB_Z_def, GSYM word_add_def, word_sub_def]);


val nzcv_SUB_N_fold_ARM8 = store_thm ("nzcv_SUB_N_fold_ARM8",
``!w1 w0. word_msb ((w0:'a word) - w1) = nzcv_BIR_SUB_N w0 w1``,
SIMP_TAC std_ss [nzcv_def, LET_THM, nzcv_BIR_SUB_N_def, GSYM word_add_def, word_sub_def]);


val nzcv_SUB_FOLDS_ARM8_GEN = save_thm ("nzcv_SUB_FOLDS_ARM8_GEN",
  LIST_CONJ [nzcv_SUB_N_fold_ARM8, nzcv_SUB_C_fold_ARM8, nzcv_SUB_Z_fold_ARM8, nzcv_SUB_V_fold_ARM8]
);



(*************************)
(* ARM 8 general add/cmn *)
(*************************)

(* cmp uses w2 - w1, we also need a version for w1 + w2 *)

val nzcv_ADD_V_fold_ARM8 = store_thm ("nzcv_ADD_V_fold_ARM8",
``!w1:'a word w0:'a word.
  (word_msb w0 <=> word_msb w1) /\
  (word_msb w0 <=/=> BIT (dimindex (:'a) - 1) (w2n w0 + w2n w1)) = nzcv_BIR_ADD_V w0 w1``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [nzcv_BIR_ADD_V_def,
  GSYM word_msb_n2w, word_add_def]);

(* We need a special case for w0 = w1 *)
val nzcv_ADD_V_fold_ARM8_ID = store_thm ("nzcv_ADD_V_fold_ARM8_ID",
``!w:'a word.
  (word_msb w <=/=> BIT  (dimindex (:'a) - 1) (w2n w + w2n w)) =
  nzcv_BIR_ADD_V w w``,
SIMP_TAC std_ss [GSYM nzcv_ADD_V_fold_ARM8]);


val nzcv_ADD_C_fold_ARM8 = store_thm ("nzcv_ADD_C_fold_ARM8",
``!w1 w0.
  ((if w2n w0 + w2n ((w1:'a word)) < dimword (:'a) then w2n w0 + w2n w1
   else (w2n w0 + w2n w1) MOD (dimword (:'a))) <>
  w2n w0 + w2n w1) = nzcv_BIR_ADD_C w0 w1``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [nzcv_BIR_ADD_C_def] >>
Q.ABBREV_TAC `nn = w2n w0 + w2n w1` >>
Cases_on `nn < dimword (:'a)` >- (
  ASM_SIMP_TAC arith_ss [] >>
  STRIP_TAC >>
  `dimword (:'a) <= nn` by METIS_TAC[bitTheory.BIT_IMP_GE_TWOEXP, dimword_def] >>
  DECIDE_TAC
) >>

`?m. (m < dimword (:'a)) /\ (nn = m + dimword (:'a))` by (
  FULL_SIMP_TAC arith_ss [arithmeticTheory.NOT_LESS] >>
  `?m. nn = dimword (:'a) + m` by METIS_TAC[arithmeticTheory.LESS_EQ_EXISTS] >>
  Q.EXISTS_TAC `m` >>
  ASM_SIMP_TAC arith_ss [] >>
  `nn < dimword (:'a) + dimword (:'a)` by (
    Q.UNABBREV_TAC `nn` >>
    MATCH_MP_TAC integerTheory.LT_ADD2 >>
    METIS_TAC[w2n_lt]
  ) >>
  DECIDE_TAC
) >>

ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MODULUS, ZERO_LT_dimword] >>

MP_TAC (SPECL [``dimindex (:'a)``, ``SUC (dimindex (:'a))``, ``m + dimword (:'a)``] bitTheory.EXISTS_BIT_IN_RANGE) >>
ASM_SIMP_TAC arith_ss [dimword_def, arithmeticTheory.EXP, GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
METIS_TAC[arithmeticTheory.LESS_EQUAL_ANTISYM]);


val nzcv_ADD_Z_fold_ARM8 = store_thm ("nzcv_ADD_Z_fold_ARM8",
``!w1 w0. (((w0:'a word) + w1) = 0w) = nzcv_BIR_ADD_Z w0 w1``,
SIMP_TAC std_ss [nzcv_BIR_ADD_Z_def, GSYM nzcv_SUB_Z_fold_ARM8,
  word_sub_def, WORD_NEG_NEG]);

val nzcv_ADD_N_fold_ARM8 = store_thm ("nzcv_ADD_N_fold_ARM8",
``!w1 w0. word_msb ((w0:'a word) + w1) = nzcv_BIR_ADD_N (w0:'a word) w1``,
SIMP_TAC std_ss [nzcv_BIR_ADD_N_def, GSYM nzcv_SUB_N_fold_ARM8,
  word_sub_def, WORD_NEG_NEG]);


val nzcv_ADD_FOLDS_ARM8_GEN = save_thm ("nzcv_ADD_FOLDS_ARM8_GEN",
  LIST_CONJ [nzcv_ADD_N_fold_ARM8, nzcv_ADD_C_fold_ARM8, nzcv_ADD_Z_fold_ARM8, nzcv_ADD_V_fold_ARM8,
    nzcv_ADD_V_fold_ARM8_ID]
)


(************************)
(* ARM 8 immediate args *)
(************************)

(* The generic one needs instantiating unluckily because immediate arguments
   are allowed and there are extra simps for these. *)

(* We can ignore the case "n < INT_MIN (:'a)" since
   n is computed from a small immediate and should for all
   relevant cases be that large. *)
val nzcv_SUB_V_fold_ARM8_CONST = store_thm ("nzcv_SUB_V_fold_ARM8_CONST",
``!w0 n. n < dimword (:'a) ==> INT_MIN (:'a) <= n ==>
   ((word_msb w0) /\
    (word_msb w0 <=/=> BIT  (dimindex (:'a) - 1) (w2n w0 + n + 1)) =

   (nzcv_BIR_SUB_V (w0:'a word) (n2w (dimword (:'a) - SUC n))))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [GSYM nzcv_SUB_V_fold_ARM8,
  word_1comp_n2w, w2n_n2w, word_msb_n2w_numeric]);


val nzcv_ADD_V_fold_ARM8_CONST = store_thm ("nzcv_ADD_V_fold_ARM8_CONST",
``!(w0 : 'a word) n. n < dimword (:'a) ==> (n < INT_MIN (:'a)) ==>
   ((~(word_msb w0) /\
    (word_msb w0 <=/=> BIT  (dimindex (:'a) - 1) (w2n w0 + n))) =
   nzcv_BIR_ADD_V w0 (n2w n))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [GSYM nzcv_ADD_V_fold_ARM8,
  word_1comp_n2w, w2n_n2w, word_msb_n2w_numeric]);



val nzcv_SUB_C_fold_ARM8_CONST = store_thm ("nzcv_SUB_C_fold_ARM8_CONST",
``!w0 n. n < dimword (:'a) ==>
 ( ((if w2n w0 + n + 1 < dimword (:'a) then w2n w0 + n + 1
   else (w2n w0 + n + 1) MOD (dimword (:'a))) <>
  w2n w0 + n + 1) = (nzcv_BIR_SUB_C (w0:'a word) (n2w (dimword (:'a) - SUC n))))``,
SIMP_TAC arith_ss [GSYM nzcv_SUB_C_fold_ARM8,  word_1comp_n2w, w2n_n2w]);


val nzcv_ADD_C_fold_ARM8_CONST = store_thm ("nzcv_ADD_C_fold_ARM8_CONST",
``!w0 n. n < dimword (:'a) ==>
 ( ((if w2n w0 + n < dimword (:'a) then w2n w0 + n
   else (w2n w0 + n) MOD (dimword (:'a))) <>
  w2n w0 + n) = (nzcv_BIR_ADD_C (w0:'a word) (n2w n)))``,
SIMP_TAC arith_ss [GSYM nzcv_ADD_C_fold_ARM8, w2n_n2w]);


(* For Z and N no special constant rewrites are needed, the standard ones
   for ADD always fire. However, we might not want this, since we want to
   introduce nzcv_BIR_SUB_Z and nzcv_BIR_SUB_C.
   So let us rewrite, if constants are two large. *)

val nzcv_ADD_Z_to_SUB = store_thm ("nzcv_ADD_Z_to_SUB",
``!(w0:'a word) n.
         (n < dimword (:'a)) /\ (dimword (:'a) - n < n) ==>
         (nzcv_BIR_ADD_Z w0 (n2w n) <=>
          nzcv_BIR_SUB_Z w0 (n2w (dimword (:'a) - n)))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [nzcv_BIR_ADD_Z_def, word_2comp_n2w]);


val nzcv_ADD_N_to_SUB = store_thm ("nzcv_ADD_N_to_SUB",
``!(w0:'a word) n.
         (n < dimword (:'a)) /\ (dimword (:'a) - n < n) ==>
         (nzcv_BIR_ADD_N w0 (n2w n) <=>
          nzcv_BIR_SUB_N w0 (n2w (dimword (:'a) - n)))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [nzcv_BIR_ADD_N_def, word_2comp_n2w]);

(* For 0 it does not matter, which constant is smaller, but SUB is more canonical *)
val nzcv_ADD_Z_to_SUB_0 = store_thm ("nzcv_ADD_Z_to_SUB_0",
``!(w0:'a word). (nzcv_BIR_ADD_Z w0 (n2w 0) <=>  nzcv_BIR_SUB_Z w0 (n2w 0))``,

ASM_SIMP_TAC std_ss [nzcv_BIR_ADD_Z_def, word_2comp_n2w,
  ZERO_LT_dimword, n2w_dimword]);

val nzcv_ADD_N_to_SUB_0 = store_thm ("nzcv_ADD_N_to_SUB_0",
``!(w0:'a word). (nzcv_BIR_ADD_N w0 (n2w 0) <=>  nzcv_BIR_SUB_N w0 (n2w 0))``,

ASM_SIMP_TAC std_ss [nzcv_BIR_ADD_N_def, word_2comp_n2w,
  ZERO_LT_dimword, n2w_dimword]);



(* Nothing special needed for Z and N *)
val nzcv_ADD_FOLDS_ARM8_CONST_GEN = save_thm ("nzcv_ADD_FOLDS_ARM8_CONST_GEN",
  LIST_CONJ [
        nzcv_ADD_C_fold_ARM8_CONST,
        nzcv_ADD_V_fold_ARM8_CONST]
)


val nzcv_SUB_FOLDS_ARM8_CONST_GEN = save_thm ("nzcv_SUB_FOLDS_ARM8_CONST_GEN",
  LIST_CONJ [
        nzcv_SUB_C_fold_ARM8_CONST,
        nzcv_SUB_V_fold_ARM8_CONST,
        nzcv_ADD_N_to_SUB,
        nzcv_ADD_Z_to_SUB,
        nzcv_ADD_N_to_SUB_0,
        nzcv_ADD_Z_to_SUB_0]
);




(****************)
(* ARM 8 32 bit *)
(****************)

(* What we really need is an instance for 32 bit words, though*)
val nzcv_FOLDS_ARM8_32 = save_thm ("nzcv_FOLDS_ARM8_32",
SIMP_RULE (std_ss++wordsLib.SIZES_ss) []  (
  INST_TYPE [``:'a`` |-> ``:32``] (LIST_CONJ [
      nzcv_BIR_SIMPS,
      nzcv_SUB_FOLDS_ARM8_GEN,
      nzcv_SUB_FOLDS_ARM8_CONST_GEN,
      nzcv_ADD_FOLDS_ARM8_GEN,
      nzcv_ADD_FOLDS_ARM8_CONST_GEN])
));



(*********)
(* Tests *)
(*********)



(*

open arm8_stepLib

fun test_nzcv_folds_hex s =
  (arm8.diss s, s,
   map (SIMP_RULE std_ss [nzcv_FOLDS_ARM8_32]) (arm8_step_hex s));

val test_nzcv_folds_code = List.map test_nzcv_folds_hex o arm8AssemblerLib.arm8_code;


test_nzcv_folds_code `CMP w0, #3`;
test_nzcv_folds_code `cmp w0, #324`;
test_nzcv_folds_code `cmp w0, #0`;
test_nzcv_folds_code `cmp w0, w1`;
test_nzcv_folds_code `cmp w0, w0`;
test_nzcv_folds_code `cmp w1, w1`;

test_nzcv_folds_code `cmn w0, #3`
test_nzcv_folds_code `cmn w0, #324`
test_nzcv_folds_code `cmn w0, #0`
test_nzcv_folds_code `cmn w0, w2`
test_nzcv_folds_code `cmp w0, #0`
test_nzcv_folds_code `cmn w1, w1`

test_nzcv_folds_code `ADDS w0, w1, w2`

test_nzcv_folds_code `subs w0, w1, w2`
test_nzcv_folds_code `adds w0, w1, w1`
test_nzcv_folds_code `bics w0, w1, w2`


``w2w ((w2w (w:word64)):word32):word64``
*)

val _ = export_theory();
