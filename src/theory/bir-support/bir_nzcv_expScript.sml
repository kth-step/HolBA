open HolKernel Parse boolLib bossLib;
open bir_immTheory bir_expTheory
open bir_typing_expTheory bir_valuesTheory
open pred_setTheory
open bir_exp_immTheory bir_bool_expTheory
open HolBACoreSimps
open wordsTheory

(* ARM uses so called NZCV status flags for conditional execution. They are useful
   concepts for other architectures as well and needs modelling in BIR.

    N – Negative
        is set if the result of a data processing instruction was negative
    Z – Zero
        is set if the result was zero
    C – Carry
        is set if an addition, subtraction or compare causes a result bigger than word size
        or is set from the output of the shifter for move and logical instructions.
    V – Overflow
        is set if an addition, subtraction or compare produces a signed result bigger than
        31/63 bit, i.e. the largest representable positive number

   Comparison and substraction are all very similar. Their flags are modelled
   by "nzcv" from the word library. We use this function and add special ones
   for addition.

*)

val _ = new_theory "bir_nzcv_exp";


(*************)
(* Constants *)
(*************)

(* General constants for add with carry *)
val awc_BIR_C_def = Define `awc_BIR_C w1 w2 c = FST (SND (add_with_carry (w1, w2, c)))`
val awc_BIR_V_def = Define `awc_BIR_V w1 w2 c = SND (SND (add_with_carry (w1, w2, c)))`
val awc_BIR_N_def = Define `awc_BIR_N w1 w2 c = (w1 + w2 + (if c then 1w else 0w) < 0w)`;
val awc_BIR_Z_def = Define `awc_BIR_Z w1 w2 c = (w1 + w2 + (if c then 1w else 0w) = 0w)`


(* Let's instroduce constants for the components of the nzcv tuple. Later we show that
   these correspond to simple subtraction. *)
val nzcv_BIR_SUB_N_def = Define `nzcv_BIR_SUB_N w1 w2 = (let (n, z, c, v) = nzcv w1 w2 in n)`;
val nzcv_BIR_SUB_Z_def = Define `nzcv_BIR_SUB_Z w1 w2 = (let (n, z, c, v) = nzcv w1 w2 in z)`;
val nzcv_BIR_SUB_C_def = Define `nzcv_BIR_SUB_C w1 w2 = (let (n, z, c, v) = nzcv w1 w2 in c)`;
val nzcv_BIR_SUB_V_def = Define `nzcv_BIR_SUB_V w1 w2 = (let (n, z, c, v) = nzcv w1 w2 in v)`;

val nzcv_BIR_SUB_DEF = store_thm ("nzcv_BIR_SUB_DEF",
  ``!w1 w2. nzcv w1 w2 = (nzcv_BIR_SUB_N w1 w2, nzcv_BIR_SUB_Z w1 w2, nzcv_BIR_SUB_C w1 w2, nzcv_BIR_SUB_V w1 w2)``,
REPEAT GEN_TAC >>
`?n z c v. (nzcv w1 w2 = (n, z, c, v))` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [nzcv_BIR_SUB_V_def, nzcv_BIR_SUB_N_def,
  nzcv_BIR_SUB_Z_def, nzcv_BIR_SUB_C_def, LET_THM]);


(* Corresponding definitions for addition *)
val nzcv_BIR_ADD_V_def = Define `nzcv_BIR_ADD_V (w1 : 'a word) (w2 : 'a word) <=>
   ((word_msb w1 <=> word_msb w2) /\
    (word_msb (w1 + w2) <=/=> word_msb w1))`;

val nzcv_BIR_ADD_C_def = Define `nzcv_BIR_ADD_C (w1 : 'a word) (w2 : 'a word) <=>
   BIT (dimindex (:'a)) (w2n w1 + w2n w2)`;

val nzcv_BIR_ADD_Z_def = Define `nzcv_BIR_ADD_Z (w1 : 'a word) (w2 : 'a word) <=>
   nzcv_BIR_SUB_Z w1 (-w2)`;

val nzcv_BIR_ADD_N_def = Define `nzcv_BIR_ADD_N (w1 : 'a word) (w2 : 'a word) <=>
   nzcv_BIR_SUB_N w1 (-w2)`;


(******************)
(* add_with_carry *)
(******************)

val nzcv_BIR_SUB_N_CARRY_DEF = store_thm ("nzcv_BIR_SUB_N_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_SUB_N w1 w2 = awc_BIR_N w1 (~w2) T``,
SIMP_TAC std_ss [awc_BIR_N_def, ADD_WITH_CARRY_SUB, nzcv_BIR_SUB_N_def,
  nzcv_def, LET_THM, word_msb_neg,
  GSYM word_add_n2w, n2w_w2n] >>
SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.WORD_NEG]);

val nzcv_BIR_SUB_Z_CARRY_DEF = store_thm ("nzcv_BIR_SUB_Z_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_SUB_Z w1 w2 = awc_BIR_Z w1 (~w2) T``,
SIMP_TAC std_ss [awc_BIR_Z_def, ADD_WITH_CARRY_SUB, nzcv_BIR_SUB_Z_def,
  nzcv_def, LET_THM, GSYM word_add_n2w, n2w_w2n] >>
SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.WORD_NEG]);

val nzcv_BIR_SUB_C_CARRY_DEF = store_thm ("nzcv_BIR_SUB_C_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_SUB_C w1 w2 = awc_BIR_C w1 (~w2) T``,
SIMP_TAC std_ss [ADD_WITH_CARRY_SUB, nzcv_BIR_SUB_C_def, GSYM word_hs_def,
  WORD_HIGHER_EQ, awc_BIR_C_def]);

val nzcv_BIR_SUB_V_CARRY_DEF = store_thm ("nzcv_BIR_SUB_V_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_SUB_V w1 w2 = awc_BIR_V w1 (~w2) T``,
SIMP_TAC std_ss [ADD_WITH_CARRY_SUB, nzcv_BIR_SUB_V_def, nzcv_def, LET_THM,
  GSYM word_add_def, word_sub_def, awc_BIR_V_def]);


val nzcv_BIR_ADD_N_CARRY_DEF = store_thm ("nzcv_BIR_ADD_N_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_ADD_N w1 w2 = awc_BIR_N w1 w2 F``,
SIMP_TAC (std_ss++wordsLib.WORD_ss) [awc_BIR_N_def, ADD_WITH_CARRY_SUB, nzcv_BIR_ADD_N_def,
  nzcv_BIR_SUB_N_def, nzcv_def, LET_THM, word_msb_neg, GSYM word_add_n2w,
  n2w_w2n]);

val nzcv_BIR_ADD_Z_CARRY_DEF = store_thm ("nzcv_BIR_ADD_Z_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_ADD_Z w1 w2 = awc_BIR_Z w1 w2 F``,
SIMP_TAC (std_ss++wordsLib.WORD_ss) [awc_BIR_Z_def, ADD_WITH_CARRY_SUB,
  nzcv_BIR_ADD_Z_def, nzcv_BIR_SUB_Z_def,
  nzcv_def, LET_THM, GSYM word_add_n2w, n2w_w2n]);

val nzcv_BIR_ADD_C_CARRY_DEF = store_thm ("nzcv_BIR_ADD_C_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_ADD_C w1 w2 = awc_BIR_C w1 w2 F``,
SIMP_TAC arith_ss [nzcv_BIR_ADD_C_def, add_with_carry_def, LET_THM,
   bir_auxiliaryTheory.BIT_ADD_WORD_CARRY, w2n_n2w, ZERO_LT_dimword,
   awc_BIR_C_def]);

val nzcv_BIR_ADD_V_CARRY_DEF = store_thm ("nzcv_BIR_ADD_V_CARRY_DEF",
  ``!w1 w2. nzcv_BIR_ADD_V w1 w2 = awc_BIR_V w1 w2 F``,
SIMP_TAC std_ss [add_with_carry_def, nzcv_BIR_ADD_V_def, LET_THM,
  GSYM word_add_def, awc_BIR_V_def] >>
METIS_TAC[]);


val awc_BIR_NZVC_INTROS = save_thm ("awc_BIR_NZVC_INTROS",
LIST_CONJ [
  nzcv_BIR_SUB_N_CARRY_DEF,
  nzcv_BIR_SUB_Z_CARRY_DEF,
  nzcv_BIR_SUB_V_CARRY_DEF,
  nzcv_BIR_SUB_C_CARRY_DEF,
  nzcv_BIR_ADD_N_CARRY_DEF,
  nzcv_BIR_ADD_Z_CARRY_DEF,
  nzcv_BIR_ADD_V_CARRY_DEF,
  nzcv_BIR_ADD_C_CARRY_DEF]);

val awc_BIR_NZVC_ELIMS = save_thm ("awc_BIR_NZVC_ELIMS",
GSYM awc_BIR_NZVC_INTROS);



(***********************)
(* Simple BIR rewrites *)
(***********************)

(* The nzcv tuple is defined in a way not easily expressable via
   BIR expressions. So let's introduce equivalent, easily expressable
   formulations. *)

val nzcv_BIR_SUB_N_raw = prove (
  ``!w1 w2. nzcv_BIR_SUB_N w1 w2 = (w1 - w2 < 0w)``,
SIMP_TAC std_ss [nzcv_BIR_SUB_N_def, nzcv_def, LET_THM, GSYM word_add_def, GSYM word_sub_def,
  word_msb_neg]);

val nzcv_BIR_SUB_Z_raw = prove (
  ``!w1 w2. nzcv_BIR_SUB_Z w1 w2 = (w1 - w2 = 0w)``,
SIMP_TAC std_ss [nzcv_BIR_SUB_Z_def, nzcv_def, LET_THM, GSYM word_add_def, GSYM word_sub_def,
  word_msb_neg]);

val nzcv_BIR_SUB_C_raw = prove (
  ``!w1 w2. nzcv_BIR_SUB_C w1 w2 = (w1 >=+ w2)``,
SIMP_TAC std_ss [nzcv_BIR_SUB_C_def, nzcv_def, word_hs_def, LET_THM]);

val nzcv_BIR_SUB_V_raw = prove (
  ``!w1 w2. nzcv_BIR_SUB_V w1 w2 = ((w1 - w2 < 0w) <=> (w1 >= w2))``,

SIMP_TAC std_ss [word_ge_def, GSYM nzcv_BIR_SUB_N_raw] >>
REPEAT STRIP_TAC >>
`?n z c v. (nzcv w1 w2 = (n, z, c, v))` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM, nzcv_BIR_SUB_V_def, nzcv_BIR_SUB_N_def] >>
METIS_TAC[]);


val nzcv_BIR_ADD_C_raw = prove (
  ``!w1 w2. (nzcv_BIR_ADD_C w1 w2 = (w1 >=+ -w2) /\ (w2 <> 0w))``,
REPEAT GEN_TAC >>
SIMP_TAC std_ss [nzcv_BIR_SUB_C_def, nzcv_def, LET_THM, nzcv_BIR_ADD_C_def,
  WORD_NEG_NEG, GSYM nzcv_BIR_SUB_C_raw, WORD_NEG_EQ_0] >>
Cases_on `w2 = 0w` >> ASM_REWRITE_TAC [] >>
SIMP_TAC std_ss [w2n_n2w, ZERO_LT_dimword] >>
MATCH_MP_TAC bitTheory.NOT_BIT_GT_TWOEXP >>
SIMP_TAC std_ss [GSYM dimword_def, w2n_lt]);


val nzcv_BIR_ADD_C_raw_aux = prove (``!w1 w2. ((w1 >=+ -w2) /\ (w2 <> 0w)) <=> (w1 >+ ~w2)``,
REPEAT Cases >>
ASM_SIMP_TAC arith_ss [WORD_HS, w2n_n2w, word_2comp_n2w, n2w_11,
  ZERO_LT_dimword] >>
ASM_SIMP_TAC (arith_ss++boolSimps.CONJ_ss) [] >>
ASM_SIMP_TAC arith_ss [word_1comp_n2w, w2n_n2w, word_hi_n2w]);


val awc_BIR_C_raw = prove (
  ``!w1 w2 c. awc_BIR_C w1 w2 c = (if c then w1 >=+ ~w2 else (w1 >+ ~w2))``,

REPEAT GEN_TAC >>
Tactical.REVERSE (Cases_on `c`) >> SIMP_TAC std_ss [awc_BIR_NZVC_ELIMS] >- (
  SIMP_TAC std_ss [nzcv_BIR_ADD_C_raw, nzcv_BIR_ADD_C_raw_aux]
) >>
Q.SUBGOAL_THEN `w2 = ~(~w2)` SUBST1_TAC >- REWRITE_TAC[WORD_NOT_NOT] >>
SIMP_TAC std_ss [awc_BIR_NZVC_ELIMS, nzcv_BIR_SUB_C_raw, WORD_NOT_NOT]);


val nzcv_BIR_SUB_V_raw = prove (
  ``!w1 w2. nzcv_BIR_SUB_V w1 w2 = ((w1 - w2 < 0w) <=> (w1 >= w2))``,

SIMP_TAC std_ss [word_ge_def, GSYM nzcv_BIR_SUB_N_raw] >>
REPEAT STRIP_TAC >>
`?n z c v. (nzcv w1 w2 = (n, z, c, v))` by METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [LET_THM, nzcv_BIR_SUB_V_def, nzcv_BIR_SUB_N_def] >>
METIS_TAC[]);


(* I don't have a good idea here, so let's use a dummy translation. *)
val nzcv_BIR_ADD_V_raw = prove (
  ``!w1 w2. nzcv_BIR_ADD_V w1 w2 = ((w1 < 0w <=> w2 < 0w) /\ (w1 + w2 < 0w <=/=> w1 < 0w))``,

SIMP_TAC std_ss [word_msb_neg, nzcv_BIR_ADD_V_def]);



(* So, after a few tiny changes to these raw rewrites, we get the following
   nice definitions *)

val nzcv_BIR_SUB_NZCV_REWRS = store_thm ("nzcv_BIR_SUB_NZCV_REWRS", ``
  (!w1 (w2:'a word). nzcv_BIR_SUB_N w1 w2 <=> w1 - w2 < 0w) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_Z w1 w2 <=> (w1 = w2)) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_C w1 w2 <=> w2 <=+ w1) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_V w1 w2 <=> (w1 - w2 < 0w <=> w2 <= w1))``,

SIMP_TAC std_ss [nzcv_BIR_SUB_V_raw, nzcv_BIR_SUB_N_raw,
  nzcv_BIR_SUB_Z_raw, nzcv_BIR_SUB_C_raw, WORD_HIGHER_EQ,
  WORD_GREATER_EQ, WORD_SUM_ZERO, word_sub_def, WORD_NEG_NEG]);


val nzcv_BIR_ADD_NZCV_REWRS = store_thm ("nzcv_BIR_ADD_NZCV_REWRS", ``
  (!w1 (w2:'a word). nzcv_BIR_ADD_N w1 w2 <=> w1 + w2 < 0w) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_Z w1 w2 <=> (w1 = -w2)) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_C w1 w2 <=> ~w2 <+ w1) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_V w1 w2 <=> ((w1 < 0w <=> w2 < 0w) /\ (w1 + w2 < 0w <=/=> w1 < 0w)))``,

SIMP_TAC std_ss [nzcv_BIR_SUB_NZCV_REWRS, nzcv_BIR_ADD_N_def,
  nzcv_BIR_ADD_Z_def, word_sub_def, WORD_NEG_NEG,
  nzcv_BIR_ADD_C_raw, nzcv_BIR_ADD_C_raw_aux,
  nzcv_BIR_ADD_V_raw, WORD_HIGHER
]);



val awc_BIR_NZCV_REWRS = store_thm ("awc_BIR_NZCV_REWRS", ``
  (!w1 (w2:'a word) c. awc_BIR_N w1 w2 c <=> w1 + w2 + (if c then 1w else 0w) < 0w) /\
  (!w1 (w2:'a word) c. awc_BIR_Z w1 w2 c <=> (w1 + w2 + (if c then 1w else 0w) = 0w)) /\
  (!w1 (w2:'a word) c. awc_BIR_C w1 w2 c <=> (if c then ~w2 <=+ w1 else (~w2 <+ w1))) /\
  (!w1 (w2:'a word) c. awc_BIR_V w1 w2 c <=> ((w1 < 0w <=> w2 < 0w) /\ (w1 + w2 + (if c then 1w else 0w) < 0w <=/=> w1 < 0w)))``,

SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [
  awc_BIR_N_def, awc_BIR_Z_def,
  awc_BIR_C_raw, awc_BIR_V_def, add_with_carry_def, LET_THM,
  word_msb_neg, GSYM word_add_n2w, n2w_w2n, WORD_HIGHER, WORD_HIGHER_EQ]);


val nzcv_BIR_ADD_SYM = store_thm ("nzcv_BIR_ADD_SYM", ``
  (!w1 (w2:'a word). nzcv_BIR_ADD_N w1 w2 <=> nzcv_BIR_ADD_N w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_Z w1 w2 <=> nzcv_BIR_ADD_Z w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_C w1 w2 <=> nzcv_BIR_ADD_C w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_ADD_V w1 w2 <=> nzcv_BIR_ADD_V w2 w1)``,

SIMP_TAC std_ss [nzcv_BIR_ADD_N_def, nzcv_def, LET_THM,
  nzcv_BIR_ADD_Z_def, nzcv_BIR_SUB_N_def, nzcv_BIR_ADD_C_def,
  nzcv_BIR_SUB_Z_def, WORD_NEG_NEG, nzcv_BIR_ADD_V_def,
  GSYM word_add_def] >>
METIS_TAC[wordsTheory.WORD_ADD_COMM, arithmeticTheory.ADD_COMM]);

val awc_BIR_NZCV_SYM = store_thm ("awc_BIR_NZCV_SYM", ``
  (!w1 (w2:'a word) c. awc_BIR_N w1 w2 c <=> awc_BIR_N w2 w1 c) /\
  (!w1 (w2:'a word) c. awc_BIR_Z w1 w2 c <=> awc_BIR_Z w2 w1 c) /\
  (!w1 (w2:'a word) c. awc_BIR_C w1 w2 c <=> awc_BIR_C w2 w1 c) /\
  (!w1 (w2:'a word) c. awc_BIR_V w1 w2 c <=> awc_BIR_V w2 w1 c)``,

SIMP_TAC (arith_ss++wordsLib.WORD_ss) [awc_BIR_N_def, awc_BIR_Z_def, awc_BIR_C_def,
  add_with_carry_def, LET_THM, GSYM word_add_n2w, n2w_w2n, awc_BIR_V_def] >>
METIS_TAC[]);

val awc_BIR_NZVC_ELIMS_SYM = store_thm ("awc_BIR_NZVC_ELIMS_SYM",
``(!w1 w2. awc_BIR_N (~w2) w1 T <=> nzcv_BIR_SUB_N w1 w2) /\
  (!w1 w2. awc_BIR_Z (~w2) w1 T <=> nzcv_BIR_SUB_Z w1 w2) /\
  (!w1 w2. awc_BIR_V (~w2) w1 T <=> nzcv_BIR_SUB_V w1 w2) /\
  (!w1 w2. awc_BIR_C (~w2) w1 T <=> nzcv_BIR_SUB_C w1 w2)``,

METIS_TAC[awc_BIR_NZCV_SYM, awc_BIR_NZVC_ELIMS]);


val nzcv_BIR_SUB_SYM = store_thm ("nzcv_BIR_ADD_SYM", ``
  (!w1 (w2:'a word). nzcv_BIR_SUB_N (~w1) (~w2) <=> nzcv_BIR_SUB_N w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_Z (~w1) (~w2) <=> nzcv_BIR_SUB_Z w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_C (~w1) (~w2) <=> nzcv_BIR_SUB_C w2 w1) /\
  (!w1 (w2:'a word). nzcv_BIR_SUB_V (~w1) (~w2) <=> nzcv_BIR_SUB_V w2 w1)``,

SIMP_TAC std_ss [awc_BIR_NZVC_INTROS, WORD_NOT_NOT] >>
SIMP_TAC std_ss [awc_BIR_NZVC_ELIMS_SYM, awc_BIR_NZVC_ELIMS]);



(*******************)
(* Simplifications *)
(*******************)

(* Special ones for immediate 0 *)
val nzcv_BIR_ADD_V_0 = store_thm ("nzcv_BIR_ADD_V_0",
  ``(!w. nzcv_BIR_ADD_V w 0w = F) /\
    (!w. nzcv_BIR_ADD_V 0w w = F)``,
SIMP_TAC arith_ss [nzcv_BIR_ADD_NZCV_REWRS,
   WORD_LESS_REFL, WORD_ADD_0]);

val nzcv_BIR_ADD_C_0 = store_thm ("nzcv_BIR_ADD_C_0",
  ``(!w. nzcv_BIR_ADD_C w 0w = F) /\
    (!w. nzcv_BIR_ADD_C 0w w = F)``,
SIMP_TAC arith_ss [nzcv_BIR_ADD_NZCV_REWRS,
  WORD_NOT_0, WORD_LS_T, WORD_NOT_LOWER, WORD_LO_word_0]);


val nzcv_BIR_ADD_Z_0 = store_thm ("nzcv_BIR_ADD_Z_0",
  ``(!w. nzcv_BIR_ADD_Z w 0w = (w = 0w)) /\
    (!w. nzcv_BIR_ADD_Z 0w w = (w = 0w))``,
SIMP_TAC arith_ss [nzcv_BIR_ADD_NZCV_REWRS, WORD_NEG_0] >>
METIS_TAC[WORD_NEG_EQ_0]);

val nzcv_BIR_ADD_N_0 = store_thm ("nzcv_BIR_ADD_N_0",
  ``(!w. nzcv_BIR_ADD_N w 0w = (word_msb w)) /\
    (!w. nzcv_BIR_ADD_N 0w w = (word_msb w))``,
SIMP_TAC arith_ss [nzcv_BIR_ADD_NZCV_REWRS, WORD_ADD_0, word_msb_neg]);


val nzcv_BIR_SUB_V_0 = store_thm ("nzcv_BIR_SUB_V_0",
  ``(!w:'a word. nzcv_BIR_SUB_V w 0w = F)``,

SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS,
  WORD_SUB_RZERO, WORD_ZERO_LE, GSYM word_msb_neg,
  WORD_MSB_INT_MIN_LS, WORD_LS, w2n_n2w,
  word_L_def, INT_MIN_LT_DIMWORD, WORD_SUB_LZERO]);


val nzcv_BIR_SUB_C_0 = store_thm ("nzcv_BIR_SUB_C_0",
  ``(!w. nzcv_BIR_SUB_C w 0w = T) /\
    (!w. nzcv_BIR_SUB_C 0w w = (w = 0w))``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS, WORD_0_LS,
  WORD_LS_word_0]);

val nzcv_BIR_SUB_Z_0 = store_thm ("nzcv_BIR_SUB_Z_0",
  ``(!w. nzcv_BIR_SUB_Z w 0w = (w = 0w)) /\
    (!w. nzcv_BIR_SUB_Z 0w w = (w = 0w))``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS] >>
METIS_TAC[]);

val nzcv_BIR_SUB_N_0 = store_thm ("nzcv_BIR_SUB_N_0",
  ``(!w. nzcv_BIR_SUB_N w 0w = (word_msb w)) /\
    (!w. nzcv_BIR_SUB_N 0w w = (word_msb (-w)))``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS,
  WORD_SUB_RZERO, WORD_SUB_LZERO, word_msb_neg]);


(* Special ones for immediate same args *)
val nzcv_BIR_SUB_Z_ID = store_thm ("nzcv_BIR_SUB_Z_ID",
  ``!w. nzcv_BIR_SUB_Z w w = T``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS]);

val nzcv_BIR_SUB_N_ID = store_thm ("nzcv_BIR_SUB_N_ID",
  ``!w. nzcv_BIR_SUB_N w w = F``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS, WORD_SUB_REFL,
  WORD_LESS_REFL]);

val nzcv_BIR_SUB_C_ID = store_thm ("nzcv_BIR_SUB_C_ID",
  ``!w. nzcv_BIR_SUB_C w w = T``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS, WORD_LOWER_EQ_REFL]);

val nzcv_BIR_SUB_V_ID = store_thm ("nzcv_BIR_SUB_V_ID",
  ``!w. nzcv_BIR_SUB_V w w = F``,
SIMP_TAC arith_ss [nzcv_BIR_SUB_NZCV_REWRS, WORD_LESS_EQ_REFL,
  WORD_SUB_REFL, WORD_LESS_REFL]);


val nzcv_BIR_SIMPS = save_thm ("nzcv_BIR_SIMPS",
LIST_CONJ [
  nzcv_BIR_SUB_Z_ID,
  nzcv_BIR_SUB_N_ID,
  nzcv_BIR_SUB_C_ID,
  nzcv_BIR_SUB_V_ID,
  nzcv_BIR_ADD_V_0,
  nzcv_BIR_ADD_C_0,
  nzcv_BIR_ADD_N_0,
  nzcv_BIR_ADD_Z_0,
  nzcv_BIR_SUB_V_0,
  nzcv_BIR_SUB_C_0,
  nzcv_BIR_SUB_N_0,
  nzcv_BIR_SUB_Z_0,
  awc_BIR_NZVC_ELIMS,
  awc_BIR_NZVC_ELIMS_SYM
]);


(*************************)
(* Conditional Codes SUB *)
(*************************)

(* It might be useful to not expand the nzcv_BIR_SUB predicates during
   analysis of BIR programs, since they allow to simplify conditional
   codes as shown below. *)

val nzcv_SUB_COND_CODE_EQ_def    = Define `nzcv_SUB_COND_CODE_EQ    w1 w2 <=> nzcv_BIR_SUB_Z w1 w2`;
val nzcv_SUB_COND_CODE_NE_def    = Define `nzcv_SUB_COND_CODE_NE    w1 w2 <=> ~(nzcv_BIR_SUB_Z w1 w2)`;
val nzcv_SUB_COND_CODE_CS_HS_def = Define `nzcv_SUB_COND_CODE_CS_HS w1 w2 <=> nzcv_BIR_SUB_C w1 w2`;
val nzcv_SUB_COND_CODE_CC_LO_def = Define `nzcv_SUB_COND_CODE_CC_LO w1 w2 <=> ~(nzcv_BIR_SUB_C w1 w2)`;
val nzcv_SUB_COND_CODE_MI_def    = Define `nzcv_SUB_COND_CODE_MI    w1 w2 <=> (nzcv_BIR_SUB_N w1 w2)`;
val nzcv_SUB_COND_CODE_PL_def    = Define `nzcv_SUB_COND_CODE_PL    w1 w2 <=> ~(nzcv_BIR_SUB_N w1 w2)`;
val nzcv_SUB_COND_CODE_VS_def    = Define `nzcv_SUB_COND_CODE_VS    w1 w2 <=> (nzcv_BIR_SUB_V w1 w2)`;
val nzcv_SUB_COND_CODE_VC_def    = Define `nzcv_SUB_COND_CODE_VC    w1 w2 <=> ~(nzcv_BIR_SUB_V w1 w2)`;
val nzcv_SUB_COND_CODE_HI_def    = Define `nzcv_SUB_COND_CODE_HI    w1 w2 <=> (nzcv_BIR_SUB_C w1 w2) /\ ~(nzcv_BIR_SUB_Z w1 w2)`;
val nzcv_SUB_COND_CODE_LS_def    = Define `nzcv_SUB_COND_CODE_LS    w1 w2 <=> ~(nzcv_BIR_SUB_C w1 w2) \/ (nzcv_BIR_SUB_Z w1 w2)`;
val nzcv_SUB_COND_CODE_GE_def    = Define `nzcv_SUB_COND_CODE_GE    w1 w2 <=> (nzcv_BIR_SUB_N w1 w2 <=> nzcv_BIR_SUB_V w1 w2)`;
val nzcv_SUB_COND_CODE_LT_def    = Define `nzcv_SUB_COND_CODE_LT    w1 w2 <=> ~(nzcv_BIR_SUB_N w1 w2 <=> nzcv_BIR_SUB_V w1 w2)`;
val nzcv_SUB_COND_CODE_GT_def    = Define `nzcv_SUB_COND_CODE_GT    w1 w2 <=> (((nzcv_BIR_SUB_N w1 w2 <=> nzcv_BIR_SUB_V w1 w2)) /\ ~(nzcv_BIR_SUB_Z w1 w2))`;

val nzcv_SUB_COND_CODE_LE_def    = Define `nzcv_SUB_COND_CODE_LE    w1 w2 <=> (~((nzcv_BIR_SUB_N w1 w2 <=> nzcv_BIR_SUB_V w1 w2)) \/ (nzcv_BIR_SUB_Z w1 w2))`;

val nzcv_SUB_COND_CODE_AL_def    = Define `nzcv_SUB_COND_CODE_AL    (w1 : 'a word) (w2:'a word) <=> T`;



val nzcv_SUB_COND_CODE_EVALS = store_thm ("nzcv_SUB_COND_CODE_EVALS", ``
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_EQ    w1 w2 <=> (w1 = w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_NE    w1 w2 <=> ~(w1 = w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_CS_HS w1 w2 <=> (w2 <=+ w1))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_CC_LO w1 w2 <=> (w1 <+ w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_MI    w1 w2 <=> (w1 - w2 < 0w))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_PL    w1 w2 <=> (0w <= w1 - w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_VS    w1 w2 <=> (nzcv_BIR_SUB_V w1 w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_VC    w1 w2 <=> ~(nzcv_BIR_SUB_V w1 w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_HI    w1 w2 <=> (w1 >+ w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_LS    w1 w2 <=> (w1 <=+ w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_GE    w1 w2 <=> (w1 >= w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_LT    w1 w2 <=> (w1 < w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_GT    w1 w2 <=> (w1 > w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_LE    w1 w2 <=> (w1 <= w2))) /\
(!(w1:'a word) (w2:'a word). (nzcv_SUB_COND_CODE_AL    w1 w2 <=> T))``,

(* First get all the negations and compositions of the way *)
SIMP_TAC std_ss [
  nzcv_SUB_COND_CODE_AL_def,
  GSYM nzcv_SUB_COND_CODE_EQ_def,
  nzcv_SUB_COND_CODE_NE_def,
  GSYM nzcv_SUB_COND_CODE_CS_HS_def,
  nzcv_SUB_COND_CODE_CC_LO_def,
  GSYM nzcv_SUB_COND_CODE_MI_def,
  nzcv_SUB_COND_CODE_PL_def,
  GSYM nzcv_SUB_COND_CODE_VS_def,
  nzcv_SUB_COND_CODE_VC_def,
  GSYM nzcv_SUB_COND_CODE_HI_def,
  nzcv_SUB_COND_CODE_LS_def,
  GSYM nzcv_SUB_COND_CODE_GE_def,
  nzcv_SUB_COND_CODE_LT_def,
  nzcv_SUB_COND_CODE_GT_def,
  nzcv_SUB_COND_CODE_LE_def] >>
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
  WORD_NOT_LOWER_EQUAL,
  WORD_NOT_LESS_EQUAL,
  WORD_GREATER_EQ,
  WORD_HIGHER,
  WORD_GREATER,
  WORD_NOT_LOWER,
  WORD_NOT_LESS,
  WORD_LESS_OR_EQ,
  WORD_LOWER_OR_EQ,
  WORD_LESS_NOT_EQ] >>

(* Now the real work *)
SIMP_TAC std_ss [nzcv_BIR_SUB_NZCV_REWRS,
  nzcv_SUB_COND_CODE_EQ_def,
  nzcv_SUB_COND_CODE_CS_HS_def,
  nzcv_SUB_COND_CODE_MI_def,
  nzcv_SUB_COND_CODE_HI_def,
  nzcv_SUB_COND_CODE_GE_def,

  WORD_LOWER_OR_EQ,
  WORD_GREATER_OR_EQ,
  WORD_LESS_OR_EQ
] >>
REPEAT CONJ_TAC >| [
  SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WORD_LOWER_NOT_EQ],
  SIMP_TAC (std_ss++boolSimps.CONJ_ss) [WORD_LOWER_NOT_EQ],
  METIS_TAC[]
]);




(*******************)
(* Expressions SUB *)
(*******************)


(* We can now define expressions for the nzcv flags *)
val BExp_nzcv_SUB_N_def = Define `BExp_nzcv_SUB_N sz e1 e2 =
   BExp_BinPred BIExp_SignedLessThan (BExp_BinExp BIExp_Minus e1 e2)
        (BExp_Const (n2bs 0 sz))`;

val BExp_nzcv_SUB_Z_def = Define `BExp_nzcv_SUB_Z e1 e2 =
   BExp_BinPred BIExp_Equal e1 e2`;

val BExp_nzcv_SUB_C_def = Define `BExp_nzcv_SUB_C e1 e2 =
   BExp_BinPred BIExp_LessOrEqual e2 e1`;

val BExp_nzcv_SUB_V_def = Define `BExp_nzcv_SUB_V sz e1 e2 =
(BExp_BinPred BIExp_Equal
        (BExp_BinPred BIExp_SignedLessThan
           (BExp_BinExp BIExp_Minus e1 e2) (BExp_Const (n2bs 0 sz)))
        (BExp_BinPred BIExp_SignedLessOrEqual e2 e1))`;


val BExp_nzcv_SUB_DEFS = save_thm ("BExp_nzcv_SUB_DEFS",
  LIST_CONJ [BExp_nzcv_SUB_N_def, BExp_nzcv_SUB_Z_def, BExp_nzcv_SUB_C_def, BExp_nzcv_SUB_V_def]);


val BExp_nzcv_SUB_type_of = store_thm ("BExp_nzcv_SUB_type_of",``
(!sz e1 e2. (type_of_bir_exp (BExp_nzcv_SUB_N sz e1 e2) = (if
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))) /\

(!sz e1 e2. (type_of_bir_exp (BExp_nzcv_SUB_V sz e1 e2) = if
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2. (type_of_bir_exp (BExp_nzcv_SUB_Z e1 e2) = if
    ?sz. (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
         (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2. (type_of_bir_exp (BExp_nzcv_SUB_C e1 e2) = if
    ?sz. (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
         (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))``,

SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_SUB_DEFS, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));




val BExp_nzcv_SUB_vars_of = store_thm ("BExp_nzcv_SUB_vars_of",``
(!sz e1 e2. (bir_vars_of_exp (BExp_nzcv_SUB_N sz e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!sz e1 e2. (bir_vars_of_exp (BExp_nzcv_SUB_V sz e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!e1 e2. (bir_vars_of_exp (BExp_nzcv_SUB_Z e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!e1 e2. (bir_vars_of_exp (BExp_nzcv_SUB_C e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2)))``,

SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [BExp_nzcv_SUB_DEFS,
  EXTENSION, IN_UNION, NOT_IN_EMPTY]);



val BExp_nzcv_SUB_N_eval = store_thm ("BExp_nzcv_SUB_N_eval",
``!sz e1 e2 env.
  (bir_eval_exp (BExp_nzcv_SUB_N sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_N w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_SUB_N_def, nzcv_BIR_SUB_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val BExp_nzcv_SUB_V_eval = store_thm ("BExp_nzcv_SUB_V_eval",
``!sz e1 e2 env.
  (bir_eval_exp (BExp_nzcv_SUB_V sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_V w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_SUB_V_def, nzcv_BIR_SUB_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def, bool2w_11]
));

val BExp_nzcv_SUB_Z_eval = store_thm ("BExp_nzcv_SUB_Z_eval",
``!e1 e2 env.
  (bir_eval_exp (BExp_nzcv_SUB_Z e1 e2) env =
     case (bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | (BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | (BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | (BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | (BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | (BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_Z w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_SUB_Z_def, nzcv_BIR_SUB_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def, bool2w_11]
));


val BExp_nzcv_SUB_C_eval = store_thm ("BExp_nzcv_SUB_C_eval",
``!e1 e2 env.
  (bir_eval_exp (BExp_nzcv_SUB_C e1 e2) env =
     case (bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | (BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | (BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | (BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | (BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | (BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_SUB_C w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_SUB_C_def, nzcv_BIR_SUB_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) []
));



(*******************)
(* Expressions ADD *)
(*******************)

(* We can now define expressions for the nzcv flags *)
val BExp_nzcv_ADD_N_def = Define `BExp_nzcv_ADD_N sz e1 e2 =
   BExp_BinPred BIExp_SignedLessThan (BExp_BinExp BIExp_Plus e1 e2)
        (BExp_Const (n2bs 0 sz))`;

val BExp_nzcv_ADD_Z_def = Define `BExp_nzcv_ADD_Z e1 e2 =
   BExp_BinPred BIExp_Equal e1 (BExp_UnaryExp BIExp_ChangeSign e2)`;


val BExp_nzcv_ADD_C_def = Define `BExp_nzcv_ADD_C e1 e2 =
   BExp_BinPred BIExp_LessThan (BExp_UnaryExp BIExp_Not e2) e1`;

val BExp_nzcv_ADD_V_def = Define `BExp_nzcv_ADD_V sz e1 e2 =
     (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
           (BExp_BinPred BIExp_SignedLessThan e1
              (BExp_Const (n2bs 0 sz)))
           (BExp_BinPred BIExp_SignedLessThan e2
              (BExp_Const (n2bs 0 sz))))
        (
           (BExp_BinPred BIExp_NotEqual
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Plus e1 e2) (BExp_Const (n2bs 0 sz)))
              (BExp_BinPred BIExp_SignedLessThan e1
                 (BExp_Const (n2bs 0 sz))))))`


val BExp_nzcv_ADD_DEFS = save_thm ("BExp_nzcv_ADD_DEFS",
  LIST_CONJ [BExp_nzcv_ADD_N_def, BExp_nzcv_ADD_Z_def, BExp_nzcv_ADD_C_def, BExp_nzcv_ADD_V_def]);


val BExp_nzcv_ADD_type_of = store_thm ("BExp_nzcv_ADD_type_of",``
(!sz e1 e2. (type_of_bir_exp (BExp_nzcv_ADD_N sz e1 e2) = (if
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))) /\

(!sz e1 e2. (type_of_bir_exp (BExp_nzcv_ADD_V sz e1 e2) = if
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2. (type_of_bir_exp (BExp_nzcv_ADD_Z e1 e2) = if
    ?sz. (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
         (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2. (type_of_bir_exp (BExp_nzcv_ADD_C e1 e2) = if
    ?sz. (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
         (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))``,

SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_ADD_DEFS, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val BExp_nzcv_ADD_vars_of = store_thm ("BExp_nzcv_ADD_vars_of",``
(!sz e1 e2. (bir_vars_of_exp (BExp_nzcv_ADD_N sz e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!sz e1 e2. (bir_vars_of_exp (BExp_nzcv_ADD_V sz e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!e1 e2. (bir_vars_of_exp (BExp_nzcv_ADD_Z e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2))) /\

(!e1 e2. (bir_vars_of_exp (BExp_nzcv_ADD_C e1 e2) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2)))``,

SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [BExp_nzcv_ADD_DEFS,
  EXTENSION, IN_UNION, NOT_IN_EMPTY]);



val BExp_nzcv_ADD_N_eval = store_thm ("BExp_nzcv_ADD_N_eval",
``!sz e1 e2 env.
  (bir_eval_exp (BExp_nzcv_ADD_N sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_N w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_ADD_N_def, nzcv_BIR_ADD_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val BExp_nzcv_ADD_V_eval = store_thm ("BExp_nzcv_ADD_V_eval",
``!sz e1 e2 env.
  (bir_eval_exp (BExp_nzcv_ADD_V sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_V w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_ADD_V_def, nzcv_BIR_ADD_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [
     bir_bin_pred_BOOL_OPER_EVAL,
     bir_unary_exp_BOOL_OPER_EVAL,
     bir_bin_exp_BOOL_OPER_EVAL]
));


val BExp_nzcv_ADD_Z_eval = store_thm ("BExp_nzcv_ADD_Z_eval",
``!e1 e2 env.
  (bir_eval_exp (BExp_nzcv_ADD_Z e1 e2) env =
     case (bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | (BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | (BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | (BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | (BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | (BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_Z w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_ADD_Z_def, nzcv_BIR_ADD_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2b_def, bool2w_11]
));


val BExp_nzcv_ADD_C_eval = store_thm ("BExp_nzcv_ADD_C_eval",
``!e1 e2 env.
  (bir_eval_exp (BExp_nzcv_ADD_C e1 e2) env =
     case (bir_eval_exp e1 env, bir_eval_exp e2 env) of
         (BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | (BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | (BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | (BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | (BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | (BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2)) =>
            BVal_Imm (bool2b (nzcv_BIR_ADD_C w1 w2))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_nzcv_ADD_C_def, nzcv_BIR_ADD_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) []
));



(******************************)
(* Expressions ADD WITH CARRY *)
(******************************)

(* We can now define expressions for the nzcv flags *)
val BExp_ADD_WITH_CARRY_N_def = Define `BExp_ADD_WITH_CARRY_N sz e1 e2 ec =
   BExp_BinPred BIExp_SignedLessThan (BExp_BinExp BIExp_Plus e1
        (BExp_BinExp BIExp_Plus e2 (BExp_IfThenElse ec (BExp_Const (n2bs 1 sz)) (BExp_Const (n2bs 0 sz)))))
        (BExp_Const (n2bs 0 sz))`;

val BExp_ADD_WITH_CARRY_Z_def = Define `BExp_ADD_WITH_CARRY_Z sz e1 e2 ec =
   BExp_BinPred BIExp_Equal (BExp_BinExp BIExp_Plus e1
        (BExp_BinExp BIExp_Plus e2 (BExp_IfThenElse ec (BExp_Const (n2bs 1 sz)) (BExp_Const (n2bs 0 sz)))))
        (BExp_Const (n2bs 0 sz))`;


val BExp_ADD_WITH_CARRY_C_def = Define `BExp_ADD_WITH_CARRY_C e1 e2 ec =
   BExp_IfThenElse ec
     (BExp_BinPred BIExp_LessOrEqual (BExp_UnaryExp BIExp_Not e2) e1)
     (BExp_BinPred BIExp_LessThan (BExp_UnaryExp BIExp_Not e2) e1)`;


val BExp_ADD_WITH_CARRY_V_def = Define `BExp_ADD_WITH_CARRY_V sz e1 e2 ec =
     (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
           (BExp_BinPred BIExp_SignedLessThan e1
              (BExp_Const (n2bs 0 sz)))
           (BExp_BinPred BIExp_SignedLessThan e2
              (BExp_Const (n2bs 0 sz))))
        (BExp_BinPred BIExp_NotEqual
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Plus e1
                    (BExp_BinExp BIExp_Plus e2 (BExp_IfThenElse ec (BExp_Const (n2bs 1 sz)) (BExp_Const (n2bs 0 sz)))))
                  (BExp_Const (n2bs 0 sz)))
              (BExp_BinPred BIExp_SignedLessThan e1
                 (BExp_Const (n2bs 0 sz)))))`;


val BExp_ADD_WITH_CARRY_DEFS = save_thm ("BExp_ADD_WITH_CARRY_DEFS",
  LIST_CONJ [BExp_ADD_WITH_CARRY_N_def,
             BExp_ADD_WITH_CARRY_Z_def,
             BExp_ADD_WITH_CARRY_C_def,
             BExp_ADD_WITH_CARRY_V_def]);


val BExp_ADD_WITH_CARRY_type_of = store_thm ("BExp_ADD_WITH_CARRY_type_of",``
(!sz e1 e2 ec. (type_of_bir_exp (BExp_ADD_WITH_CARRY_N sz e1 e2 ec) = (if
    (type_of_bir_exp ec = SOME BType_Bool) /\
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))) /\

(!sz e1 e2 ec. (type_of_bir_exp (BExp_ADD_WITH_CARRY_V sz e1 e2 ec) = if
    (type_of_bir_exp ec = SOME BType_Bool) /\
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2 ec sz.
    (type_of_bir_exp (BExp_ADD_WITH_CARRY_Z sz e1 e2 ec) = if
    (type_of_bir_exp ec = SOME BType_Bool) /\
    (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
    (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)) /\

(!e1 e2 ec. (type_of_bir_exp (BExp_ADD_WITH_CARRY_C e1 e2 ec) = if
    ?sz. (type_of_bir_exp ec = SOME BType_Bool) /\
         (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
         (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME BType_Bool else NONE))``,

SIMP_TAC (std_ss++holBACore_ss) [BExp_ADD_WITH_CARRY_DEFS, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val BExp_ADD_WITH_CARRY_vars_of = store_thm ("BExp_ADD_WITH_CARRY_vars_of",``
(!sz e1 e2 ec. (bir_vars_of_exp (BExp_ADD_WITH_CARRY_N sz e1 e2 ec) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2 UNION bir_vars_of_exp ec))) /\

(!sz e1 e2 ec. (bir_vars_of_exp (BExp_ADD_WITH_CARRY_V sz e1 e2 ec) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2 UNION bir_vars_of_exp ec))) /\

(!sz e1 e2 ec. (bir_vars_of_exp (BExp_ADD_WITH_CARRY_Z sz e1 e2 ec) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2 UNION bir_vars_of_exp ec))) /\

(!e1 e2 ec. (bir_vars_of_exp (BExp_ADD_WITH_CARRY_C e1 e2 ec) = (
    bir_vars_of_exp e1 UNION bir_vars_of_exp e2 UNION bir_vars_of_exp ec)))``,

SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [BExp_ADD_WITH_CARRY_DEFS,
  EXTENSION, IN_UNION, NOT_IN_EMPTY]);



val BExp_ADD_WITH_CARRY_N_eval = store_thm ("BExp_ADD_WITH_CARRY_N_eval",
``!sz e1 e2 ec env.
  (bir_eval_exp (BExp_ADD_WITH_CARRY_N sz e1 e2 ec) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env, bir_dest_bool_val (bir_eval_exp ec env)) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_N w1 w2 c))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ADD_WITH_CARRY_N_def, awc_BIR_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++boolSimps.LIFT_COND_ss) []
));


val BExp_ADD_WITH_CARRY_V_eval = store_thm ("BExp_ADD_WITH_CARRY_V_eval",
``!sz e1 e2 ec env.
  (bir_eval_exp (BExp_ADD_WITH_CARRY_V sz e1 e2 ec) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env, bir_dest_bool_val (bir_eval_exp ec env)) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_V w1 w2 c))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ADD_WITH_CARRY_V_def, awc_BIR_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [
     bir_bin_pred_BOOL_OPER_EVAL,
     bir_unary_exp_BOOL_OPER_EVAL,
     bir_bin_exp_BOOL_OPER_EVAL]
));


val BExp_ADD_WITH_CARRY_Z_eval = store_thm ("BExp_ADD_WITH_CARRY_Z_eval",
``!sz e1 e2 ec env.
  (bir_eval_exp (BExp_ADD_WITH_CARRY_Z sz e1 e2 ec) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env, bir_dest_bool_val (bir_eval_exp ec env)) of
         (Bit1, BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | (Bit8, BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | (Bit16, BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | (Bit32, BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | (Bit64, BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | (Bit128, BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_Z w1 w2 c))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ADD_WITH_CARRY_Z_def, awc_BIR_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++boolSimps.LIFT_COND_ss) []
));


val BExp_ADD_WITH_CARRY_C_eval = store_thm ("BExp_ADD_WITH_CARRY_C_eval",
``!e1 e2 ec env.
  (bir_eval_exp (BExp_ADD_WITH_CARRY_C e1 e2 ec) env =
     case (bir_eval_exp e1 env, bir_eval_exp e2 env, bir_dest_bool_val (bir_eval_exp ec env)) of
         (BVal_Imm (Imm1 w1), BVal_Imm (Imm1 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | (BVal_Imm (Imm8 w1), BVal_Imm (Imm8 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | (BVal_Imm (Imm16 w1), BVal_Imm (Imm16 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | (BVal_Imm (Imm32 w1), BVal_Imm (Imm32 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | (BVal_Imm (Imm64 w1), BVal_Imm (Imm64 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | (BVal_Imm (Imm128 w1), BVal_Imm (Imm128 w2), SOME c) =>
            BVal_Imm (bool2b (awc_BIR_C w1 w2 c))
       | _ => BVal_Unknown)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ADD_WITH_CARRY_C_def, awc_BIR_NZCV_REWRS] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) []
));



val _ = export_theory();
