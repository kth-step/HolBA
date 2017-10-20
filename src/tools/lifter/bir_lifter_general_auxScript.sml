open HolKernel Parse boolLib bossLib;
open sortingTheory listTheory
open bir_programTheory
open wordsTheory
open HolBACoreSimps

(* This theory contains auxiliary definitions
   and lemmata used by the lifter which don't
   belong in any specific theory. *)

val _ = new_theory "bir_lifter_general_aux";


(****************************)
(* A protected if-then-else *)
(****************************)

(* For merging multiple step theorems, a top-level if-then-else is
   handy. However, one has to be careful how to use this if-then-else.
   One does not want to use it for conditional rewriting, otherwise, one
   might get aritfacts like

   ms'.REG 0 = if (ms.REG 0 = 0w) then 0w else ms.REG 0

   instead of

   ms'.REG 0 = ms.REG 0

   Moreover, one needs to be careful how to evaluate terms like

   (if c then ms1 else ms2).REG 0

   If lifting of if-then-else is used naively, there might be trouble with
   conditions in ms1 or ms2.

   After attempts with specialised rewrite rules and markers lead to very
   large and complicated code, below a new if-then-else constant is introduced.
   The simplifier does not know anything about this new constant and
   rewrite rules can distinguish between it and common if-then-else expressions
   while lifting. *)

val PROTECTED_COND_def = Define `PROTECTED_COND = $COND`

val PROTECTED_COND_ID = store_thm ("PROTECTED_COND_ID",
``!c t. PROTECTED_COND c t t = t``,
SIMP_TAC std_ss [PROTECTED_COND_def]);

val PROTECTED_COND_RAND = store_thm ("PROTECTED_COND_RAND",
``!f b x y. f (PROTECTED_COND b x y) = PROTECTED_COND b (f x) (f y)``,
SIMP_TAC std_ss [PROTECTED_COND_def, COND_RAND]);

val PROTECTED_COND_RATOR = store_thm ("PROTECTED_COND_RATOR",
``!b f g x. (PROTECTED_COND b f g) x = PROTECTED_COND b (f x) (g x)``,
SIMP_TAC std_ss [PROTECTED_COND_def, COND_RATOR]);

val PROTECTED_COND_NEG_COND = store_thm ("PROTECTED_COND_NEG_COND",
``!b x y. (PROTECTED_COND (~b) x y) = PROTECTED_COND b y x``,

Cases >>
SIMP_TAC std_ss [PROTECTED_COND_def]);


val PROTECTED_COND_NEG_COND_CONJ = store_thm ("PROTECTED_COND_NEG_COND_CONJ",
``!b1 b2 x y. (PROTECTED_COND (~b1 \/ ~b2) x y) = PROTECTED_COND (b1 /\ b2) y x``,

Cases >> Cases >>
SIMP_TAC std_ss [PROTECTED_COND_def]);


val COMBINE_TWO_STEP_THMS_SIMPLE = store_thm ("COMBINE_TWO_STEP_THMS_SIMPLE",
``!next cond1 cond2 ms ms1 ms2.
     (cond1 ==> (next ms = SOME ms1)) ==>
     (cond2 ==> (next ms = SOME ms2)) ==>
     (cond1 <=> ~cond2) ==>
     (next ms = SOME (PROTECTED_COND cond1 ms1 ms2))``,

REPEAT STRIP_TAC >>
Cases_on `cond2` >> FULL_SIMP_TAC std_ss [PROTECTED_COND_def]);




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



val w2w_REMOVE_FOLDS = save_thm ("w2w_REMOVE_FOLDS",
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



val _ = export_theory();
