open HolKernel Parse boolLib bossLib;
open sortingTheory listTheory
open bir_programTheory
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


val _ = export_theory();
