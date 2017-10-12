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



(***************************************)
(* Show that set of labels is distinct *)
(***************************************)

(* If we show naively that the set of labels of a program is distinct,
   we need quadratic time in the length of the program. It is very slow.
   We need something more fancy. The lifter produces labels in an ordered
   form. We can just translate address labels to ints and check that these are
   sorted. This is much faster. For string labels, we can't do much, though. *)

val bir_labels_of_program_EVAL = store_thm ("bir_labels_of_program_EVAL",
 ``(bir_labels_of_program (BirProgram []) = []) /\
   (bir_labels_of_program (BirProgram (bl::bls)) =
    bl.bb_label :: (bir_labels_of_program (BirProgram bls)))``,
SIMP_TAC list_ss [bir_programTheory.bir_labels_of_program_def])


val ALL_DISTINCT_lifter_labels_list_PART_def = Define `
(ALL_DISTINCT_lifter_labels_list_PART nl sl [] = (nl, sl)) /\
(ALL_DISTINCT_lifter_labels_list_PART nl sl ((BL_Address i)::ls) <=> (
   ALL_DISTINCT_lifter_labels_list_PART ((b2n i)::nl) sl ls)) /\
(ALL_DISTINCT_lifter_labels_list_PART nl sl ((BL_Label s)::ls) <=> (
   ALL_DISTINCT_lifter_labels_list_PART nl (s::sl) ls))`;


val PERM_PARTITION = store_thm ("PERM_PARTITION",
``!P l. PERM (FILTER P l ++ FILTER (\x. ~(P x)) l) l``,

GEN_TAC >>
Induct >- (
  SIMP_TAC list_ss [PERM_REFL]
) >>
GEN_TAC >>
rename1 `x::xs` >>
Cases_on `P x` >- (
  ASM_SIMP_TAC list_ss [PERM_CONS_IFF]
) >- (
  ASM_SIMP_TAC list_ss [PERM_FUN_APPEND_CONS, PERM_CONS_IFF]
));

val ALL_DISTINCT_lifter_labels_list_PART_ALT_DEF = store_thm ("ALL_DISTINCT_lifter_labels_list_PART_ALT_DEF",
``!ll nl sl.
  ALL_DISTINCT_lifter_labels_list_PART nl sl ll =
  ((REVERSE (MAP (\ll. case ll of BL_Address a => b2n a) (FILTER IS_BL_Address ll))) ++ nl,
   (REVERSE (MAP (\ll. case ll of BL_Label s => s) (FILTER (\l. ~(IS_BL_Address l)) ll))) ++ sl)``,

Induct >- (
  SIMP_TAC list_ss [ALL_DISTINCT_lifter_labels_list_PART_def]
) >>
Cases >> (
  ASM_SIMP_TAC (list_ss++bir_TYPES_ss) [ALL_DISTINCT_lifter_labels_list_PART_def,
    IS_BL_Label_def, IS_BL_Address_def] >>
  SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND]
));


val ALL_DISTINCT_lifter_label_list_PARTS_THM = store_thm ("ALL_DISTINCT_lifter_label_list_PARTS_THM",
``!ll nl sl.
  (ALL_DISTINCT_lifter_labels_list_PART [] [] ll = (nl, sl)) ==>
  (ALL_DISTINCT sl /\  SORTED ($>) nl) ==>
  ALL_DISTINCT ll``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [ALL_DISTINCT_lifter_labels_list_PART_ALT_DEF] >>
Q.SUBGOAL_THEN `ALL_DISTINCT ll =
  ALL_DISTINCT ((FILTER IS_BL_Address ll) ++ (FILTER (\x. ~(IS_BL_Address x)) ll))` SUBST1_TAC >- (

  MATCH_MP_TAC ALL_DISTINCT_PERM >>
  ONCE_REWRITE_TAC [PERM_SYM] >>
  METIS_TAC[PERM_PARTITION]
) >>

`ALL_DISTINCT nl` by (
  IRULE_TAC SORTED_ALL_DISTINCT >>
  Q.EXISTS_TAC `$>` >>
  ASM_SIMP_TAC arith_ss [relationTheory.irreflexive_def,
    relationTheory.transitive_def]
) >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>
FULL_SIMP_TAC list_ss [ALL_DISTINCT_REVERSE, ALL_DISTINCT_APPEND,
  MEM_FILTER] >>
METIS_TAC[ALL_DISTINCT_MAP])


val _ = export_theory();
