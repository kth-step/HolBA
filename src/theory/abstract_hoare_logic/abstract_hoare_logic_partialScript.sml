open HolKernel Parse boolLib bossLib;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

open abstract_hoare_logicTheory;

val _ = new_theory "abstract_hoare_logic_partial";

val weak_rel_steps_def = Define `
  weak_rel_steps m ms ls ms' n =
          ((n > 0 /\
           FUNPOW_OPT m.trs n ms = SOME ms' /\
           m.pc ms' IN ls) /\
           !n'.
             (n' < n /\ n' > 0 ==>
             ?ms''.
               FUNPOW_OPT m.trs n' ms = SOME ms'' /\
               ~(m.pc ms'' IN ls)
             ))`;

val weak_rel_steps_equiv = prove(``
  !m ms ls ms'.
  weak_model m ==>
  (m.weak ms ls ms' <=>
  ?n. weak_rel_steps m ms ls ms' n)
  ``,

REPEAT STRIP_TAC >>
EQ_TAC >> (
 STRIP_TAC
) >| [
 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 Q.EXISTS_TAC `n` >>
 fs [weak_rel_steps_def],

 PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
 fs [weak_rel_steps_def] >>
 Q.EXISTS_TAC `n` >>
 REPEAT STRIP_TAC >> (
  fs []
 )
]
);

val weak_rel_steps_imp = prove(``
  !m ms ls ms' n.
  weak_model m ==>
  (weak_rel_steps m ms ls ms' n ==>
   m.weak ms ls ms')
  ``,

REPEAT STRIP_TAC >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP (fst $ EQ_IMP_RULE (Q.SPEC `m` weak_model_def)) thm]) >>
Q.EXISTS_TAC `n` >>
fs [weak_rel_steps_def]
);

val weak_rel_steps_label = prove(``
  !m ms ls ms' n.
  weak_model m ==>
  weak_rel_steps m ms ls ms' n ==>
  m.pc ms' IN ls
  ``,

fs [weak_rel_steps_def]
);

(* Returns a list of n successive applications of f on s *)
(* Hard for proofs?
val FUNPOW_OPT_LIST_def = Define `
 (FUNPOW_OPT_LIST f 0 s = SOME [s]) /\
 (FUNPOW_OPT_LIST f (SUC n) s =
  case f s of
  | SOME res_hd =>
   (case FUNPOW_OPT_LIST f n res_hd of
    | SOME res_tl => SOME (res_hd::res_tl)
    | NONE => NONE)
  | NONE => NONE)`;
*)

(* Head-recursive version (nicer for most proofs) *)
val FUNPOW_OPT_LIST_def = Define `
 (FUNPOW_OPT_LIST f 0 s = SOME [s]) /\
 (FUNPOW_OPT_LIST f (SUC n) s =
  case FUNPOW_OPT_LIST f n s of
   | SOME res_prefix =>
    (case f (LAST res_prefix) of
     | SOME res_last => SOME (SNOC res_last res_prefix)
     | NONE => NONE)
   | NONE => NONE)`;

(* TODO: Split up in two theorems, one specific for FUNPOW_OPT equivalence? *)
val FUNPOW_OPT_LIST_EQ_SOME = prove(``
!f n s l.
FUNPOW_OPT_LIST f n s = SOME l <=>
LENGTH l = (SUC n) /\
FUNPOW_OPT f n s = SOME (LAST l) /\
(!n'. n' <= n ==> FUNPOW_OPT f n' s = SOME (EL n' l)) /\
!i. (SUC i) < LENGTH l ==>
f (EL i l) = SOME (EL (SUC i) l)
``,

cheat
);

val FUNPOW_OPT_LIST_EQ_NONE = prove(``
!f n s.
FUNPOW_OPT_LIST f n s = NONE <=>
?n'. n' <= n /\ FUNPOW_OPT f n' s = NONE /\
(* TODO: Overkill? *)
(!n''. n'' < n' ==> (FUNPOW_OPT f n'' s <> NONE))
``,

REPEAT STRIP_TAC >>
EQ_TAC >| [
 REPEAT STRIP_TAC >>
 (* Looks OK *)
 cheat,

 REPEAT STRIP_TAC >>
 (* Looks OK *)
 cheat
]
);

(*
(* Tail-recursive version (useful for a few proofs) *)
val FUNPOW_OPT_LIST_tailrec_def = Define `
 (FUNPOW_OPT_LIST_tailrec f 0 s = SOME [s]) /\
 (FUNPOW_OPT_LIST_tailrec f (SUC n) s =
  case f s of
  | SOME res_hd =>
   (case FUNPOW_OPT_LIST_tailrec f n res_hd of
    | SOME res_tl => SOME (res_hd::res_tl)
    | NONE => NONE)
  | NONE => NONE)`;

val FUNPOW_OPT_LIST_tailrec_EQ_SOME = prove(``
!f n s l.
FUNPOW_OPT_LIST_tailrec f n s = SOME l <=>
LENGTH l = (SUC n) /\
FUNPOW_OPT f n s = SOME (LAST l) /\
(!n'. n' <= n ==> FUNPOW_OPT f n' s = SOME (EL n' l)) /\
!i. (SUC i) < LENGTH l ==>
f (EL i l) = SOME (EL (SUC i) l)
``,

cheat
);

val FUNPOW_OPT_LIST_tailreq_equiv = prove(``
!f n s.
FUNPOW_OPT_LIST f n s = FUNPOW_OPT_LIST_tailrec f n s
``,

(* TODO: Break up into lemmata... *)
cheat

(*
Induct_on `n` >- (
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_LIST_tailrec_def]
) >>
fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_LIST_tailrec_def] >>
REPEAT STRIP_TAC >>
Cases_on `FUNPOW_OPT_LIST_tailrec f n s` >| [
 (* Case: result became NONE somewhere before last step *)
 cheat,

 (* Case: result is still SOME right before last step *)
 IMP_RES_TAC FUNPOW_OPT_LIST_tailrec_SOME >>
 fs [] >>
 (* f s could not have been NONE, since FUNPOW_OPT_LIST_tailrec f n s is SOME*)
 subgoal `?x. f s = SOME x` >- (
  cheat
 ) >>
 fs [] >>
) >>
Cases_on `FUNPOW_OPT_LIST_tailrec f n s` >> (
 fs []
) >>
Cases_on `f s` >> (
 fs []
) >>
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_LIST_tailrec_def]
) >>
cheat
*)
);
*)

(*
val FUNPOW_OPT_LISTS_def = Define `
 (FUNPOW_OPT_LISTS f [] s = SOME [s]) /\
 (FUNPOW_OPT_LISTS f (h::t) s =
  case FUNPOW_OPT_LISTS f t s of
   | SOME res_tl =>
    (case f (LAST res_tl) of
     | SOME res_hd => SOME (res_hd::res_tl)
     | NONE => NONE)
   | NONE => NONE)`;
*)

val FUNPOW_OPT_LIST_0 = prove(``
!f x.
FUNPOW_OPT_LIST f 0 x = SOME [x]
``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_LIST_def]
);

val FUNPOW_OPT_LIST_NONEMPTY = prove(``
!f n x l.
FUNPOW_OPT_LIST f n x = SOME l ==>
l <> []
``,

REPEAT STRIP_TAC >>
rw [] >>
Cases_on `n` >> (
 fs [FUNPOW_OPT_LIST_def]
) >>
Cases_on `FUNPOW_OPT_LIST f n' x` >> (
 fs []
) >>
Cases_on `f (LAST x')` >> (
 fs []
)
);

val FUNPOW_OPT_LIST_LAST = prove(``
!f n x l_opt.
FUNPOW_OPT_LIST f n x = l_opt ==>
(case l_opt of
 | SOME l =>
  FUNPOW_OPT f n x = SOME (LAST l)
 | NONE => FUNPOW_OPT f n x = NONE)
``,

REPEAT STRIP_TAC >>
Cases_on `l_opt` >| [
 (* TODO: Prove EQ_NONE theorem? *)
 fs [FUNPOW_OPT_LIST_EQ_NONE] >>
 subgoal `?n''. n = n' + n''` >- (
  Q.EXISTS_TAC `n - n'` >>
  fs []
 ) >>
 METIS_TAC [FUNPOW_OPT_next_n_NONE],

 (* Using EQ_SOME: *) 
 fs [FUNPOW_OPT_LIST_EQ_SOME]
(* OLD:
 Cases_on `n` >- (
  fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_def] >>
  rw []
 ) >>
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_def] >>
 Cases_on `FUNPOW_OPT_LIST f n' x` >> (
  fs []
 ) >>
 Cases_on `f (LAST x'')` >> (
  fs []
 ) >>
 fs [arithmeticTheory.FUNPOW] >>
 (* TODO: Tail-recursive vs. head-recursive definitions *)
 cheat
*)
]
);

val FUNPOW_OPT_LIST_CONS = prove(``
!f x n t.
FUNPOW_OPT_LIST f n x = SOME t ==>
((?h. f (LAST t) = SOME h /\
      FUNPOW_OPT_LIST f (SUC n) x = SOME (SNOC h t)) \/ FUNPOW_OPT_LIST f (SUC n) x = NONE)
``,

REPEAT STRIP_TAC >>
Cases_on `n` >> (
 fs [FUNPOW_OPT_LIST_def]
) >| [
 rw [] >>
 Cases_on `f x` >> (
  fs []
 ),

 Cases_on `FUNPOW_OPT_LIST f n' x` >> (
  fs []
 ) >>
 Cases_on `f (LAST x')` >> (
  fs []
 ) >>
 Cases_on `f (LAST t)` >> (
  fs []
 )
]
);

val FUNPOW_OPT_LIST_FRONT_PRE = prove(``
!f x n t.
FUNPOW_OPT_LIST f (SUC n) x = SOME t ==>
FUNPOW_OPT_LIST f n x = SOME (FRONT t)
``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_LIST_def]  >>
Cases_on `FUNPOW_OPT_LIST f n x` >> (
 fs []
) >>
Cases_on `f (LAST x')` >> (
 fs []
) >>
rw [listTheory.FRONT_DEF] >>
fs [rich_listTheory.FRONT_APPEND]
);

val FUNPOW_OPT_LIST_BACK_PRE = prove(``
!f x x' n l.
FUNPOW_OPT_LIST f (SUC n) x = SOME l ==>
f x = SOME x' ==>
FUNPOW_OPT_LIST f n x' = SOME (TL l)
``,

cheat
);

val FUNPOW_OPT_LIST_BACK_INCR = prove(``
!f x x' n t.
FUNPOW_OPT_LIST f n x' = SOME t ==>
f x = SOME x' ==>
FUNPOW_OPT_LIST f (SUC n) x = SOME (x::t)
``,

cheat
);

val FUNPOW_OPT_LIST_INCR2 = prove(``
!f x n h t.
FUNPOW_OPT_LIST f n x = SOME t ==>
LENGTH t = (SUC n) ==>
f (LAST t) = SOME h ==>
FUNPOW_OPT_LIST f (SUC n) x = SOME (SNOC h t) /\ LENGTH (SNOC h t) = (SUC (SUC n))
``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_LIST_def]
);

(*
val FUNPOW_OPT_LISTS_LENGTH = prove(``
!l' l f x.
FUNPOW_OPT_LISTS f l' x = SOME l ==>
LENGTH l = (SUC (LENGTH l'))
``,

cheat
);

val FUNPOW_OPT_LISTS_EQUIV = prove(``
!l' l f x.
FUNPOW_OPT_LISTS f l' x = SOME l <=>
FUNPOW_OPT_LIST f (LENGTH l') x = SOME l
``,

REPEAT STRIP_TAC >>
EQ_TAC >> (
 REPEAT STRIP_TAC
) >>
Induct_on `l` >> Induct_on `l'` >>
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_LISTS_def] >>

 Cases_on `FUNPOW_OPT_LISTS f l' x` >> (
  fs []
 ) >>
 Cases_on `FUNPOW_OPT_LIST f (LENGTH l') x` >> (
  fs []
 ) >>
 Cases_on `f (LAST x')` >> (
  fs []
 ) >>

 Cases_on `f (LAST x'')` >> (
  fs []
 ) >>
);
*)

val FUNPOW_OPT_LIST_LENGTH = prove(``
!n l f x.
FUNPOW_OPT_LIST f n x = SOME l ==>
LENGTH l = (SUC n)
``,

Induct_on `n` >- (
 fs [FUNPOW_OPT_LIST_def]
) >>
REPEAT STRIP_TAC >>
subgoal `FUNPOW_OPT_LIST f n x = SOME (FRONT l)` >- (
 METIS_TAC [FUNPOW_OPT_LIST_FRONT_PRE]
) >>
RES_TAC >>
IMP_RES_TAC FUNPOW_OPT_LIST_NONEMPTY >>
IMP_RES_TAC rich_listTheory.LENGTH_FRONT >>
fs []

(* Using FUNPOW_OPT_LISTS:
REPEAT STRIP_TAC >>
subgoal `?l'. n = LENGTH l'` >- (
 Q.EXISTS_TAC `REPLICATE n a` >>
 fs [rich_listTheory.LENGTH_REPLICATE]
) >>
fs [GSYM FUNPOW_OPT_LISTS_EQUIV] >>
METIS_TAC [FUNPOW_OPT_LISTS_LENGTH]
*)
);

val FUNPOW_OPT_step = prove(``
!f n x x' x''.
FUNPOW_OPT f (SUC n) x = SOME x'' ==>
f x = SOME x' ==>
FUNPOW_OPT f n x' = SOME x''
``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_REWRS]
);

val FUNPOW_OPT_INTER = store_thm ("FUNPOW_OPT_INTER",
  ``!f n n' ms ms' ms''.
    (FUNPOW_OPT f n ms = SOME ms') ==>
    (FUNPOW_OPT f (n'+n) ms = SOME ms'') ==>
    (FUNPOW_OPT f n' ms' = SOME ms'')
    ``,

METIS_TAC [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_OPT_SUBLIST = prove(``
!f n n' x l.
n' <= n ==>
FUNPOW_OPT_LIST f (SUC n) x = SOME l ==>
FUNPOW_OPT_LIST f (SUC n − n') (LAST (TAKE (SUC n') l)) = SOME (DROP n' l) ==>
FUNPOW_OPT_LIST f (n − n') (LAST (TAKE (SUC (SUC n')) l)) = SOME (DROP (SUC n') l)
``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_LIST_EQ_SOME] >>
REPEAT STRIP_TAC >| [
 (* OK: starting one step later but taking one step less leads to same end result *)
 irule FUNPOW_OPT_step >>
 Q.EXISTS_TAC `LAST (TAKE (SUC n') l)` >>
 fs [] >>
 STRIP_TAC >| [
  QSPECL_X_ASSUM ``!i. SUC i < LENGTH l ==> f (EL i l) = SOME (EL (SUC i) l)`` [`n'`] >>
  rfs [] >>
  (* OK modulo basic list operations *)
  cheat,

  subgoal `EL (SUC n - n') (DROP n' l) = EL (SUC (n - n')) (DROP n' l)` >- (
   fs [arithmeticTheory.SUB_LEFT_SUC] >>
   Cases_on `n = n'` >> (
    fs []
   )
  ) >>
  fs [listTheory.last_drop]
 ],

 (* OK: starting one step later, and then taking steps that won't let you reach the end of l
  * makes you reach the associated index of l *)
 irule FUNPOW_OPT_INTER >>
 Q.EXISTS_TAC `x` >>
 Q.EXISTS_TAC `n'` >>
 rfs [] >>
 STRIP_TAC >| [
  (* OK modulo basic list operations *)
  cheat,

  (* OK modulo basic list operations *)
  cheat
 ],

 (* OK: Property should hold for element i of sublist starting from element SUC n' *)
 QSPECL_X_ASSUM ``!i. SUC i < LENGTH l - n' ==>
                  f (EL i (DROP n' l)) = SOME (EL (SUC i) (DROP n' l))`` [`SUC i`] >>
 rfs [] >>
 subgoal `EL (SUC i) (DROP n' l) = EL i (DROP (SUC n') l)` >- (
  (* OK modulo basic list operations *)
  cheat
 ) >>
 subgoal `EL (SUC (SUC i)) (DROP n' l) = EL (SUC i) (DROP (SUC n') l)` >- (
  (* OK modulo basic list operations *)
  cheat
 ) >>
 fs []
]
);

val FUNPOW_OPT_LIST_APPEND = prove(``
!f n n' x l.
n' <= n ==>
FUNPOW_OPT_LIST f n x = SOME l ==>
?l' l''.
FUNPOW_OPT_LIST f n' x = SOME l' /\
FUNPOW_OPT_LIST f (n - n') (LAST l') = SOME l'' /\
l' ++ (DROP 1 l'') = l
``,

REPEAT STRIP_TAC >>
Q.EXISTS_TAC `TAKE (SUC n') l` >>
Q.EXISTS_TAC `DROP n' l` >>
REPEAT STRIP_TAC >| [
 Induct_on `n'` >- (
  STRIP_TAC >>
  Cases_on `n` >- (
   fs [FUNPOW_OPT_LIST_def] >>
   rw []
  ) >>
(* OLD:
  (* TODO: tail-recursive vs. head-recursive definitions *)
  cheat
*)
  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  (* OK modulo basic list operations *)
  cheat
 ) >>
 REPEAT STRIP_TAC >>
 Q.SUBGOAL_THEN `n' ≤ n` (fn thm => fs [thm]) >- (
  fs []
 ) >>
 fs [FUNPOW_OPT_LIST_def] >>
 Cases_on `f (LAST (TAKE (SUC n') l))` >- (
  fs [] >>
(* OLD:
  (* Cannot have been NONE, since result is SOME for greater number of steps *)
  cheat
*)
  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  QSPECL_X_ASSUM ``!n'.
          n' <= n ==>
          FUNPOW_OPT f n' x = SOME (EL n' l)`` [`n'`] >>
  rfs [] >>
  QSPECL_X_ASSUM ``!i. i < n ==> f (EL i l) = SOME (EL (SUC i) l)`` [`n'`] >>
  rfs [] >>
  Q.SUBGOAL_THEN `LAST (TAKE (SUC n') l) = EL n' l` (fn thm => fs [thm]) >- (
   fs []
  )
 ) >>
 fs [] >>
(* OLD:
 (* Requires to prove that x' is the result of transition n' + 1 *)
 cheat
*)
 fs [FUNPOW_OPT_LIST_EQ_SOME] >>
 subgoal `x' = EL (SUC n') l` >- (
  QSPECL_X_ASSUM ``!n'.
          n' <= n ==>
          FUNPOW_OPT f n' x = SOME (EL n' l)`` [`n'`] >>
  rfs [] >>
  QSPECL_X_ASSUM ``!i. i < n ==> f (EL i l) = SOME (EL (SUC i) l)`` [`n'`] >>
  rfs [] >>
  (* OK modulo basic list operations *)
  cheat
 ) >>
 (* OK modulo basic list operations *)
 cheat,

 (* Start off after n' steps, take n - n' steps *)
 Induct_on `n'` >- (
  STRIP_TAC >>
  fs [] >>
  Q.SUBGOAL_THEN `TAKE 1 l = [x]` (fn thm => fs [thm]) >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   Cases_on `n` >- (
    fs [FUNPOW_OPT_def] >>
    (* OK modulo basic list operations *)
    cheat
   ) >>
   QSPECL_X_ASSUM ``!n''. _`` [`0`] >>
   fs [FUNPOW_OPT_def] >>
   (* OK modulo basic list operations *)
   cheat
(* OLD:
   (* TODO: tail-recursive vs. head-recursive definitions *)
   cheat
*)
  )
 ) >>
 Cases_on `n` >- (
  fs []
 ) >>
 REPEAT STRIP_TAC >>
 Q.SUBGOAL_THEN `n' ≤ SUC n''` (fn thm => fs [thm]) >- (
  fs []
 ) >>
 (* If you take one more step, if you start one step earlier, then the result is the same as before
  * with one less step dropped (from head) *)
 irule FUNPOW_OPT_SUBLIST >>
 fs [] >>
 Q.EXISTS_TAC `x` >>
 fs [],

 fs [rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1]
]
);

val FUNPOW_OPT_LIST_EL_SOME = prove(``
!f n n' x l.
FUNPOW_OPT_LIST f n x = SOME l ==>
n' <= n ==>
?x'. FUNPOW_OPT f n' x = SOME x'
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC FUNPOW_OPT_LIST_APPEND >>
Q.EXISTS_TAC `LAST l'` >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs []
);

val FUNPOW_OPT_LIST_EL_NONE = prove(``
!f n n' x.
FUNPOW_OPT_LIST f n x = NONE ==>
(n' >= n) ==>
FUNPOW_OPT f n' x = NONE
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs [] >>
subgoal `?n''. n' = n + n''` >- (
 fs [arithmeticTheory.LESS_EQUAL_ADD]
) >>
METIS_TAC [FUNPOW_OPT_next_n_NONE]
);

(* TODO: Use FUNPOW_OPT_next_n_NONE instead of this *)
val FUNPOW_OPT_ADD_NONE = store_thm ("FUNPOW_OPT_ADD_NONE",
  ``!f n n' ms ms'.
    (FUNPOW_OPT f n ms = SOME ms') ==>
    (FUNPOW_OPT f n' ms' = NONE) ==> 
    (FUNPOW_OPT f (n'+n) ms = NONE)``,

METIS_TAC [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_OPT_LIST_EL_NEXT = prove(``
!f n x x'.
FUNPOW_OPT_LIST f n x = SOME x' ==>
FUNPOW_OPT f (SUC n) x = f (LAST x')
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs [] >>
Cases_on `f (LAST x')` >| [
 fs [arithmeticTheory.ADD1] >>
 ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
 irule FUNPOW_OPT_ADD_NONE >>
 Q.EXISTS_TAC `LAST x'` >>
 fs [FUNPOW_OPT_compute],

 fs [arithmeticTheory.ADD1] >>
 ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
 irule FUNPOW_OPT_ADD_thm >>
 Q.EXISTS_TAC `LAST x'` >>
 fs [FUNPOW_OPT_compute]
]
(* OLD: 
(* TODO: tail vs. head FUNPOW_OPT *)
cheat
*)
);

val FUNPOW_OPT_LIST_NONE = prove(``
!f n x.
FUNPOW_OPT_LIST f n x = NONE ==>
FUNPOW_OPT_LIST f (SUC n) x = NONE
``,

fs [FUNPOW_OPT_LIST_def]
);

val FUNPOW_OPT_LIST_EXISTS = prove(``
!f n n' x x'.
FUNPOW_OPT f n x = SOME x' ==>
n' <= n ==>
?l. FUNPOW_OPT_LIST f n' x = SOME l
``,

Induct_on `n` >- (
 REPEAT STRIP_TAC >>
 Q.EXISTS_TAC `[x']` >>
 fs [] >>
 rw [] >>
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_def]
) >>
REPEAT STRIP_TAC >>
Cases_on `n' = SUC n` >- (
 fs [FUNPOW_OPT_LIST_def] >>
 Cases_on `FUNPOW_OPT_LIST f n x` >- (
  fs [] >>
  IMP_RES_TAC FUNPOW_OPT_LIST_NONE >>
  subgoal `?x''. FUNPOW_OPT f n x = SOME x''` >- (
   irule FUNPOW_OPT_prev_EXISTS >>
   Q.EXISTS_TAC `SUC n` >>
   Q.EXISTS_TAC `x'` >>
   fs []
  ) >>
  IMP_RES_TAC (Q.SPECL [`f`, `n`, `SUC n`, `x`] FUNPOW_OPT_LIST_EL_NONE) >>
  fs []
 ) >>
 Cases_on `f (LAST x'')` >- (
  fs [] >>
  IMP_RES_TAC FUNPOW_OPT_LIST_EL_NEXT >>
  fs []
 ) >>
 fs []
) >>
subgoal `?x''. FUNPOW_OPT f n x = SOME x''` >- (
 irule FUNPOW_OPT_prev_EXISTS >>
 Q.EXISTS_TAC `SUC n` >>
 Q.EXISTS_TAC `x'` >>
 fs []
) >>
QSPECL_X_ASSUM ``!f n' x x'. _`` [`f`, `n'`, `x`, `x''`] >>
fs []
);

val FUNPOW_OPT_LIST_EL = prove(``
!f n n' x x' l.
FUNPOW_OPT_LIST f n x = SOME l ==>
n' <= n ==>
FUNPOW_OPT f n' x = SOME x' ==>
(EL n' l) = x'
``,

REPEAT STRIP_TAC >>
IMP_RES_TAC (Q.SPECL [`f`, `n`, `n'`, `x`, `l`] FUNPOW_OPT_LIST_APPEND) >>
subgoal `EL n' l = LAST l'` >- (
 rw [] >>
 IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
 Q.SUBGOAL_THEN `n' = PRE (LENGTH l')` (fn thm => REWRITE_TAC [thm]) >- (
  fs []
 ) >>
 Q.SUBGOAL_THEN `EL (PRE (LENGTH l')) (l' ++ DROP 1 l'') = EL (PRE (LENGTH l')) l'` (fn thm => REWRITE_TAC [thm]) >- (
  irule rich_listTheory.EL_APPEND1 >>
  fs []
 ) >>
 irule rich_listTheory.EL_PRE_LENGTH >>
 Cases_on `l'` >> (
  fs []
 )
) >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs []
);

val FUNPOW_OPT_LIST_INDEX_FIND = prove(``
!f P n x l i x'.
FUNPOW_OPT_LIST f n x = SOME l ==>
INDEX_FIND 0 P l = SOME (i, x') ==>
FUNPOW_OPT f i x = SOME x'
``,

REPEAT STRIP_TAC >>
fs [INDEX_FIND_EQ_SOME_0] >>
IMP_RES_TAC (Q.SPECL [`f`, `n`, `i`, `x`, `l`] FUNPOW_OPT_LIST_EL_SOME) >>
QSPECL_X_ASSUM ``!i. _`` [`i`] >>
IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
rfs [] >>
fs [] >>
rfs [] >>
IMP_RES_TAC (Q.SPECL [`f`, `n`, `x`, `l`] FUNPOW_OPT_LIST_EQ_SOME) >>
QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT f n' x = SOME (EL n' l)`` [`i`] >>
rfs []
);

val INDEX_FIND_MEM = prove(``
!P l x.
P x ==>
MEM x l ==>
?i x'. INDEX_FIND 0 P l = SOME (i, x')
``,

Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >| [
 Q.EXISTS_TAC `0` >>
 Q.EXISTS_TAC `h` >>
 fs [INDEX_FIND_EQ_SOME_0],

 Cases_on `P h` >| [
  Q.EXISTS_TAC `0` >>
  Q.EXISTS_TAC `h` >>
  fs [INDEX_FIND_EQ_SOME_0],

  RES_TAC >>
  Q.EXISTS_TAC `SUC i` >>
  Q.EXISTS_TAC `x'` >>
  fs [listTheory.INDEX_FIND_def] >>
  REWRITE_TAC [Once listTheory.INDEX_FIND_add] >>
  fs []
 ]
]
);

val MEM_HD = prove(``
!l.
MEM (HD l) l
``,

cheat
);

val FILTER_MEM = prove(``
!P l l' x.
FILTER P l = l' ==>
MEM x l' ==>
P x /\ MEM x l
``,

rw [] >>
fs [listTheory.MEM_FILTER]
);

(*
val FILTER_LAST = prove(``
!P l l' x.
LENGTH (FILTER P l) > 0 ==>
?i. EL (PRE (LENGTH (FILTER P l))) (FILTER P l) = EL i l
``,

cheat
);
*)

val MEM_EL_CONS = prove(``
!n e l.
n > 0 ==>
n < SUC (LENGTH l) ==>
MEM (EL n (e::l)) l
``,

cheat
);

val FILTER_NOT_MEM = prove(``
!P l l' x.
FILTER P l = l' ==>
MEM x l ==>
~MEM x l' ==>
~P x
``,

cheat
);

val FILTER_BEFORE = prove(``
!P l l' i.
FILTER P l = l' ==>
EL i l = HD l' ==>
(!i'. i' < i ==> ~P (EL i l) /\ ~MEM (EL i' l) l')
``,

cheat
);

val FILTER_AFTER = prove(``
!P l l' i.
FILTER P l = l' ==>
EL i l = LAST l' ==>
(!i'. i' > i ==> ~P (EL i' l) /\ ~MEM (EL i' l) l')
``,

cheat
);

val FILTER_ORDER = prove(``
!P l i i' i''.
EL i' l = EL i (FILTER P l) ==>
EL i'' l = EL (SUC i) (FILTER P l) ==>
i' < i''
``,

cheat
);

val FUNPOW_OPT_LIST_FIRST = prove(``
!f n x x' x_list.
n > 0 ==>
FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
f x = SOME x' ==>
FUNPOW_OPT_LIST f (PRE n) x' = SOME x_list
``,

cheat
);

(* If ms and ms' are not related by weak transition to ls for n transitions,
 * but if taking n transitions from ms takes you to ms' with a label in ls,
 * then there has to exist an ms'' and a *smallest* n' such that the label of
 * ms'' is in ls. *)
val weak_rel_steps_smallest_exists = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' n.
   ~(weak_rel_steps m ms ls ms' n) ==>
   n > 0 ==>
   FUNPOW_OPT m.trs n ms = SOME ms' ==>
   m.pc ms' IN ls ==>
   ?n' ms''.
    n' < n /\ n' > 0 /\
    FUNPOW_OPT m.trs n' ms = SOME ms'' /\
    m.pc ms'' IN ls /\
    (!n''.
     (n'' < n' /\ n'' > 0 ==>
      ?ms'''. FUNPOW_OPT m.trs n'' ms = SOME ms''' /\
      ~(m.pc ms''' IN ls)))
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list)` >- (
 IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS >>
 QSPECL_X_ASSUM ``!n'. n' <= n ==> ?l. FUNPOW_OPT_LIST m.trs n' ms = SOME l`` [`n`] >>
 fs [] >>
 Cases_on `n` >- (
  fs [FUNPOW_OPT_LIST_def]
 ) >>
 (* TODO: Should be OK... *)
 cheat
(* OLD
 irule FUNPOW_OPT_LIST_EXISTS >>
 Q.EXISTS_TAC `n` >>
 fs []
*)
) >>
subgoal `?i ms''. INDEX_FIND 0 (\ms. m.pc ms IN ls) ms_list = SOME (i, ms'')` >- (
 (* OK: There is at least ms', possibly some earlier encounter of ls *)
 irule INDEX_FIND_MEM >>
 Q.EXISTS_TAC `ms'` >>
 fs [listTheory.MEM_EL] >>
 Q.EXISTS_TAC `PRE n` >> (* Note: Indexing change *)
 CONJ_TAC >| [
  IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
  fs [] >>
  (* OK modulo some arithmetic *)
  cheat,

  REWRITE_TAC [Once EQ_SYM_EQ] >>
  irule FUNPOW_OPT_LIST_EL >>
  fs [] >>
  subgoal `?ms''. m.trs ms = SOME ms''` >- (
   (* TODO: Should be OK... *)
   cheat
  ) >>
  Q.EXISTS_TAC `m.trs` >>
  Q.EXISTS_TAC `PRE n` >>
  Q.EXISTS_TAC `ms''` >>
  fs [] >>
  CONJ_TAC >| [
   cheat,

   METIS_TAC [FUNPOW_OPT_LIST_FIRST]
  ]
 ]
) >>
Q.EXISTS_TAC `SUC i` >>
Q.EXISTS_TAC `ms''` >>
fs [] >>
subgoal `?ms'''. FUNPOW_OPT m.trs n' ms = SOME ms'''` >- (
 METIS_TAC [FUNPOW_OPT_prev_EXISTS]
) >>
REPEAT STRIP_TAC >| [
 (* i < n since i must be at least n', since INDEX_FIND at least must have found ms''',
  * if not any earlier encounter *)
 fs [INDEX_FIND_EQ_SOME_0] >>
 Cases_on `n' < (SUC i)` >| [
  (* Contradiction: ms''' occurs earlier than the first encounter of ls found by INDEX_FIND *)
  subgoal `m.pc (EL (PRE n') ms_list) NOTIN ls` >- ( (* Note: Indexing change *)
   fs []
  ) >>
  subgoal `(EL (PRE n') ms_list) = ms'''` >- ( (* Note: Indexing change *)
   subgoal `(EL n' (ms::ms_list)) = ms'''` >- (
    METIS_TAC [FUNPOW_OPT_LIST_EL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
   ) >>
   METIS_TAC [rich_listTheory.EL_CONS, arithmeticTheory.GREATER_DEF]
  ) >>
  fs [],

  fs []
 ],

 fs [INDEX_FIND_EQ_SOME_0, FUNPOW_OPT_LIST_EQ_SOME],

 fs [INDEX_FIND_EQ_SOME],

 subgoal `n'' < n` >- (
  fs [INDEX_FIND_EQ_SOME_0] >>
  IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
  fs []
 ) >>
 subgoal `?ms''''. FUNPOW_OPT m.trs n'' ms = SOME ms''''` >- (
  METIS_TAC [FUNPOW_OPT_LIST_EL_SOME, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
 ) >>
 subgoal `(EL (PRE n'') ms_list) = ms''''` >- (
  irule FUNPOW_OPT_LIST_EL >>
  subgoal `?ms'''''. m.trs ms = SOME ms'''''` >- (
   (* TODO: Should be OK... *)
   cheat
  ) >>
  Q.EXISTS_TAC `m.trs` >>
  Q.EXISTS_TAC `PRE n` >>
  Q.EXISTS_TAC `ms'''''` >>
  fs [] >>
  (* TODO: Should be OK... *)
  cheat
 ) >>
 fs [INDEX_FIND_EQ_SOME_0] >>
 rw []
]
);

val weak_rel_steps_intermediate_labels = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' n.
  weak_rel_steps m ms ls1 ms' n ==>
  ~(weak_rel_steps m ms (ls1 UNION ls2) ms' n) ==>
  ?ms'' n'. weak_rel_steps m ms ls2 ms'' n' /\ n' < n
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
rfs [] >>
subgoal `?n' ms''.
  n' < n /\ n' > 0 /\
  FUNPOW_OPT m.trs n' ms = SOME ms'' /\
  (m.pc ms'' IN (ls1 UNION ls2)) /\
  (!n''.
   (n'' < n' /\ n'' > 0 ==>
    ?ms'''. FUNPOW_OPT m.trs n'' ms = SOME ms''' /\
    ~(m.pc ms''' IN (ls1 UNION ls2))))` >- (
 irule weak_rel_steps_smallest_exists >>
 fs [weak_rel_steps_def] >>
 Q.EXISTS_TAC `n'` >>
 REPEAT STRIP_TAC >> (
  fs []
 )
) >>
Q.EXISTS_TAC `ms''` >>
Q.EXISTS_TAC `n''` >>
fs [] >| [
 QSPECL_X_ASSUM ``!(n':num). n' < n /\ n' > 0 ==> _`` [`n''`] >>
 rfs [],

 REPEAT STRIP_TAC >>
 QSPECL_X_ASSUM ``!(n'3':num). n'3' < n'' /\ n'3' > 0 ==> _`` [`n'3'`] >>
 rfs []
]
);

val weak_rel_steps_union = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms'' n n'.
  weak_rel_steps m ms ls1 ms' n ==>
  weak_rel_steps m ms ls2 ms'' n' ==>
  n' < n ==>
  weak_rel_steps m ms (ls1 UNION ls2) ms'' n'
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
QSPECL_X_ASSUM ``!n'. _`` [`n''`] >>
rfs [] >>
fs []
);

val weak_intermediate_labels = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms'.
  m.weak ms ls1 ms' ==>
  ~(m.weak ms (ls1 UNION ls2) ms') ==>
  ?ms''. (m.pc ms'') IN ls2 /\ m.weak ms (ls1 UNION ls2) ms''
  ``,

REPEAT STRIP_TAC >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
QSPECL_X_ASSUM ``!n. _`` [`n`] >>
IMP_RES_TAC weak_rel_steps_intermediate_labels >>
Q.EXISTS_TAC `ms''` >>
CONJ_TAC >| [
 METIS_TAC [weak_rel_steps_label],

 METIS_TAC [weak_rel_steps_union]
]
);

val FUNPOW_ASSOC = prove(``
!f m n x.
FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)``,

fs [GSYM arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_SUB = prove(``
!f m n x.
m > n ==>
FUNPOW f (m - n) (FUNPOW f n x) = FUNPOW f m x``,

fs [GSYM arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_OPT_split = prove(``
!f n n' s s' s''.
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n + n') s = SOME s'' ==>
FUNPOW_OPT f n' s' = SOME s''``,

METIS_TAC [FUNPOW_ASSOC, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_OPT_split2 = prove(``
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f n' s = SOME s'' ==>
FUNPOW_OPT f (n - n') s'' = SOME s'``,

REPEAT STRIP_TAC >>
METIS_TAC [FUNPOW_SUB, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
);

val FUNPOW_OPT_split3 = prove(``
!f n' n s s'' s'.
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n + n') s = SOME s'' ==>
FUNPOW_OPT f n' s' = SOME s''``,

cheat
);

val FUNPOW_OPT_todoname = prove(``
!f n n' n'' P ms ms_list.
FUNPOW_OPT_LIST f n ms = SOME (ms::ms_list) ==>
FUNPOW_OPT f n'' ms =
        SOME
          (EL (LENGTH (FILTER P ms_list) - 1)
             (FILTER P ms_list)) ==>
n' < n - n'' ==>
FUNPOW_OPT f (n' + n'') ms = SOME (EL (PRE (n' + n'')) ms_list)``,

REPEAT STRIP_TAC >>
fs [FUNPOW_OPT_LIST_EQ_SOME] >>
irule rich_listTheory.EL_CONS >>
fs [weak_rel_steps_def] >>
cheat
);

val weak_rel_steps_FILTER_inter = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' i i' i'' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' (LENGTH ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  EL i' ms_list = EL i (FILTER (\ms. m.pc ms = l) ms_list) ==>
  EL i'' ms_list = EL (i+1) (FILTER (\ms. m.pc ms = l) ms_list) ==>
  i < LENGTH ms_list' - 1 ==>
  FUNPOW_OPT_LIST m.trs (LENGTH ms_list) ms = SOME (ms::ms_list) ==>
  weak_rel_steps m (EL i ms_list') ({l} UNION ls) (EL (i + 1) ms_list') (i'' - i')
  ``,

cheat
);

val weak_rel_steps_FILTER_end = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' i i'' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' (LENGTH ms_list) ==>
  FUNPOW_OPT_LIST m.trs (LENGTH ms_list) ms = SOME (ms::ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  i < LENGTH ms_list' - 1 ==>
  EL i'' ms_list = EL (i+1) (FILTER (\ms. m.pc ms = l) ms_list) ==>
  weak_rel_steps m (EL (i + 1) ms_list') ls ms' (LENGTH ms_list - SUC i'')
  ``,

cheat
);

val weak_rel_steps_FILTER_NOTIN_end = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' n n' l ms_list ms_list'.
  weak_rel_steps m ms ls ms' n ==>
  l NOTIN ls ==>
  FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list) ==>
  FILTER (\ms. m.pc ms = l) ms_list = ms_list' ==>
  EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list) = EL n' ms_list ==>
  SUC n' < n
  ``,

cheat
);

val weak_rel_steps_unique = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' ms'' n n'.
  weak_rel_steps m ms ls ms' n ==>
  weak_rel_steps m ms ls ms'' n' ==>
  (ms' = ms'' /\ n = n')
  ``,

REPEAT STRIP_TAC >| [
 METIS_TAC [weak_rel_steps_imp, weak_unique_thm],

 fs [weak_rel_steps_def] >>
 CCONTR_TAC >>
 Cases_on `n < n'` >- (
  QSPECL_X_ASSUM ``!n''. _`` [`n`] >>
  rfs []
 ) >>
 QSPECL_X_ASSUM ``!n'.
                  n' < n /\ n' > 0 ==>
                  ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls`` [`n'`] >>
 rfs []
]
);

val weak_rel_steps_intermediate_start = prove(``
  !m.
  weak_model m ==>
  !ms ls ms' ms'' n n'.
  n' < n ==>
  weak_rel_steps m ms ls ms' n ==>
  FUNPOW_OPT m.trs n' ms = SOME ms'' ==>
  weak_rel_steps m ms'' ls ms' (n - n')
  ``,

cheat
);

val weak_rel_steps_superset_after = prove(``
  !m.
  weak_model m ==>
  !ms ls ls' ms' ms'' n n'.
  n' < n ==>
  weak_rel_steps m ms ls ms' n ==>
  weak_rel_steps m ms'' ls ms' (n - n') ==>
  (!n''. n'' < (n-n') ==> n'' > 0 ==> (?ms'''. FUNPOW_OPT m.trs n'' ms'' = SOME ms''' /\ m.pc ms''' NOTIN ls')) ==>
  weak_rel_steps m ms'' (ls' UNION ls) ms' (n - n')
  ``,

cheat
);

val weak_rel_steps_intermediate_labels2 = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms'' n n'.
  weak_rel_steps m ms ls2 ms' n ==>
  ~(weak_rel_steps m ms (ls1 UNION ls2) ms' n) ==>
  weak_rel_steps m ms (ls1 UNION ls2) ms'' n' ==>
  ?n''. weak_rel_steps m ms'' ls2 ms' n'' /\ n'' < n
  ``,

REPEAT STRIP_TAC >>
subgoal `weak_rel_steps m ms (ls1 UNION ls2) ms'' n' /\ n' < n` >- (
 subgoal `?ms'' n'. weak_rel_steps m ms (ls1 UNION ls2) ms'' n' /\ n' < n` >- (
  METIS_TAC [weak_rel_steps_intermediate_labels, weak_rel_steps_union, pred_setTheory.UNION_COMM]
 ) >>
 METIS_TAC [weak_rel_steps_unique]
) >>
fs [] >>
fs [weak_rel_steps_def] >>
rfs [] >> (
 Q.EXISTS_TAC `n - n'` >>
 subgoal `FUNPOW_OPT m.trs (n - n') ms'' = SOME ms'` >- (
  METIS_TAC [FUNPOW_OPT_split2, arithmeticTheory.GREATER_DEF]
 ) >>
 fs [] >>
 REPEAT STRIP_TAC >>
 QSPECL_X_ASSUM ``!n'.
           n' < n /\ n' > 0 ==>
           ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls2`` [`n' + n'3'`] >>
 subgoal `n' + n'3' < n` >- (
  fs []
 ) >>
 subgoal `n' + n'3' > 0` >- (
  fs []
 ) >>
 fs [] >>
 Q.EXISTS_TAC `ms'3'` >>
 fs [] >>
 METIS_TAC [FUNPOW_OPT_split]
)
);

val weak_rel_steps_intermediate_labels3 = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms'' n n'.
  weak_rel_steps m ms ls1 ms' n ==>
  weak_rel_steps m ms (ls2 UNION ls1) ms'' n' ==>
  n' < n ==>
  m.pc ms'' IN ls2
  ``,

REPEAT STRIP_TAC >>
fs [weak_rel_steps_def] >>
QSPECL_X_ASSUM ``!n'.
                 n' < n /\ n' > 0 ==>
                 ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls1`` [`n'`] >>
rfs []
);

val weak_intermediate_labels2 = prove(``
  !m.
  weak_model m ==>
  !ms ls1 ls2 ms' ms''.
  m.weak ms ls2 ms' ==>
  ~(m.weak ms (ls1 UNION ls2) ms') ==>
  m.weak ms (ls1 UNION ls2) ms'' ==>
  m.weak ms'' ls2 ms'
  ``,

REPEAT STRIP_TAC >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
METIS_TAC [weak_rel_steps_intermediate_labels2]
);

(* Definition of the triple *)
(* Pre and post usually have conditions on execution mode and code in memory *)
(* also post is usually a map that depends on the end state address *)
val abstract_partial_jgmt_def = Define `
  abstract_partial_jgmt m (l:'a) (ls:'a->bool) pre post =
  !ms ms'.
   ((m.pc ms) = l) ==>
   pre ms ==>
   m.weak ms ls ms' ==>
   post ms'
`;

val abstract_jgmt_imp_partial_triple =
  store_thm("abstract_jgmt_imp_partial_triple",
  ``!m l ls pre post.
    weak_model m ==>
    abstract_jgmt m l ls pre post ==>
    abstract_partial_jgmt m l ls pre post``,

FULL_SIMP_TAC std_ss [abstract_jgmt_def, abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms. _`` [`ms`] >>
METIS_TAC [weak_unique_thm]
);

val weak_partial_case_rule_thm = prove(``
!m l ls pre post C1.
  abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (C1 ms)) post ==>
  abstract_partial_jgmt m l ls (\ms. (pre ms) /\ (~(C1 ms))) post ==>
  abstract_partial_jgmt m l ls pre post
``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
METIS_TAC []
);

val weak_partial_weakening_rule_thm =
  store_thm("weak_partial_weakening_rule_thm",
  ``!m. 
    !l ls pre1 pre2 post1 post2.
    weak_model m ==>
    (!ms. ((m.pc ms) = l) ==> (pre2 ms) ==> (pre1 ms)) ==>
    (!ms. ((m.pc ms) IN ls) ==> (post1 ms) ==> (post2 ms)) ==>
    abstract_partial_jgmt m l ls pre1 post1 ==>
    abstract_partial_jgmt m l ls pre2 post2
  ``,

SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_pc_in_thm]
);

val weak_partial_subset_rule_thm =
 store_thm("weak_partial_subset_rule_thm",
  ``!m.  ! l ls1 ls2 pre post .
    weak_model m ==>
    (!ms. post ms ==> (~(m.pc ms IN ls2))) ==>
    abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
    abstract_partial_jgmt m l ls1 pre post``,

REPEAT STRIP_TAC >>
rfs [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_ASSUM ``!ms ms'. _`` [`ms`, `ms'`] >>
rfs [] >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
 fs []
) >>
subgoal `?n. FUNPOW_OPT m.trs n ms = SOME ms'` >- (
 METIS_TAC [weak_model_def]
) >>
IMP_RES_TAC weak_intermediate_labels >>
QSPECL_X_ASSUM ``!ms ms'. _`` [`ms`, `ms''`] >>
rfs [] >>
METIS_TAC []
);


val weak_partial_conj_rule_thm = prove(``
  !m.
  weak_model m ==>
  !l ls pre post1 post2.
  abstract_partial_jgmt m l ls pre post1 ==>
  abstract_partial_jgmt m l ls pre post2 ==>
  abstract_partial_jgmt m l ls pre (\ms. (post1 ms) /\ (post2 ms))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [weak_unique_thm]
);


val weak_partial_seq_rule_thm = store_thm("weak_partial_seq_rule_thm",
  ``!m l ls1 ls2 pre post.
    weak_model m ==>
    abstract_partial_jgmt m l (ls1 UNION ls2) pre post ==>
    (!l1. (l1 IN ls1) ==>
    (abstract_partial_jgmt m l1 ls2 post post)) ==>
    abstract_partial_jgmt m l ls2 pre post``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [abstract_partial_jgmt_def] >>
REPEAT STRIP_TAC >>
QSPECL_X_ASSUM ``!ms ms'.
		 (m.pc ms = l) ==>
		 pre ms ==>
		 m.weak ms (ls1 UNION ls2) ms' ==>
		 post ms'`` [`ms`] >>
rfs [] >>
subgoal `(m.pc ms') IN ls2` >- (
  METIS_TAC [weak_pc_in_thm]
) >>
Cases_on `m.weak ms (ls1 UNION ls2) ms'` >- (
  METIS_TAC []
) >>
subgoal `?ms''. m.pc ms'' IN ls1 /\ m.weak ms (ls2 UNION ls1) ms''` >- (
  METIS_TAC [weak_intermediate_labels, pred_setTheory.UNION_COMM]
) >>
QSPECL_X_ASSUM  ``!l1. l1 IN ls1 ==> _`` [`m.pc ms''`] >>
rfs [] >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms''`, `ms'`] >>
rfs [] >>
subgoal `post ms''` >- (
  METIS_TAC [pred_setTheory.UNION_COMM]
) >>
METIS_TAC [pred_setTheory.UNION_COMM, weak_intermediate_labels2]
);

(* This describes the necessary characteristics of the list ms_list, which consists of
 * all states where l is encountered between ms and ms'. *)
val weak_rel_steps_list_states = prove(``
!m ms l ls ms' n.
 weak_model m ==>
 weak_rel_steps m ms ls ms' n ==>
 l NOTIN ls ==>
 ?ms_list.
  (!i. i < LENGTH ms_list ==> m.pc (EL i ms_list) = l) /\
  (LENGTH ms_list = 0 ==> weak_rel_steps m ms ({l} UNION ls) ms' n) /\
  (LENGTH ms_list > 0 ==>
   (?n'. weak_rel_steps m ms ({l} UNION ls) (HD ms_list) n' /\
         weak_rel_steps m (HD ms_list) ls ms' (n - n') /\ n' < n /\ n' > 0) /\
   (?n''. weak_rel_steps m (EL ((LENGTH ms_list) - 1) ms_list) ({l} UNION ls) ms' n'' /\ n'' > 0) /\
    !i. (i < ((LENGTH ms_list) - 1) ==> ?n' n''.
         weak_rel_steps m (EL i ms_list) ({l} UNION ls) (EL (i+1) ms_list) n' /\
         weak_rel_steps m (EL (i+1) ms_list) ls ms' n'' /\ n' < n /\ n' > 0 /\ n'' < n /\ n'' > 0))
``,

REPEAT STRIP_TAC >>
subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME (ms::ms_list)` >- (
 fs [weak_rel_steps_def] >>
 IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS >>
 QSPECL_X_ASSUM ``!n'. n' <= n ==> ?l. FUNPOW_OPT_LIST m.trs n' ms = SOME l`` [`n`] >>
 fs [] >>
 Cases_on `n` >- (
  fs [FUNPOW_OPT_LIST_def]
 ) >>
 subgoal `?ms''. m.trs ms = SOME ms''` >- (
  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  QSPECL_X_ASSUM ``!n''. n'' <= SUC n' ==> FUNPOW_OPT m.trs n'' ms = SOME (EL n'' l')`` [`1`] >>
  fs [FUNPOW_OPT_compute] >>
  Cases_on `m.trs ms` >> (
   fs []
  )
 ) >>
 subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n' ms'' = SOME ms_list` >- (
  METIS_TAC [FUNPOW_OPT_LIST_BACK_PRE]
 ) >>
 Q.EXISTS_TAC `ms_list` >>
 (* TODO: Should be OK...
  * (see also first subgoal in weak_rel_steps_smallest_exists, reuse this?) *)
 IMP_RES_TAC FUNPOW_OPT_LIST_BACK_INCR >>
 fs []
(* OLD
 irule FUNPOW_OPT_LIST_EXISTS >>
 Q.EXISTS_TAC `n` >>
 fs []
*)
) >>
(*
REPEAT STRIP_TAC >>
subgoal `?ms_list. FUNPOW_OPT_LIST m.trs n ms = SOME ms_list` >- (
 (* OK: Contradicts weak_rel_steps m ms ls ms' n otherwise *)
 fs [weak_rel_steps_def] >>
 irule FUNPOW_OPT_LIST_EXISTS >>
 fs [] >>
 Q.EXISTS_TAC `n` >>
 fs []
) >>
*)
Q.EXISTS_TAC `FILTER (\ms. m.pc ms = l) ms_list` >>
REPEAT STRIP_TAC >| [
 (* subgoal 1. OK: Element in filtered list obeys filter property *)
 subgoal `(\ms. m.pc ms = l) (EL i (FILTER (\ms. m.pc ms = l) ms_list))` >- (
  (* TODO: Silly, but it works... *)
  `(\ms. m.pc ms = l) (EL i (FILTER (\ms. m.pc ms = l) ms_list)) /\ MEM (EL i (FILTER (\ms. m.pc ms = l) ms_list)) ms_list` suffices_by (
   fs []
  ) >>
  irule FILTER_MEM >>
  Q.EXISTS_TAC `FILTER (\ms. m.pc ms = l) ms_list` >>
  METIS_TAC [listTheory.MEM_EL]
 ) >>
 fs [],

 (* subgoal 2. OK: If filtered list is empty, l can be inserted in ending label set *)
 fs [weak_rel_steps_def] >>
 REPEAT STRIP_TAC >>
 subgoal `?ms''. FUNPOW_OPT m.trs n' ms = SOME ms''` >- (
  METIS_TAC [FUNPOW_OPT_LIST_EL_SOME]
 ) >>
 fs [listTheory.FILTER_EQ_NIL] >>
 subgoal `EL (PRE n') ms_list = ms''` >- (
  subgoal `(EL n' (ms::ms_list)) = ms''` >- (
   METIS_TAC [FUNPOW_OPT_LIST_EL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
  ) >>
  METIS_TAC [rich_listTheory.EL_CONS, arithmeticTheory.GREATER_DEF]
 ) >>
 fs [listTheory.EVERY_EL] >>
 QSPECL_X_ASSUM ``!n. _`` [`PRE n'`] >>
 QSPECL_X_ASSUM ``!n'. _`` [`n'`] >>
 fs [] >>
 IMP_RES_TAC FUNPOW_OPT_LIST_LENGTH >>
 rfs [],

 (* subgoal 3. OK: First encounter of l is reached when filtered list is non-empty,
  * also weak transition can proceed from there directly to ending label set *)
 subgoal `?ms''. ms'' = EL 0 (FILTER (\ms. m.pc ms = l) ms_list)` >- (
  METIS_TAC []
 ) >>
 (* TODO: The below is used in multiple subgoals... *)
 subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
  fs []
 ) >>
 (* Note: last state in ms_list can't be at label l *)
 subgoal `?i. ms'' = EL i ms_list /\ i < (PRE n)` >- (
  subgoal `?i. SOME ms'' = oEL i ms_list` >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   IMP_RES_TAC FILTER_MEM >>
   QSPECL_X_ASSUM ``!x. MEM x ms_list' ==> MEM x ms_list`` [`ms''`] >>
   rfs [MEM_HD] >>
   fs [listTheory.MEM_EL] >>
   Q.EXISTS_TAC `n'` >>
   fs [listTheory.oEL_THM]
  ) >>
  Q.EXISTS_TAC `i` >>
  fs [listTheory.oEL_EQ_EL, FUNPOW_OPT_LIST_EQ_SOME] >>
  Cases_on `i = PRE n` >- (
   subgoal `m.pc ms'' = l` >- (
    IMP_RES_TAC FILTER_MEM >>
    QSPECL_X_ASSUM ``!x. MEM x ms_list' ==> (\ms. m.pc ms = l) x`` [`ms''`] >>
    rfs [MEM_HD]
   ) >>
   fs [weak_rel_steps_def] >>
   subgoal `ms'' = ms'` >- (
    `LAST (ms::ms_list) = EL (PRE n) ms_list` suffices_by (
     fs []
    ) >>
    subgoal `LAST (ms::ms_list) = EL (PRE (LENGTH (ms::ms_list))) (ms::ms_list)` >- (
     irule listTheory.LAST_EL >>
     fs []
    ) >>
    subgoal `PRE (LENGTH (ms::ms_list)) = n` >- (
     SIMP_TAC list_ss [] >>
     METIS_TAC []
    ) >>
    fs [rich_listTheory.EL_CONS, listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
   ) >>
   fs []
  ) >>
  fs []
 ) >>
 Q.EXISTS_TAC `SUC i` >>
 fs [] >>
 REPEAT STRIP_TAC >| [
  (* subgoal 3a. OK: SUC i steps taken until first encounter of l
   * EL i ms_list = HD ms_list' is among assumptions *)
  fs [weak_rel_steps_def] >>
  REPEAT STRIP_TAC >| [
   (* HD ms_list' reached in SUC i steps from ms *)
   fs [FUNPOW_OPT_LIST_EQ_SOME],

   (* HD ms_list' is either l or in ls *)
   IMP_RES_TAC FILTER_MEM >>
   QSPECL_X_ASSUM ``!x. MEM x ms_list' ==> (\ms. m.pc ms = l) x`` [`HD ms_list'`] >>
   rfs [MEM_HD],

   (* At n' < SUC i steps, we are neither at l nor in ls *)
   QSPECL_X_ASSUM ``!n'.
          n' < n /\ n' > 0 ==>
          ?ms''. FUNPOW_OPT m.trs n' ms = SOME ms'' /\ m.pc ms'' NOTIN ls`` [`n'`] >>
   rfs [] >>
   ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
   `~(\ms. m.pc ms = l) ms'3'` suffices_by (
    fs []
   ) >>
   irule FILTER_NOT_MEM >>
   Q.EXISTS_TAC `ms_list` >>
   Q.EXISTS_TAC `ms_list'` >>
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   (* OK: ms'3' is in ms_list (since n' < n) but not in ms_list' (since n' < SUC i, so before first encounter) *)
   CONJ_TAC >| [
    IMP_RES_TAC FILTER_BEFORE >>
    QSPECL_X_ASSUM ``!i'. i' < i ==> ~MEM (EL i' ms_list) ms_list'`` [`PRE n'`] >>
    rfs [] >>
    `EL (PRE n') ms_list = ms'3'` suffices_by (
     METIS_TAC []
    ) >>
    METIS_TAC [rich_listTheory.EL_CONS, arithmeticTheory.GREATER_DEF],

    QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' (ms::ms_list))`` [`n'`] >>
    rfs [] >>
    irule MEM_EL_CONS >>
    fs []
   ]
  ],

  (* subgoal 3b. OK: (n - SUC i) steps taken from first encounter of l will get you to ms' *)
  irule weak_rel_steps_intermediate_start >>
  fs [] >>
  Q.EXISTS_TAC `ms` >>
  fs [FUNPOW_OPT_LIST_EQ_SOME]
 ],

 (* subgoal 4. OK: Last element in filtered list can perform weak transition with ending
  * label set ({l} UNION ls) and reach ms' *)
 subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
  fs []
 ) >>
 subgoal `MEM (EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list)) ms_list` >- (
  subgoal `MEM (EL (PRE (LENGTH (FILTER (\ms. m.pc ms = l) ms_list))) (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [listTheory.MEM_EL] >>
   Q.EXISTS_TAC `PRE (LENGTH ms_list')` >>
   fs []
  ) >>
  METIS_TAC [FILTER_MEM]
 ) >>
 (* Note : this introduces n'3', the number of transitions to last encounter of l. *)
 subgoal `?n'''. FUNPOW_OPT m.trs n''' ms = SOME (EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1) (FILTER (\ms. m.pc ms = l) ms_list)) /\ n''' < n /\ n''' > 0` >- (
  fs [listTheory.MEM_EL] >>
  Q.EXISTS_TAC `SUC n'` >>
  REPEAT CONJ_TAC >| [
   fs [FUNPOW_OPT_LIST_EQ_SOME, arithmeticTheory.PRE_SUB1] >>
   rw [],
   
   (* TODO: Last element of ms_list' not being in l contradiction *)
   METIS_TAC [weak_rel_steps_FILTER_NOTIN_end],

   fs []
  ]
 ) >>
 IMP_RES_TAC weak_rel_steps_intermediate_start >>
 Q.EXISTS_TAC `n - n'3'` >>
 fs [] >>
 irule weak_rel_steps_superset_after >>
 REPEAT STRIP_TAC >> (
  fs []
 ) >| [
  (* Find appropriate index in ms_list and use it, also lemma that indices after FILTER LAST do
   * not have label l *)
  Q.EXISTS_TAC `EL (PRE (n'' + n'3')) ms_list` >>
  CONJ_TAC >| [
   (* TODO: Lemma for this situation *)
   irule FUNPOW_OPT_split3 >>
   Q.EXISTS_TAC `n'3'` >>
   Q.EXISTS_TAC `ms` >>
   fs [] >>
   METIS_TAC [FUNPOW_OPT_todoname],

(*
   subgoal `n'3' < n` >- (
    fs []
   ) >>
*)
   subgoal `EL (PRE n'3') ms_list = LAST ms_list'` >- (
    subgoal `FUNPOW_OPT m.trs n'3' ms = SOME (EL (PRE n'3') ms_list)` >- (
     fs [FUNPOW_OPT_LIST_EQ_SOME] >>
     QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT m.trs n' ms = SOME (EL n' (ms::ms_list))`` [`n'3'`] >>
     rfs [rich_listTheory.EL_CONS]
    ) >>
    subgoal `EL (PRE n'3') ms_list = EL (LENGTH (FILTER (\ms. m.pc ms = l) ms_list) - 1)
             (FILTER (\ms. m.pc ms = l) ms_list)` >- (
     fs []
    ) >>
    fs [] >>
    ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
    ONCE_REWRITE_TAC [GSYM arithmeticTheory.PRE_SUB1] >>
    irule listTheory.LAST_EL >>
    fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
   ) >>
   IMP_RES_TAC FILTER_AFTER >>
   QSPECL_X_ASSUM ``!i'. i' > PRE n'3' ==> ~(\ms. m.pc ms = l) (EL i' ms_list)`` [`(PRE (n'' + n'3'))`] >>
   `PRE (n'' + n'3') > PRE n'3'` suffices_by (
    fs []
   ) >>
   Cases_on `n''` >- (
    fs []
   ) >>
   Cases_on `n'3'` >> (
    fs []
   )
  ],

  METIS_TAC [],

  METIS_TAC []
 ],

 (* subgoal 5. Inductive case for weak transition with ending label set ({l} UNION ls)
  * between elements of the list (where the latter point goes to ms' with ending label set ls).
  * Should also be OK *)
 subgoal `?ms_list'. FILTER (\ms. m.pc ms = l) ms_list = ms_list'` >- (
  fs []
 ) >>
 subgoal `?i'. EL i' ms_list = EL i (FILTER (\ms. m.pc ms = l) ms_list) /\ i' < LENGTH ms_list` >- (
  subgoal `MEM (EL i (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [rich_listTheory.EL_MEM]
  ) >>
  fs [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  Q.EXISTS_TAC `n'` >>
  rw []
 ) >>
 subgoal `?i'. EL i' ms_list = EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list) /\ i' < LENGTH ms_list` >- (
  subgoal `MEM (EL (i + 1) (FILTER (\ms. m.pc ms = l) ms_list)) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
   fs [rich_listTheory.EL_MEM]
  ) >>
  fs [listTheory.MEM_FILTER, listTheory.MEM_EL] >>
  Q.EXISTS_TAC `n'` >>
  rw []
 ) >>
 subgoal `i' < i''` >- (
  irule FILTER_ORDER >>
  Q.EXISTS_TAC `(\ms. m.pc ms = l)` >>
  Q.EXISTS_TAC `i` >>
  Q.EXISTS_TAC `ms_list` >>
  fs [arithmeticTheory.ADD1]
 ) >>
 subgoal `n = LENGTH ms_list` >- (
  fs [FUNPOW_OPT_LIST_EQ_SOME]
 ) >>
 Q.EXISTS_TAC `SUC i'' - SUC i'` >>
 Q.EXISTS_TAC `n - (SUC i'')` >>
 fs [] >>
 REPEAT STRIP_TAC >| [
  (* Weak transtion to ({l} UNION ls) between element i and element i+1 in ms_list' *)
  METIS_TAC [weak_rel_steps_FILTER_inter],

  (* Weak transtion to ls between element i+1 and LAST of ms_list' *)
  METIS_TAC [weak_rel_steps_FILTER_end],

  (* Phrased differently: "Why can't a member of ms_list' be the last element in ms_list?" *)
  (* TODO: Last element of ms_list' not being in l contradiction *)
  Cases_on `SUC i'' = LENGTH ms_list` >- (
   fs [weak_rel_steps_def] >>
   subgoal `m.pc (EL i'' ms_list) = l` >- (
    subgoal `MEM (EL i'' ms_list) (FILTER (\ms. m.pc ms = l) ms_list)` >- (
     fs [listTheory.MEM_EL] >>
     Q.EXISTS_TAC `i + 1` >>
     fs []
    ) >>
    fs [listTheory.MEM_FILTER]
   ) >>

   subgoal `ms' = EL i'' ms_list` >- (
    fs [FUNPOW_OPT_LIST_EQ_SOME, listTheory.LAST_EL] >>
    METIS_TAC [listTheory.EL_restricted]
   ) >>
   METIS_TAC []
  ) >>
  fs []
 ]
]
);

val weak_partial_loop_contract_def = Define `
  weak_partial_loop_contract m l le invariant C1 =
    (l NOTIN le /\
     abstract_partial_jgmt m l ({l} UNION le) (\ms. invariant ms /\ C1 ms)
       (\ms. m.pc ms = l /\ invariant ms))
`;
(* TODO: Preliminaries for proving partial loop rule *)
val weak_partial_loop_rule_thm = store_thm("weak_partial_loop_rule_thm",
  ``!m.
    weak_model m ==>
    !l le invariant C1 var post.
    weak_partial_loop_contract m l le invariant C1 ==>
    abstract_partial_jgmt m l le (\ms. invariant ms /\ ~(C1 ms)) post ==>
    abstract_partial_jgmt m l le invariant post``,

REPEAT STRIP_TAC >>
fs [abstract_partial_jgmt_def, weak_partial_loop_contract_def] >>
REPEAT STRIP_TAC >>
PAT_ASSUM ``weak_model m`` (fn thm => fs [HO_MATCH_MP weak_rel_steps_equiv thm]) >>
IMP_RES_TAC weak_rel_steps_list_states >>
(* QSPECL_X_ASSUM  ``!l. ?ms_list. _`` [`l`] >> *)
fs [] >>
Cases_on `ms_list = []` >- (
 fs [] >>
 QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms`, `ms'`] >>
 QSPECL_X_ASSUM  ``!ms ms'. _`` [`ms`, `ms'`] >>
 rfs [] >>
 Cases_on `C1 ms` >| [
  METIS_TAC [weak_pc_in_thm, weak_rel_steps_imp],

  METIS_TAC []
 ]
) >>
subgoal `LENGTH ms_list > 0` >- (
 fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
) >>
fs [] >>
Cases_on `~C1 ms` >- (
 METIS_TAC []
) >>
fs [] >>
subgoal `m.pc ms' <> l` >- (
  METIS_TAC [weak_pc_in_thm, weak_rel_steps_imp]
) >>
subgoal `!i. i < LENGTH ms_list ==> 
             (invariant (EL i ms_list) \/ post ms') /\
             (C1 (EL i ms_list) \/ (~C1 (EL i ms_list) /\ post ms'))` >- (
 Induct_on `i` >- (
  fs [] >>
  QSPECL_X_ASSUM  ``!i. _`` [`0`] >>
  subgoal `invariant (EL 0 ms_list)` >- (
   fs [] >>
   METIS_TAC [weak_rel_steps_intermediate_labels3, pred_setTheory.IN_SING]
  ) >>
  fs [] >>
  Cases_on `C1 (HD ms_list)` >> (
   fs []
  ) >>
  PAT_X_ASSUM  ``!ms ms'. _`` (fn thm => irule thm) >>
  Q.EXISTS_TAC `HD ms_list` >>
  fs [] >>
  METIS_TAC []
 ) >>
 REPEAT STRIP_TAC >> (
  fs []
 ) >| [
  QSPECL_X_ASSUM  ``!ms'' ms'3'.
          m.pc ms'' = l ==>
          invariant ms'' /\ C1 ms'' ==>
          (?n. weak_rel_steps m ms'' ({l} UNION le) ms'3' n) ==>
          m.pc ms'3' = l /\ invariant ms'3'`` [`EL i ms_list`, `EL (SUC i) ms_list`] >>
  QSPECL_X_ASSUM  ``!i. i < LENGTH ms_list ==> m.pc (EL i ms_list) = l`` [`i`] >>
  fs [] >>
  rfs [] >>
  QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
  rfs [] >>
  `?n. weak_rel_steps m (EL i ms_list) ({l} UNION le) (EL (SUC i) ms_list) n` suffices_by (
   fs []
  ) >>
  Q.EXISTS_TAC `n'3'` >>
  fs [arithmeticTheory.SUC_ONE_ADD],

  Cases_on `C1 (EL (SUC i) ms_list)` >> (
   fs []
  ) >>
  subgoal `invariant (EL (SUC i) ms_list)` >- (
   QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
   QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
   rfs [arithmeticTheory.SUC_ONE_ADD] >>
   METIS_TAC []
  ) >>
  PAT_X_ASSUM  ``!ms ms'. _`` (fn thm => irule thm) >>
  QSPECL_X_ASSUM  ``!i. _`` [`i`] >>
  Cases_on `SUC i = LENGTH ms_list - 1` >- (
   (* SUC i is last in ms_list *)
   QSPECL_X_ASSUM  ``!i. _`` [`SUC i`] >>
   Q.EXISTS_TAC `EL (SUC i) ms_list` >>
   fs [] >>
   rfs [] >>
   PAT_ASSUM ``weak_model m`` (fn thm => fs [GSYM (HO_MATCH_MP weak_rel_steps_equiv thm)]) >>
   METIS_TAC [weak_union_thm, pred_setTheory.IN_SING, weak_rel_steps_equiv]
  ) >>
  subgoal `SUC i < LENGTH ms_list - 1` >- (
   fs []
  ) >>
  fs [] >>
  Q.EXISTS_TAC `EL (SUC i) ms_list` >>
  fs [arithmeticTheory.SUC_ONE_ADD] >>
  METIS_TAC []
 ]
) >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`EL (LENGTH ms_list − 1) ms_list`, `ms'`] >>
QSPECL_X_ASSUM  ``!ms ms'. _`` [`EL (LENGTH ms_list − 1) ms_list`, `ms'`] >>
subgoal `MEM (EL (LENGTH ms_list − 1) ms_list) ms_list` >- (
 subgoal `LENGTH ms_list − 1 < LENGTH ms_list` >- (
  fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
 ) >>
 METIS_TAC [rich_listTheory.EL_MEM]
) >>
rfs [] >>
Cases_on `C1 (EL (LENGTH ms_list − 1) ms_list)` >> (
 fs [] >>
 QSPECL_X_ASSUM  ``!i. _`` [`LENGTH ms_list − 1`] >>
 QSPECL_X_ASSUM  ``!i. _`` [`LENGTH ms_list − 1`] >>
 fs [] >>
 rfs [] >>
 fs []
)
);

val _ = export_theory();
