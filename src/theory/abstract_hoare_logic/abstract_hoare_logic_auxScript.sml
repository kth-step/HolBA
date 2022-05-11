open HolKernel boolLib bossLib BasicProvers dep_rewrite;

open bir_auxiliaryLib;

open bir_auxiliaryTheory;

val _ = new_theory "abstract_hoare_logic_aux";

(*******************)
(* Generic lemmata *)
(*******************)

Theorem EL_LAST_APPEND:
 !l x.
 EL (LENGTH l) (l ++ [x]) = x
Proof
rpt strip_tac >>
ASSUME_TAC (ISPEC ``l ++ [x]`` rich_listTheory.EL_PRE_LENGTH) >>
fs [GSYM arithmeticTheory.ADD1]
QED

Theorem LAST_TAKE_EL:
 !n l.
 n < LENGTH l ==>
 EL n l = LAST (TAKE (SUC n) l)
Proof
rpt strip_tac >>
subgoal `(TAKE (SUC n) l) <> []` >- (
 subgoal `LENGTH (TAKE (SUC n) l) = SUC n` >- (
  irule listTheory.LENGTH_TAKE >>
  fs []
 ) >>
 Cases_on `l` >> (
  fs []
 )
) >>
IMP_RES_TAC listTheory.LAST_EL >>
fs [] >>
metis_tac [listTheory.EL_TAKE, prim_recTheory.LESS_SUC_REFL]
QED

Theorem INDEX_FIND_MEM:
 !P l x.
 P x ==>
 MEM x l ==>
 ?i x'. INDEX_FIND 0 P l = SOME (i, x')
Proof
Induct_on `l` >> (
 fs []
) >>
rpt strip_tac >| [
 qexists_tac `0` >>
 qexists_tac `h` >>
 fs [INDEX_FIND_EQ_SOME_0],

 Cases_on `P h` >| [
  qexists_tac `0` >>
  qexists_tac `h` >>
  fs [INDEX_FIND_EQ_SOME_0],

  RES_TAC >>
  qexists_tac `SUC i` >>
  qexists_tac `x'` >>
  fs [listTheory.INDEX_FIND_def] >>
  REWRITE_TAC [Once listTheory.INDEX_FIND_add] >>
  fs []
 ]
]
QED

Theorem MEM_HD:
 !l.
 l <> [] ==>
 MEM (HD l) l
Proof
Cases_on `l` >> (
 fs []
)
QED

Theorem FILTER_MEM:
 !P l l' x.
 FILTER P l = l' ==>
 MEM x l' ==>
 P x /\ MEM x l
Proof
rw [] >>
fs [listTheory.MEM_FILTER]
QED

(*
Theorem MEM_EL_CONS:
 !n e l.
 n > 0 ==>
 n < SUC (LENGTH l) ==>
 MEM (EL n (e::l)) l
Proof
rpt strip_tac >>
fs [listTheory.MEM_EL] >>
qexists_tac `PRE n` >>
fs [] >>
irule rich_listTheory.EL_CONS >>
fs []
QED
*)

(*
Theorem FILTER_NOT_MEM:
!P l l' x.
FILTER P l = l' ==>
MEM x l ==>
~MEM x l' ==>
~P x
Proof
rpt strip_tac >>
rw [] >>
fs [listTheory.MEM_FILTER]
QED
*)

Theorem FILTER_OLEAST_HD:
 !P l l'.
 FILTER P l = l' ==>
 LENGTH l' > 0 ==>
 ?i. (OLEAST i. oEL i l = SOME (HD l')) = SOME i
Proof
cheat
QED

(* Note: Since l can have duplicate elements, we need to make sure
 * EL i l is the FIRST encounter of HD l' in l. *)
Theorem FILTER_BEFORE:
 !P l l' i.
 FILTER P l = l' ==>
 LENGTH l' > 0 ==>
 (OLEAST i. oEL i l = SOME (HD l')) = SOME i ==>
 (!i'. i' < i ==> ~P (EL i' l) /\ ~MEM (EL i' l) l')
Proof
cheat
QED

(* TODO: Since l can have duplicate elements, we need to make sure
 * EL i l is the LAST encounter of LAST l' in l. *)
(* TODO: Might require list nonempty or OLEAST... *)
Theorem FILTER_AFTER:
 !P l l' i.
 FILTER P l = l' ==>
 (LEAST i. EL i (REVERSE l) = HD l') = i ==>
 (!i'. i' > i ==> ~P (EL i' l) /\ ~MEM (EL i' l) l')
Proof
cheat
QED

(* TODO: This is just plain wrong... *)
Theorem FILTER_ORDER:
 !P l i i' i''.
 EL i' l = EL i (FILTER P l) ==>
 EL i'' l = EL (SUC i) (FILTER P l) ==>
 i' < i''
Proof
cheat
QED

Theorem INDEX_FIND_SUFFIX:
!P n i x_list x.
i < n ==>
INDEX_FIND 0 P x_list = SOME (PRE n, x) ==>
INDEX_FIND 0 P (DROP i x_list) = SOME (PRE (n - i), x)
Proof
cheat
QED

Theorem EL_PRE_CONS_EQ:
!i x x_list x_list'.
 EL (SUC i) (x::x_list) = EL (SUC i) (x::x_list') ==>
 EL i x_list = EL i x_list'
Proof
fs []
QED


(*******************)
(*   FUNPOW_OPT    *)
(*******************)

(*
val FUNPOW_ASSOC = prove(``
!f m n x.
FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)``,

fs [GSYM arithmeticTheory.FUNPOW_ADD]
);
*)

Theorem FUNPOW_OPT_step:
 !f n x x' x''.
 FUNPOW_OPT f (SUC n) x = SOME x'' ==>
 f x = SOME x' ==>
 FUNPOW_OPT f n x' = SOME x''
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_REWRS]
QED

Theorem FUNPOW_OPT_INTER:
 !f n n' ms ms' ms''.
 (FUNPOW_OPT f n ms = SOME ms') ==>
 (FUNPOW_OPT f (n'+n) ms = SOME ms'') ==>
 (FUNPOW_OPT f n' ms' = SOME ms'')
Proof
metis_tac [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
QED

(* TODO: Use FUNPOW_OPT_next_n_NONE instead of this *)
Theorem FUNPOW_OPT_ADD_NONE:
 !f n n' ms ms'.
 (FUNPOW_OPT f n ms = SOME ms') ==>
 (FUNPOW_OPT f n' ms' = NONE) ==> 
 (FUNPOW_OPT f (n'+n) ms = NONE)
Proof
metis_tac [FUNPOW_OPT_def,
           arithmeticTheory.FUNPOW_ADD]
QED

Theorem FUNPOW_OPT_PRE:
 !f n x x' x''.
 n > 0 ==>
 FUNPOW_OPT f n x = SOME x' ==>
 f x = SOME x'' ==>
 FUNPOW_OPT f (PRE n) x'' = SOME x'
Proof
rpt strip_tac >>
Cases_on `n` >> (
 fs [FUNPOW_OPT_REWRS]
)
QED

Theorem FUNPOW_SUB:
 !f m n x.
 m > n ==>
 FUNPOW f (m - n) (FUNPOW f n x) = FUNPOW f m x
Proof
fs [GSYM arithmeticTheory.FUNPOW_ADD]
QED

(*
(* TODO: Same as FUNPOW_OPT_INTER with commutativity of addition *)
val FUNPOW_OPT_split = prove(``
!f n n' s s' s''.
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n + n') s = SOME s'' ==>
FUNPOW_OPT f n' s' = SOME s''``,

metis_tac [FUNPOW_ASSOC, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
);
*)

Theorem FUNPOW_OPT_split2:
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f n' s = SOME s'' ==>
FUNPOW_OPT f (n - n') s'' = SOME s'
Proof
rpt strip_tac >>
metis_tac [FUNPOW_SUB, FUNPOW_OPT_def, arithmeticTheory.FUNPOW_ADD]
QED


(*******************)
(* FUNPOW_OPT_LIST *)
(*******************)

(* Head-recursive version (nicer for most proofs) *)
Definition FUNPOW_OPT_LIST_def:
 (FUNPOW_OPT_LIST f 0 s = SOME [s]) /\
 (FUNPOW_OPT_LIST f (SUC n) s =
  case FUNPOW_OPT_LIST f n s of
   | SOME res_prefix =>
    (case f (LAST res_prefix) of
     | SOME res_last => SOME (SNOC res_last res_prefix)
     | NONE => NONE)
   | NONE => NONE)
End

Theorem FUNPOW_OPT_LIST_SUC_NONE:
 !f n s l.
 FUNPOW_OPT_LIST f n s = SOME l ==>
 f (LAST l) = NONE ==>
 FUNPOW_OPT f (SUC n) s = NONE
Proof
cheat
QED

Theorem FUNPOW_OPT_LIST_SUC_SOME:
 !f n s l x.
 FUNPOW_OPT_LIST f n s = SOME l ==>
 f (LAST l) = SOME x ==>
 FUNPOW_OPT f (SUC n) s = SOME x
Proof
cheat
QED

Theorem FUNPOW_OPT_LIST_NEQ_NONE_PREV:
 !f n s l.
 FUNPOW_OPT_LIST f n s = SOME l ==>
 !n'. n' <= n ==> FUNPOW_OPT f n' s <> NONE
Proof
cheat
QED

(* TODO: Split up in two theorems, one specific for FUNPOW_OPT equivalence? *)
Theorem FUNPOW_OPT_LIST_EQ_SOME:
 !f n s l.
 FUNPOW_OPT_LIST f n s = SOME l <=>
 LENGTH l = (SUC n) /\
 FUNPOW_OPT f n s = SOME (LAST l) /\
 (!n'. n' <= n ==> FUNPOW_OPT f n' s = SOME (EL n' l)) /\
 !i. (SUC i) < LENGTH l ==>
 f (EL i l) = SOME (EL (SUC i) l)
Proof
cheat
(* TODO: Use FUNPOW_OPT_LIST_NEQ_NONE_PREV *)
QED

Theorem FUNPOW_OPT_LIST_EQ_NONE:
 !f n s.
 FUNPOW_OPT_LIST f n s = NONE <=>
 ?n'. n' <= n /\ FUNPOW_OPT f n' s = NONE /\
 (* TODO: Overkill? What is needed on LHS? *)
 (!n''. n'' < n' ==> (FUNPOW_OPT f n'' s <> NONE))
Proof
rpt strip_tac >>
EQ_TAC >| [
 rpt strip_tac >>
 Induct_on `n` >- (
  rpt strip_tac >>
  qexists_tac `0` >>
  fs [FUNPOW_OPT_LIST_def]
 ) >>
 rpt strip_tac >>
 fs [FUNPOW_OPT_LIST_def] >>
 Cases_on `FUNPOW_OPT_LIST f n s` >> (
  fs []
 ) >| [
  qexists_tac `n'` >>
  fs [],

  Cases_on `f (LAST x)` >> (
   fs []
  ) >>
  qexists_tac `SUC n` >>
  fs [] >>
  CONJ_TAC >| [
   (* Looks OK, might be a lemma *)
   metis_tac [FUNPOW_OPT_LIST_SUC_NONE],

   (* Should follow from FUNPOW_OPT_LIST_EQ_SOME - break out to separate lemma? *)
   rpt strip_tac >>
   IMP_RES_TAC FUNPOW_OPT_LIST_NEQ_NONE_PREV >>
   QSPECL_X_ASSUM ``!n'. n' <= n ==> FUNPOW_OPT f n' s <> NONE`` [`n''`] >>
   rfs []
  ]
 ],

 rpt strip_tac >>
 fs [FUNPOW_OPT_LIST_def] >>
 Induct_on `n` >| [
  rpt strip_tac >>
  fs [FUNPOW_OPT_def],

  rpt strip_tac >>
  fs [FUNPOW_OPT_LIST_def] >>
  Cases_on `n' = SUC n` >- (
   fs [] >>
   Cases_on `FUNPOW_OPT_LIST f n s` >> (
    fs []
   ) >>
   Cases_on `f (LAST x)` >> (
    fs []
   ) >>
   fs [] >>
   IMP_RES_TAC FUNPOW_OPT_LIST_SUC_SOME >>
   fs []
  ) >>
  fs []
 ]
]
QED

(* Tail-recursive evaluation of FUNPOW_OPT_LIST *)
Theorem FUNPOW_OPT_LIST_tail:
 !f n s l.
 (FUNPOW_OPT_LIST f 0 s = SOME [s]) /\
 (FUNPOW_OPT_LIST f (SUC n) s =
  case f s of
   | SOME res_head =>
    (case FUNPOW_OPT_LIST f n res_head of
      | SOME res_tail => SOME (s::res_tail)
      | NONE => NONE)
   | NONE => NONE)
Proof
rpt strip_tac >| [
 fs [FUNPOW_OPT_LIST_def],

 Cases_on `f s` >| [
  fs [FUNPOW_OPT_LIST_EQ_NONE] >>
  qexists_tac `1` >>
  fs [FUNPOW_OPT_compute] >>
  rpt strip_tac >>
  Cases_on `n''` >> (
   fs [FUNPOW_OPT_compute]
  ),

  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  Induct_on `n` >> (
   fs [FUNPOW_OPT_LIST_def]
  ) >>
  Cases_on `FUNPOW_OPT_LIST f n x` >- (
   fs [FUNPOW_OPT_LIST_def]
  ) >>
  Cases_on `x'` >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME]
  ) >>
  Cases_on `f (LAST (h::t))` >> (
   fs []
  ) >>
  fs [listTheory.LAST_compute]
 ]
]
QED

Theorem FUNPOW_OPT_LIST_NONEMPTY:
 !f n x l.
 FUNPOW_OPT_LIST f n x = SOME l ==>
 l <> []
Proof
rpt strip_tac >>
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
QED

Theorem FUNPOW_OPT_LIST_LAST:
 !f n x l_opt.
 FUNPOW_OPT_LIST f n x = l_opt ==>
 (case l_opt of
  | SOME l =>
   FUNPOW_OPT f n x = SOME (LAST l)
  | NONE => FUNPOW_OPT f n x = NONE)
Proof
rpt strip_tac >>
Cases_on `l_opt` >| [
 fs [FUNPOW_OPT_LIST_EQ_NONE] >>
 subgoal `?n''. n = n' + n''` >- (
  qexists_tac `n - n'` >>
  fs []
 ) >>
 metis_tac [FUNPOW_OPT_next_n_NONE],
 
 fs [FUNPOW_OPT_LIST_EQ_SOME]
]
QED

Theorem FUNPOW_OPT_LIST_NONE:
 !f n x.
 FUNPOW_OPT_LIST f n x = NONE ==>
 FUNPOW_OPT_LIST f (SUC n) x = NONE
Proof
fs [FUNPOW_OPT_LIST_def]
QED

(*
Theorem FUNPOW_OPT_LIST_CONS:
 !f x n t.
 FUNPOW_OPT_LIST f n x = SOME t ==>
 ((?h. f (LAST t) = SOME h /\
       FUNPOW_OPT_LIST f (SUC n) x = SOME (SNOC h t)) \/ FUNPOW_OPT_LIST f (SUC n) x = NONE)
Proof
rpt strip_tac >>
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
QED
*)

Theorem FUNPOW_OPT_LIST_FRONT_PRE:
 !f x n t.
 FUNPOW_OPT_LIST f (SUC n) x = SOME t ==>
 FUNPOW_OPT_LIST f n x = SOME (FRONT t)
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_LIST_def]  >>
Cases_on `FUNPOW_OPT_LIST f n x` >> (
 fs []
) >>
Cases_on `f (LAST x')` >> (
 fs []
) >>
rw [listTheory.FRONT_DEF] >>
fs [rich_listTheory.FRONT_APPEND]
QED

Theorem FUNPOW_OPT_LIST_BACK_PRE:
 !f x x' n l.
 FUNPOW_OPT_LIST f (SUC n) x = SOME l ==>
 f x = SOME x' ==>
 FUNPOW_OPT_LIST f n x' = SOME (TL l)
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_LIST_tail] >>
Cases_on `FUNPOW_OPT_LIST f n x'` >> (
 fs []
) >>
rw []
QED

Theorem FUNPOW_OPT_LIST_BACK_INCR:
 !f x x' n t.
 FUNPOW_OPT_LIST f n x' = SOME t ==>
 f x = SOME x' ==>
 FUNPOW_OPT_LIST f (SUC n) x = SOME (x::t)
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_LIST_tail]
QED

Theorem FUNPOW_OPT_LIST_LENGTH:
 !n l f x.
 FUNPOW_OPT_LIST f n x = SOME l ==>
 LENGTH l = (SUC n)
Proof
Induct_on `n` >- (
 fs [FUNPOW_OPT_LIST_def]
) >>
rpt strip_tac >>
subgoal `FUNPOW_OPT_LIST f n x = SOME (FRONT l)` >- (
 metis_tac [FUNPOW_OPT_LIST_FRONT_PRE]
) >>
RES_TAC >>
IMP_RES_TAC FUNPOW_OPT_LIST_NONEMPTY >>
IMP_RES_TAC rich_listTheory.LENGTH_FRONT >>
fs []
QED

Theorem FUNPOW_OPT_SUBLIST:
 !f n n' x l.
 n' <= n ==>
 FUNPOW_OPT_LIST f (SUC n) x = SOME l ==>
 FUNPOW_OPT_LIST f (SUC n − n') (LAST (TAKE (SUC n') l)) = SOME (DROP n' l) ==>
 FUNPOW_OPT_LIST f (n − n') (LAST (TAKE (SUC (SUC n')) l)) = SOME (DROP (SUC n') l)
Proof
rpt strip_tac >>
fs [FUNPOW_OPT_LIST_EQ_SOME] >>
rpt strip_tac >| [
 (* OK: starting one step later but taking one step less leads to same end result *)
 irule FUNPOW_OPT_step >>
 qexists_tac `LAST (TAKE (SUC n') l)` >>
 fs [] >>
 strip_tac >| [
  QSPECL_X_ASSUM ``!i. SUC i < LENGTH l ==> f (EL i l) = SOME (EL (SUC i) l)`` [`n'`] >>
  rfs [] >>
  `EL n' l = LAST (TAKE (SUC n') l) /\ EL (SUC n') l = LAST (TAKE (SUC (SUC n')) l)` suffices_by (
   rpt strip_tac >>
   fs [] >>
   rw []
  ) >>
  strip_tac >> (
   irule LAST_TAKE_EL >>
   fs []
  ),

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
 qexists_tac `x` >>
 qexists_tac `SUC n'` >>
 rfs [] >>
 strip_tac >| [
  irule LAST_TAKE_EL >>
  fs [],

  ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule listTheory.EL_DROP >>
  fs []
 ],

 (* OK: Property should hold for element i of sublist starting from element SUC n' *)
 QSPECL_X_ASSUM ``!i. SUC i < LENGTH l - n' ==>
                  f (EL i (DROP n' l)) = SOME (EL (SUC i) (DROP n' l))`` [`SUC i`] >>
 rfs [] >>
 subgoal `EL (SUC i) (DROP n' l) = EL i (DROP (SUC n') l)` >- (
  fs [rich_listTheory.DROP_CONS_EL]
 ) >>
 subgoal `EL (SUC (SUC i)) (DROP n' l) = EL (SUC i) (DROP (SUC n') l)` >- (
  fs [rich_listTheory.DROP_CONS_EL]
 ) >>
 fs []
]
QED

Theorem FUNPOW_OPT_LIST_APPEND:
 !f n n' x l.
 n' <= n ==>
 FUNPOW_OPT_LIST f n x = SOME l ==>
 ?l' l''.
 FUNPOW_OPT_LIST f n' x = SOME l' /\
 FUNPOW_OPT_LIST f (n - n') (LAST l') = SOME l'' /\
 l' ++ (DROP 1 l'') = l
Proof
rpt strip_tac >>
qexists_tac `TAKE (SUC n') l` >>
qexists_tac `DROP n' l` >>
rpt strip_tac >| [
 Induct_on `n'` >- (
  strip_tac >>
  Cases_on `n` >- (
   fs [FUNPOW_OPT_LIST_def] >>
   rw []
  ) >>
  fs [FUNPOW_OPT_LIST_EQ_SOME] >>
  Cases_on `l` >> (
   fs []
  )
 ) >>
 rpt strip_tac >>
 Q.SUBGOAL_THEN `n' ≤ n` (fn thm => fs [thm]) >- (
  fs []
 ) >>
 fs [FUNPOW_OPT_LIST_def] >>
 Cases_on `f (LAST (TAKE (SUC n') l))` >- (
  fs [] >>
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
 fs [FUNPOW_OPT_LIST_EQ_SOME] >>
 subgoal `x' = EL (SUC n') l` >- (
  QSPECL_X_ASSUM ``!n'.
          n' <= n ==>
          FUNPOW_OPT f n' x = SOME (EL n' l)`` [`n'`] >>
  rfs [] >>
  QSPECL_X_ASSUM ``!i. i < n ==> f (EL i l) = SOME (EL (SUC i) l)`` [`n'`] >>
  rfs [] >>
  `LAST (TAKE (SUC n') l) = EL n' l` suffices_by (
   rpt strip_tac >>
   fs []
  ) >>
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule LAST_TAKE_EL >>
  fs []
 ) >>
 rw [] >>
 Q.SUBGOAL_THEN `TAKE (SUC (SUC n')) l = TAKE (SUC n') l ++ TAKE 1 (DROP (SUC n') l)` (fn thm => fs [thm]) >- (
  Q.SUBGOAL_THEN `(SUC (SUC n')) = (SUC n') + 1` (fn thm => fs [thm]) >- (
   fs [arithmeticTheory.ADD1]
  ) >>
  fs [listTheory.TAKE_SUM]
 ) >>
 fs [listTheory.TAKE1_DROP],

 (* Start off after n' steps, take n - n' steps *)
 Induct_on `n'` >- (
  strip_tac >>
  fs [] >>
  Q.SUBGOAL_THEN `TAKE 1 l = [x]` (fn thm => fs [thm]) >- (
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   Cases_on `n` >- (
    fs [FUNPOW_OPT_def] >>
    subgoal `l <> []` >- (
     Cases_on `l` >> (
      fs []
     )
    ) >>
    fs [listTheory.TAKE1]
   ) >>
   QSPECL_X_ASSUM ``!n''. n'' <= SUC n' ==> FUNPOW_OPT f n'' x = SOME (EL n'' l)`` [`0`] >>
   fs [FUNPOW_OPT_def] >>
   subgoal `l <> []` >- (
    Cases_on `l` >> (
     fs []
    )
   ) >>
   fs [listTheory.TAKE1]
  )
 ) >>
 Cases_on `n` >- (
  fs []
 ) >>
 rpt strip_tac >>
 Q.SUBGOAL_THEN `n' ≤ SUC n''` (fn thm => fs [thm]) >- (
  fs []
 ) >>
 (* If you take one more step, if you start one step earlier, then the result is the same as before
  * with one less step dropped (from head) *)
 irule FUNPOW_OPT_SUBLIST >>
 fs [] >>
 qexists_tac `x` >>
 fs [],

 fs [rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1]
]
QED

Theorem FUNPOW_OPT_LIST_EL_SOME:
 !f n n' x l.
 FUNPOW_OPT_LIST f n x = SOME l ==>
 n' <= n ==>
 ?x'. FUNPOW_OPT f n' x = SOME x'
Proof
rpt strip_tac >>
IMP_RES_TAC FUNPOW_OPT_LIST_APPEND >>
qexists_tac `LAST l'` >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs []
QED

Theorem FUNPOW_OPT_LIST_EL_NONE:
 !f n n' x.
 FUNPOW_OPT_LIST f n x = NONE ==>
 (n' >= n) ==>
 FUNPOW_OPT f n' x = NONE
Proof
rpt strip_tac >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs [] >>
subgoal `?n''. n' = n + n''` >- (
 fs [arithmeticTheory.LESS_EQUAL_ADD]
) >>
metis_tac [FUNPOW_OPT_next_n_NONE]
QED

Theorem FUNPOW_OPT_LIST_EL_NEXT:
 !f n x x'.
 FUNPOW_OPT_LIST f n x = SOME x' ==>
 FUNPOW_OPT f (SUC n) x = f (LAST x')
Proof
rpt strip_tac >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs [] >>
Cases_on `f (LAST x')` >| [
 fs [arithmeticTheory.ADD1] >>
 ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
 irule FUNPOW_OPT_ADD_NONE >>
 qexists_tac `LAST x'` >>
 fs [FUNPOW_OPT_compute],

 fs [arithmeticTheory.ADD1] >>
 ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] >>
 irule FUNPOW_OPT_ADD_thm >>
 qexists_tac `LAST x'` >>
 fs [FUNPOW_OPT_compute]
]
QED

Theorem FUNPOW_OPT_LIST_EXISTS:
 !f n n' x x'.
 FUNPOW_OPT f n x = SOME x' ==>
 n' <= n ==>
 ?l. FUNPOW_OPT_LIST f n' x = SOME l
Proof
Induct_on `n` >- (
 rpt strip_tac >>
 qexists_tac `[x']` >>
 fs [] >>
 rw [] >>
 fs [FUNPOW_OPT_LIST_def, FUNPOW_OPT_def]
) >>
rpt strip_tac >>
Cases_on `n' = SUC n` >- (
 fs [FUNPOW_OPT_LIST_def] >>
 Cases_on `FUNPOW_OPT_LIST f n x` >- (
  fs [] >>
  IMP_RES_TAC FUNPOW_OPT_LIST_NONE >>
  subgoal `?x''. FUNPOW_OPT f n x = SOME x''` >- (
   irule FUNPOW_OPT_prev_EXISTS >>
   qexists_tac `SUC n` >>
   qexists_tac `x'` >>
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
 qexists_tac `SUC n` >>
 qexists_tac `x'` >>
 fs []
) >>
QSPECL_X_ASSUM ``!f n' x x'. _`` [`f`, `n'`, `x`, `x''`] >>
fs []
QED

Theorem FUNPOW_OPT_LIST_EXISTS_nicer:
 !f n n' x x'.
 FUNPOW_OPT f n x = SOME x' ==>
 n' <= n ==>
 ?l. FUNPOW_OPT_LIST f n' x = SOME (x::l)
Proof
rpt strip_tac >>
IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS >>
Cases_on `n'` >> Cases_on `l` >| [
 fs [FUNPOW_OPT_LIST_def],

 fs [FUNPOW_OPT_LIST_def],

 fs [FUNPOW_OPT_LIST_tail] >>
 Cases_on `f x` >> (
  fs []
 ) >>
 Cases_on `FUNPOW_OPT_LIST f n'' x''` >> (
  fs []
 ),

 qexists_tac `t` >>
 fs [FUNPOW_OPT_LIST_tail] >>
 Cases_on `f x` >> (
  fs []
 ) >>
 Cases_on `FUNPOW_OPT_LIST f n'' x''` >> (
  fs []
 )
]
QED

Theorem FUNPOW_OPT_LIST_EXISTS_exact:
 !f n x x'.
 FUNPOW_OPT f n x = SOME x' ==>
 n > 0 ==>
 ?l. FUNPOW_OPT_LIST f n x = SOME (x::(SNOC x' l))
Proof
rpt strip_tac >>
IMP_RES_TAC FUNPOW_OPT_LIST_EXISTS_nicer >>
QSPECL_X_ASSUM ``!n'. n' <= n ==> ?l. FUNPOW_OPT_LIST f n' x = SOME (x::l)`` [`n`] >>
fs [] >>
IMP_RES_TAC FUNPOW_OPT_LIST_LAST >>
fs [listTheory.LAST_DEF] >>
Cases_on `l = []` >> (
 fs []
) >| [
 (* TODO: Lemma *)
 cheat,

 qexists_tac `FRONT l` >>
 rw [] >>
 metis_tac [listTheory.APPEND_FRONT_LAST]
]
QED

Theorem FUNPOW_OPT_LIST_EL:
 !f n n' x x' l.
 FUNPOW_OPT_LIST f n x = SOME l ==>
 n' <= n ==>
 FUNPOW_OPT f n' x = SOME x' ==>
 (EL n' l) = x'
Proof
rpt strip_tac >>
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
QED

(*
Theorem FUNPOW_OPT_LIST_INDEX_FIND:
 !f P n x l i x'.
 FUNPOW_OPT_LIST f n x = SOME l ==>
 INDEX_FIND 0 P l = SOME (i, x') ==>
 FUNPOW_OPT f i x = SOME x'
Proof
rpt strip_tac >>
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
QED
*)

Theorem FUNPOW_OPT_LIST_FIRST:
 !f n x x' x_list.
 n > 0 ==>
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 f x = SOME x' ==>
 FUNPOW_OPT_LIST f (PRE n) x' = SOME x_list
Proof
rpt strip_tac >>
Cases_on `n` >- (
 fs []
) >>
fs [FUNPOW_OPT_LIST_EQ_SOME, FUNPOW_OPT_REWRS] >>
rpt CONJ_TAC >| [
 QSPECL_X_ASSUM ``!n''. n'' <= SUC n' ==> FUNPOW_OPT f n'' x = SOME (EL n'' (x::x_list))`` [`SUC n'`] >>
 Cases_on `x_list` >- (
  fs []
 ) >>
 fs [listTheory.LAST_CONS],

 rpt strip_tac >>
 QSPECL_X_ASSUM ``!n''. n'' <= SUC n' ==> FUNPOW_OPT f n'' x = SOME (EL n'' (x::x_list))`` [`SUC n''`] >>
 rfs [FUNPOW_OPT_REWRS],

 rpt strip_tac >>
 QSPECL_X_ASSUM ``!i. i < LENGTH x_list ==> f (EL i (x::x_list)) = SOME (EL i x_list)`` [`SUC i`] >>
 fs []
]
QED

Theorem FUNPOW_OPT_LIST_PRE:
 !f n x x' x_list.
 n > 0 ==>
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 f x = SOME x' ==>
 FUNPOW_OPT_LIST f (PRE n) x' = SOME x_list
Proof
rpt strip_tac >>
Cases_on `n` >> (
 fs [FUNPOW_OPT_LIST_tail]
) >>
Cases_on `FUNPOW_OPT_LIST f n' x'` >> (
 fs []
)
QED

Theorem FUNPOW_OPT_LIST_SUFFIX:
!f n i x x_list.
FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
FUNPOW_OPT_LIST f (n - SUC i) (EL i x_list) = SOME (EL i x_list::DROP (SUC i) x_list)
Proof
cheat
QED

(*
val FUNPOW_OPT_todoname = prove(``
!f n n' n'' P ms ms_list.
FUNPOW_OPT_LIST f n ms = SOME (ms::ms_list) ==>
FUNPOW_OPT f n'' ms =
        SOME
          (EL (LENGTH (FILTER P ms_list) - 1)
             (FILTER P ms_list)) ==>
n' < n - n'' ==>
FUNPOW_OPT f (n' + n'') ms = SOME (EL (PRE (n' + n'')) ms_list)``,

rpt strip_tac >>
fs [FUNPOW_OPT_LIST_EQ_SOME] >>
irule rich_listTheory.EL_CONS >>
(* TODO: Likely not provable... *)
cheat
);
*)

(* For weak_rel_steps_list_states_subgoal_2_lemma *)
Theorem FUNPOW_OPT_LIST_FILTER_NULL:
!f n x x' x_list P P'.
 n > 0 ==>
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 INDEX_FIND 0 P x_list = SOME (PRE n,x') ==>
 FILTER P' x_list = [] ==>
 INDEX_FIND 0 (\x. P x \/ P' x) x_list = SOME (PRE n,x')
Proof
rpt strip_tac >>
subgoal `?x''. FUNPOW_OPT f n x = SOME x''` >- (
 irule FUNPOW_OPT_LIST_EL_SOME >>
 qexists_tac `x::x_list` >>
 qexists_tac `n` >>
 fs []
) >>
fs [listTheory.FILTER_EQ_NIL] >>
subgoal `EL (PRE n) x_list = x''` >- (
 subgoal `(EL n (x::x_list)) = x''` >- (
  irule FUNPOW_OPT_LIST_EL >>
  qexists_tac `f` >>
  qexists_tac `n` >>
  qexists_tac `x` >>
  fs []
 ) >>
 metis_tac [rich_listTheory.EL_CONS, arithmeticTheory.GREATER_DEF]
) >>
fs [INDEX_FIND_EQ_SOME_0, listTheory.EVERY_EL]
QED

Theorem FUNPOW_OPT_LIST_PREFIX:
!f n n' i x x_list x_list'.
 FUNPOW_OPT_LIST f n x = SOME x_list ==>
 FUNPOW_OPT_LIST f n' x = SOME x_list' ==>
 n' <= n ==>
 x_list' <<= x_list
Proof
rpt strip_tac >>
fs [rich_listTheory.IS_PREFIX_APPEND] >>
IMP_RES_TAC FUNPOW_OPT_LIST_APPEND >>
qexists_tac `DROP 1 l''` >>
rw [] >>
fs []
QED

Theorem FUNPOW_OPT_LIST_EL_EQ:
!f n n' i x x_list x_list'.
 FUNPOW_OPT_LIST f n x = SOME x_list ==>
 FUNPOW_OPT_LIST f n' x = SOME x_list' ==>
 n' < n ==>
 i <= n' ==>
 EL i x_list' = EL i x_list
Proof
rpt strip_tac >>
irule rich_listTheory.is_prefix_el >>
rpt strip_tac >| [
 fs [FUNPOW_OPT_LIST_EQ_SOME],

 fs [FUNPOW_OPT_LIST_EQ_SOME],

 irule FUNPOW_OPT_LIST_PREFIX >>
 qexists_tac `f` >>
 qexists_tac `n` >>
 qexists_tac `n'` >>
 qexists_tac `x` >>
 fs []
]
QED

Theorem FUNPOW_OPT_LIST_FILTER_FIRST:
!f n x x' x_list P P'.
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 INDEX_FIND 0 P x_list = SOME (PRE n,x') ==>
 LENGTH (FILTER P' x_list) > 0 ==>
 ~P' (LAST x_list) ==>
 ?n'.
   (n' > 0 /\
    ?x_list'.
      FUNPOW_OPT_LIST f n' x = SOME (x::x_list') /\
      INDEX_FIND 0 (\x''. P' x'' \/ P x'') x_list' = SOME (PRE n', HD (FILTER P' x_list))) /\
   (n > n' /\
    ?x_list'.
      FUNPOW_OPT_LIST f (n - n')
        (HD (FILTER P' x_list)) =
      SOME (HD (FILTER P' x_list)::x_list') /\
      INDEX_FIND 0 P x_list' = SOME (PRE (n - n'), x')) /\ n' < n /\ n' > 0
Proof
rpt strip_tac >>
subgoal `?x''. x'' = EL 0 (FILTER P' x_list)` >- (
  metis_tac []
) >>
subgoal `?x_list'. FILTER P' x_list = x_list'` >- (
 fs []
) >>
subgoal `LENGTH x_list > 0` >- (
 fs [INDEX_FIND_EQ_SOME_0]
) >>
subgoal `?i. (OLEAST i. oEL i x_list = SOME x'') = SOME i /\ i < (PRE n)` >- (
 IMP_RES_TAC FILTER_OLEAST_HD >>
 gs [] >>
 fs [whileTheory.OLEAST_EQ_SOME] >>

 Cases_on `i = PRE n` >- (
  subgoal `P' x''` >- (
   IMP_RES_TAC FILTER_MEM >>
   QSPECL_X_ASSUM ``!x. MEM x x_list' ==> P' x`` [`x''`] >>
   PAT_ASSUM ``x'' = HD x_list'`` (fn thm => fs [thm]) >>
   Q.SUBGOAL_THEN `MEM (HD x_list') x_list'` (fn thm => rfs [thm]) >- (
    rfs [MEM_HD, listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
   )
  ) >>
  subgoal `LAST x_list = x'` >- (
   fs [INDEX_FIND_EQ_SOME_0] >>
   fs [FUNPOW_OPT_LIST_EQ_SOME] >>
   subgoal `x_list <> []` >- (
    Cases_on `x_list` >> (
     fs []
    )
   ) >>
   metis_tac [listTheory.LAST_EL]
  ) >>
  subgoal `x'' = x'` >- (
   fs [listTheory.oEL_THM, INDEX_FIND_EQ_SOME_0]
  ) >>
  rw [] >>
  fs []
 ) >>
 fs [FUNPOW_OPT_LIST_EQ_SOME, listTheory.oEL_THM]
) >>
qexists_tac `SUC i` >>
fs [] >>
rpt strip_tac >| [
 (* subgoal 3a. OK: SUC i steps taken until first encounter of l
  * EL i ms_list = HD ms_list' is among assumptions *)
 subgoal `?x_list''. FUNPOW_OPT_LIST f (SUC i) x = SOME (x::x_list'')` >- (
  subgoal `SUC i <= n` >- (
   fs []
  ) >>
  IMP_RES_TAC FUNPOW_OPT_LIST_APPEND >>
  fs [] >>
  qexists_tac `TL l'` >>
  subgoal `x = HD l'` >- (
   Cases_on `l'` >> (
    fs [FUNPOW_OPT_LIST_EQ_SOME]
   )
  ) >>
  subgoal `~NULL l'` >- (
   Cases_on `l'` >> (
    fs [FUNPOW_OPT_LIST_EQ_SOME]
   )
  ) >>
  metis_tac [listTheory.CONS]
 ) >>
 qexists_tac `x_list''` >>
 fs [] >>
 REWRITE_TAC [INDEX_FIND_EQ_SOME_0] >>
 rpt strip_tac >| [
  fs [FUNPOW_OPT_LIST_EQ_SOME],

  fs [whileTheory.OLEAST_EQ_SOME] >>
  subgoal `EL i x_list'' = EL i x_list` >- (
   irule EL_PRE_CONS_EQ >>
   qexists_tac `x` >>
   irule FUNPOW_OPT_LIST_EL_EQ >>
   qexists_tac `f` >>
   qexists_tac `n` >>
   qexists_tac `SUC i` >>
   qexists_tac `x` >>
   fs []
  ) >>
  fs [listTheory.oEL_THM],

  subgoal `MEM (HD x_list') (FILTER P' x_list)` >- (
   rw [] >>
   irule MEM_HD >>
   Cases_on `FILTER P' x_list` >> (
    fs []
   )
  ) >>
  fs [listTheory.MEM_FILTER],

  (* Before first element in filter list, neither P' nor P holds *)
  (* P': by FILTER_BEFORE *)
  (* P: by INDEX_FIND 0 P x_list = SOME (PRE n,x') *)
  fs [] >| [
   IMP_RES_TAC FILTER_BEFORE >>
   QSPECL_X_ASSUM ``!i. (OLEAST i. oEL i x_list = SOME (HD x_list')) = SOME i ==> !i'. i' < i ==> ~P' (EL i' x_list)`` [`i`] >>
   gs [] >>
   QSPECL_X_ASSUM ``!i'. i' < i ==> ~P' (EL i' x_list)`` [`j'`] >>
   rfs [] >>
   `EL j' x_list'' = EL j' x_list` suffices_by (
    metis_tac []
   ) >>
   irule EL_PRE_CONS_EQ >>
   qexists_tac `x` >>
   irule FUNPOW_OPT_LIST_EL_EQ >>
   qexists_tac `f` >>
   qexists_tac `n` >>
   qexists_tac `SUC i` >>
   qexists_tac `x` >>
   fs [],

   fs [INDEX_FIND_EQ_SOME_0] >>
   QSPECL_X_ASSUM ``!j'. j' < PRE n ==> ~P (EL j' x_list)`` [`j'`] >>
   rfs [] >>
   `EL j' x_list'' = EL j' x_list` suffices_by (
    metis_tac []
   ) >>
   irule EL_PRE_CONS_EQ >>
   qexists_tac `x` >>
   irule FUNPOW_OPT_LIST_EL_EQ >>
   qexists_tac `f` >>
   qexists_tac `n` >>
   qexists_tac `SUC i` >>
   qexists_tac `x` >>
   fs []
  ]
 ],

 (* subgoal 3b. OK: (n - SUC i) steps taken from first encounter of l will get you to ms' *)
 fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM] >>
 qexists_tac `DROP (SUC i) x_list` >>
 rpt strip_tac >| [
  metis_tac [FUNPOW_OPT_LIST_SUFFIX],

  irule INDEX_FIND_SUFFIX >>
  fs []
 ]
]
QED

Theorem FUNPOW_OPT_LIST_FILTER_LAST:
!f n x x' x_list x_list' P P'.
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 INDEX_FIND 0 P x_list = SOME (PRE n,x') ==>
 FILTER P' x_list = x_list' ==>
 LENGTH x_list' > 0 ==>
 ?n'. (?x_list''.
  FUNPOW_OPT_LIST f n' (LAST x_list') =
   SOME (LAST x_list'::x_list'') /\
  INDEX_FIND 0 (\x''. P' x'' \/ P x'') x_list'' =
   SOME (PRE n', x')) /\ n' > 0
Proof
cheat
QED

Theorem FUNPOW_OPT_LIST_FILTER_BETWEEN:
!f n x x' x_list x_list' P P' i.
 FUNPOW_OPT_LIST f n x = SOME (x::x_list) ==>
 INDEX_FIND 0 P x_list = SOME (PRE n,x') ==>
 FILTER P' x_list = x_list' ==>
 i < (LENGTH x_list') - 1 ==>
 ?n' n''.
  (?x_list''.
   FUNPOW_OPT_LIST f n' (EL i x_list') =
    SOME (EL i x_list'::x_list'') /\
   INDEX_FIND 0 (\x''. P' x'' \/ P x'') x_list'' =
    SOME (PRE n', EL (i + 1) x_list')) /\
  (?x_list''.
   FUNPOW_OPT_LIST f n'' (EL (i + 1) x_list') =
    SOME (EL (i + 1) x_list'::x_list'') /\
   INDEX_FIND 0 P x_list'' = SOME (PRE n'', x')) /\
  n' < n /\ n' > 0 /\ n'' < n /\ n'' > 0
Proof
cheat
QED

val _ = export_theory();
