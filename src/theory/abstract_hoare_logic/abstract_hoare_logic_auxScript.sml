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

Theorem MEM_OLEAST:
!l x.
MEM x l ==>
?i. (OLEAST i. oEL i l = SOME x) = SOME i
Proof
Induct >> (
 fs [listTheory.MEM, listTheory.LENGTH]
) >>
rpt strip_tac >| [
 qexists_tac `0` >>
 fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM],

 qpat_assum `!x. _` (fn thm => imp_res_tac thm) >>
 Cases_on `h = x` >- (
  qexists_tac `0` >>
  fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM]
 ) >>
 qexists_tac `SUC i` >>
 fs [whileTheory.OLEAST_EQ_SOME, listTheory.oEL_THM] >>
 rpt strip_tac >>
 Cases_on `i'` >- (
  fs []
 ) >>
 QSPECL_X_ASSUM ``!i'. _`` [`n`] >>
 gs []
]
QED


Theorem FILTER_HD_OLEAST_EXISTS:
 !P l l'.
 FILTER P l = l' ==>
 LENGTH l' > 0 ==>
 ?i. (OLEAST i. oEL i l = SOME (HD l')) = SOME i
Proof
rpt strip_tac >>
subgoal `MEM (HD l') l'` >- (
 irule MEM_HD >>
 fs [listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
) >>
subgoal `MEM (HD l') l` >- (
 metis_tac [listTheory.MEM_FILTER]
) >>
imp_res_tac MEM_OLEAST >>
qexists_tac `i` >>
fs []
QED

Theorem INDEX_FIND_SUFFIX:
!P n i x_list x.
i < n ==>
INDEX_FIND 0 P x_list = SOME (PRE n, x) ==>
INDEX_FIND 0 P (DROP i x_list) = SOME (PRE (n - i), x)
Proof
rpt strip_tac >>
fs [INDEX_FIND_EQ_SOME_0] >>
rpt strip_tac >| [
 subgoal `EL (PRE (n - i)) (DROP i x_list) = EL ((PRE (n - i)) + i) x_list` >- (
  irule listTheory.EL_DROP >>
  fs []
 ) >>
 fs [] >>
 `i + PRE (n - i) = PRE n` suffices_by (
  rpt strip_tac >>
  fs []
 ) >>
 fs [],

 subgoal `j' + i < PRE n` >- (
  fs [arithmeticTheory.LESS_MONO_ADD_EQ]
 ) >>
 Q.SUBGOAL_THEN `EL j' (DROP i x_list) = EL (j' + i) x_list` (fn thm => fs [thm]) >- (
  irule listTheory.EL_DROP >>
  fs []
 ) >>
 QSPECL_X_ASSUM ``!j'. j' < PRE n ==> ~P (EL j' x_list)`` [`i + j'`] >>
 fs []
]
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

Theorem FUNPOW_OPT_split:
!f n' n s s'' s'.
n > n' ==>
FUNPOW_OPT f n s = SOME s' ==>
FUNPOW_OPT f (n - n') s = SOME s'' ==>
FUNPOW_OPT f n' s'' = SOME s'
Proof
rpt strip_tac >>
irule FUNPOW_OPT_INTER >>
qexistsl_tac [`s`, `n - n'`] >>
fs []
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

(* TODO: Relax the first OLEAST? *)
Theorem FUNPOW_OPT_cycle:
 !f s s' n n'.
 (OLEAST n. n > 0 /\ FUNPOW_OPT f n s = SOME s) = SOME n ==>
 s <> s' ==>
 (OLEAST n'. FUNPOW_OPT f n' s = SOME s') = SOME n' ==>
 n' < n
Proof
rpt strip_tac >>
CCONTR_TAC >>
Cases_on `n' = n` >- (
 fs [whileTheory.OLEAST_EQ_SOME]
) >>
subgoal `n' > n` >- (
 gs []
) >>
subgoal `FUNPOW_OPT f (n' - n) s = SOME s'` >- (
 irule FUNPOW_OPT_split2 >>
 fs [whileTheory.OLEAST_EQ_SOME] >>
 qexists_tac `s` >>
 fs []
) >>
fs [whileTheory.OLEAST_EQ_SOME] >>
QSPECL_X_ASSUM ``!n''. n'' < n' ==> FUNPOW_OPT f n'' s <> SOME s'`` [`n' - n`] >>
gs []
QED


val _ = export_theory();
