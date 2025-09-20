(*
  Program logic asserting postconditions upon some future encounter of the ending label set.
*)
open HolKernel boolLib bossLib BasicProvers dep_rewrite prim_recTheory;

open holba_auxiliaryLib;

open holba_auxiliaryTheory;

open transition_systemTheory total_program_logicTheory;

val _ = new_theory "eventual_program_logic";

(* Total-correctness enventual-encounter judgment *)
(* TODO: Currently, "weak" is lumped in with the transition system,
 * so a separate transition system could be used for eventual-encounter
 * with another notion of weak characterised by a eventual_enc_def,
 * using "weak" as execution in contract, and eventual_enc TS among premises *)
Definition f_jgmt_def:
 f_jgmt TS (l:'b) (ls:'b->bool) pre post =
 !s.
  TS.ctrl s = l ==>
  pre s ==>
  ?n s'.
   (n > 0 /\
    FUNPOW_OPT TS.trs n s = SOME s' /\
    TS.ctrl s' IN ls
   ) /\
  post s'
End

Theorem f_jgmt_to_t_jgmt:
 !TS l ls pre post.
 first_enc TS ==>
 normal TS l ls pre ==>
 f_jgmt TS l ls pre post ==>
 t_jgmt TS l ls pre post
Proof
rpt strip_tac >>
gs[t_jgmt_def, f_jgmt_def, normal_def] >>
rpt strip_tac >>
`!s' n.
 n > 0 /\ FUNPOW_OPT TS.trs n s = SOME s' /\ TS.ctrl s' IN ls ==>
 TS.trs s' = NONE` by metis_tac[] >>
`?n s'. n > 0 /\ FUNPOW_OPT TS.trs n s = SOME s' /\ TS.ctrl s' IN ls /\
              post s'` by metis_tac[] >>
QSPECL_ASSUM ``!s' n. _`` [`s'`, `n`] >>
gs[first_enc_def] >>
qexists_tac `s'` >>
gs[] >>
qexists_tac `n` >>
gs[] >>
rpt strip_tac >>
Cases_on `n > 1` >- (
 `?s''. FUNPOW_OPT TS.trs n' s = SOME s''` by metis_tac[FUNPOW_OPT_prev_EXISTS] >>
 qexists_tac `s''` >>
 gs[] >>
 CCONTR_TAC >>
 gs[] >>
 QSPECL_ASSUM ``!s' n. _`` [`s''`, `n'`] >>
 gs[] >>
 `FUNPOW_OPT TS.trs (n'+1) s = NONE` suffices_by (
  strip_tac >>
  `!n'.
        n' < n ==>
        ?s'. FUNPOW_OPT TS.trs n' s = SOME s'` by (
   strip_tac >>
   strip_tac >>
   irule FUNPOW_OPT_prev_EXISTS >>
   qexistsl_tac [`n`, `s'`] >>
   gs[]
  ) >>
  QSPECL_ASSUM ``!n'. _`` [`n' + 1`] >>
  Cases_on `n' = n-1` >- (
   gs[]
  ) >>
  `n' + 1 < n` by gs[] >>
  `?s'. FUNPOW_OPT TS.trs (n' + 1) s = SOME s'` by metis_tac[] >>
  gs[]
 ) >>
 REWRITE_TAC[Once arithmeticTheory.ADD_SYM] >>
 irule FUNPOW_OPT_ADD_NONE >>
 REWRITE_TAC[arithmeticTheory.ONE] >>
 gs[FUNPOW_OPT_REWRS]
) >>
gs[]
QED

Theorem t_jgmt_to_f_jgmt:
 !TS l ls pre post.
 first_enc TS ==>
 t_jgmt TS l ls pre post ==>
 f_jgmt TS l ls pre post
Proof
rpt strip_tac >>
gs[t_jgmt_def, f_jgmt_def] >>
rpt strip_tac >>
res_tac >>
gs[first_enc_def] >>
qexistsl_tac [`n`, `s'`] >>
gs[]
QED

val _ = export_theory();
