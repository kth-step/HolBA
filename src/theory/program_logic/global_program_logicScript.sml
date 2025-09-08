(*
  Program logic asserting postconditions upon every encounter of the ending label set.
*)
open HolKernel boolLib bossLib BasicProvers dep_rewrite prim_recTheory;

open holba_auxiliaryLib;

open holba_auxiliaryTheory;

open transition_systemTheory total_program_logicTheory partial_program_logicTheory;

val _ = new_theory "global_program_logic";

(* Partial-correctness global-encounter judgment *)
(* TODO: Currently, "weak" is lumped in with the transition system,
 * so a separate transition system could be used for global-encounter
 * with another notion of weak characterised by a global_enc_def,
 * using "weak" as execution in contract, and global_enc TS among premises *)
Definition pg_jgmt_def:
 pg_jgmt TS (l:'b) (ls:'b->bool) pre post =
 !s.
  TS.ctrl s = l ==>
  pre s ==>
  !n s'.
   (n > 0 /\
    FUNPOW_OPT TS.trs n s = SOME s' /\
    TS.ctrl s' IN ls
   ) ==>
  post s'
End

Definition tg_jgmt_def:
 tg_jgmt TS (l:'b) (ls:'b->bool) pre post =
 !s.
  TS.ctrl s = l ==>
  pre s ==>
  (!n s'.
   (n > 0 /\
    FUNPOW_OPT TS.trs n s = SOME s' /\
    TS.ctrl s' IN ls
   ) ==>
  post s') /\
  ?n s'.
   (n > 0 /\
    FUNPOW_OPT TS.trs n s = SOME s' /\
    TS.ctrl s' IN ls
   )
End

Theorem partial_global_to_partial:
 !TS l ls pre post.
 first_enc TS ==>
 pg_jgmt TS l ls pre post ==>
 p_jgmt TS l ls pre post
Proof
rpt strip_tac >>
gs[p_jgmt_def, pg_jgmt_def, normal_def] >>
rpt strip_tac >>
`!n s'.
 n > 0 /\ FUNPOW_OPT TS.trs n s = SOME s' /\ TS.ctrl s' IN ls ==>
 post s'` by metis_tac[] >>
gs[first_enc_def] >>
QSPECL_ASSUM ``!(n:num) s'. _`` [`n`, `s'`] >>
gs[]
QED

(*
Theorem partial_global_equiv_partial:
 !TS l ls pre post.
 first_enc TS ==>
 (pg_jgmt TS l ls pre post <=>
  p_jgmt TS l ls pre post /\
  (!l'. l' IN ls ==>
    ~(p_jgmt TS l {l'} pre (\s. F)) ==>
    p_jgmt TS l' ls post post))
Proof
rpt strip_tac >>
eq_tac >- (
 rpt strip_tac >- (
  metis_tac[partial_global_to_partial]
 ) >>
 cheat
) >>
rpt strip_tac >>
cheat
QED

Theorem total_global_to_total:
 !TS l ls pre post.
 first_enc TS ==>
 normal TS l ls pre ==>
 tg_jgmt TS l ls pre post <=>
 t_jgmt TS l ls pre post
Proof
cheat
QED

Theorem total_global_equiv_total:
 !TS l ls pre post.
 first_enc TS ==>
 tg_jgmt TS l ls pre post <=>
 (t_jgmt TS l ls pre post /\
  !l'. l' IN ls ==>
   p_jgmt TS l' ls post post)
Proof
cheat
QED
*)

val _ = export_theory();
