open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "spinlock";

val _ = lift_da_and_store_mc_riscv
          "spinlock"
          "spinlock.da"
          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

open bir_promisingTheory;

Definition is_fulfil_def:
  is_fulfil cid t system1 system2 =
  ?st st' p p'.
    Core cid p st IN system1
    /\ Core cid p' st' IN system2
    /\ FILTER (λt'. t' <> t) st.bst_prom = st'.bst_prom
    /\ MEM t st.bst_prom
End

Definition is_promise_def:
  is_promise cid t M M' system1 system2 =
  ?st st' p p' v l.
    Core cid p st IN system1
    /\ Core cid p' st' IN system2
    /\ t = LENGTH M + 1
    /\ M' = M ++ [<| loc := l; val := v; cid := cid  |>]
    /\ st'.bst_prom = st.bst_prom ++ [t]
End

Definition parstep_nice_def:
  parstep_nice (sys1, M1) (sys2, M2) = parstep sys1 M1 sys2 M2
End

(* set of all traces using bir_multicore$gen_traces *)
Definition par_traces_def:
  par_traces = gen_traces parstep_nice
End

Theorem par_trace_promise_preceeds_fulfil:
  !i tr cid t.
  tr IN par_traces
  /\ SUC i < LENGTH tr
  /\ is_fulfil cid t (FST $ EL i tr) (FST $ EL (SUC i) tr)
  ==> ?j. j < i
    /\ is_promise cid t (SND $ EL j tr) (SND $ EL (SUC j) tr)
      (FST $ EL j tr) (FST $ EL (SUC j) tr)
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> `?p st. Core cid p st IN FST $ EL i tr  /\ MEM t st.bst_prom` by (
    fs[is_fulfil_def] >> metis_tac[]
  )
  >> fs[DISJ_EQ_IMP]
  >> cheat
QED

val _ = export_theory();
