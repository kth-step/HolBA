open HolKernel Parse boolLib bossLib;

(* This theory contains the definition of the modified m0 step
   (, where clock cycles are counted with word64 instead if num). *)

val _ = new_theory "m0_mod_step";


val _ = Datatype `m0_mod_state = <|
  base   : m0_state;
  countw : word64
|>`;

(*
m0_mod_eq s sm = if s.count < 2^64 then s = sm.base andalso sm.countw = n2w s.count else false;

 (s.count < 2^64) ==> m0_mod_eq s <| base := s; countw := n2w s.count |>
~(s.count < 2^64) ==> ~(m0_mod_eq s sm)
*)


(* Definitions *)
val m0_mod_def = Define `
  m0_mod s = if s.count < (2 ** 64) then SOME (<| base := s; countw := n2w s.count |>) else NONE
`;

val m0_mod_inv_def = Define `
  m0_mod_inv sm = sm.base with <| count := w2n sm.countw |>
`;

val NextStateM0_mod_def = Define `
                     NextStateM0_mod sm = case NextStateM0 (m0_mod_inv sm) of
                       | NONE    => NONE
                       | SOME s' => m0_mod s'
`;


(* mod step theorem gen *)
val m0_mod_step_thm = store_thm("m0_mod_step_thm", ``
  !s s' (d:word64) sm.
    (s = m0_mod_inv sm) ==>
    (NextStateM0 s = SOME s') ==>
    (s'.count = s.count + (w2n d)) ==>
    ((w2n d) < (2 ** 64)) ==>

    (sm.countw <+ (n2w ((2 ** 64) - 1)) - d) ==>
    (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + d |>))
``,
  cheat
);

val m0_mod_step_gen_thm = store_thm("m0_mod_step_gen_thm", ``
  !s' (d:word64) sm.
    (NextStateM0 (m0_mod_inv sm) = SOME s') ==>
    (s'.count = (m0_mod_inv sm).count + (w2n d)) ==>
    ((w2n d) < (2 ** 64)) ==>

    (sm.countw <+ (n2w ((2 ** 64) - 1)) - d) ==>
    (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + d |>))
``,
  SIMP_TAC std_ss [m0_mod_step_thm]
);






val _ = export_theory();
