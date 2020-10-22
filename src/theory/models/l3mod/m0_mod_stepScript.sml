open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open wordsTheory;
open combinTheory;

(* This theory contains the definition of the modified m0 step
   (, where clock cycles are counted with word64 instead if num). *)

val _ = new_theory "m0_mod_step";


(* modified state with word representation of clock cycle counter *)
val _ = Datatype `m0_mod_state = <|
  base   : m0_state;
  countw : word64
|>`;


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

(* helper rewrite sets and theorems *)
val m0_state_type_ss = rewrites (type_rws ``:m0_state``);
val m0_mod_state_type_ss = rewrites (type_rws ``:m0_mod_state``);

val max_int_thm = REWRITE_RULE [EVAL ``UINT_MAXw:word64``]
			       (INST_TYPE [alpha |-> ``:64``] WORD_LS_T);
val w2n_min_thm = MP (SPECL [``0xFFFFFFFFFFFFFFFFw:word64``, ``d:word64``]
			    (INST_TYPE [alpha |-> ``:64``] word_sub_w2n))
		     (SPEC ``d:word64`` max_int_thm);
val num_repr_max_thm = (TRANS (EVAL ``w2n (0xFFFFFFFFFFFFFFFFw:word64)``)
			      (GSYM (EVAL ``(2 ** 64) - (1:num)``)));

(* mod step theorem gen *)
val m0_mod_step_thm = store_thm("m0_mod_step_thm", ``
  !s s' (d:word64) sm.
    (s = m0_mod_inv sm) ==>
    (NextStateM0 s = SOME s') ==>
    (s'.count = s.count + (w2n d)) ==>

    (sm.countw <=+ (n2w ((2 ** 64) - 1)) - d) ==>
    (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + d |>))
``,

  REPEAT GEN_TAC >> STRIP_TAC >>

  ASM_REWRITE_TAC [] >>
  POP_ASSUM (K ALL_TAC) >>

  REPEAT STRIP_TAC >>
  REWRITE_TAC [NextStateM0_mod_def] >>

  CASE_TAC >> FULL_SIMP_TAC (std_ss) [] >>
  POP_ASSUM (K ALL_TAC) >>

  REWRITE_TAC [m0_mod_def] >>

  `s'.count < 2 ** 64` by (
    POP_ASSUM (K ALL_TAC) >>
    FULL_SIMP_TAC (pure_ss++m0_state_type_ss) [m0_mod_inv_def, K_THM] >>
    POP_ASSUM (fn t => POP_ASSUM (K (ASSUME_TAC t))) >>

    FULL_SIMP_TAC pure_ss [WORD_LS, LE_LT1] >>

    FULL_SIMP_TAC pure_ss [w2n_min_thm, num_repr_max_thm] >>

    `2 ** 64 − 1 >= w2n d` by (
      POP_ASSUM (K ALL_TAC) >>
      METIS_TAC [max_int_thm, num_repr_max_thm, WORD_HS, WORD_HIGHER_EQ]
    ) >>

    Cases_on `2 ** 64 − 1 = w2n d` >> (
      FULL_SIMP_TAC arith_ss [SUB_RIGHT_ADD]
    )
  ) >>

  ASM_REWRITE_TAC [] >>
  POP_ASSUM (K ALL_TAC) >>

  SIMP_TAC (std_ss++m0_state_type_ss++m0_mod_state_type_ss)
           [m0_mod_inv_def, word_add_def]
);

(* simplified theorem for use by the step function *)
val m0_mod_step_gen_thm = store_thm("m0_mod_step_gen_thm", ``
  !s' (d:word64) sm.
    (NextStateM0 (m0_mod_inv sm) = SOME s') ==>
    (s'.count = (m0_mod_inv sm).count + (w2n d)) ==>

    (sm.countw <=+ (n2w ((2 ** 64) - 1)) - d) ==>
    (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + d |>))
``,
  SIMP_TAC std_ss [m0_mod_step_thm]
);

(* simplified relaxed theorem for use by the step function *)
val m0_mod_step_gen_relaxed_thm = store_thm("m0_mod_step_gen_relaxed_thm", ``
  !s' (d:word64) (dmax:word64) sm.
    (NextStateM0 (m0_mod_inv sm) = SOME s') ==>
    (d <=+ dmax) ==>
    (s'.count = (m0_mod_inv sm).count + (w2n d)) ==>

    (sm.countw <=+ (n2w ((2 ** 64) - 1)) - dmax) ==>
    (NextStateM0_mod sm = SOME (<| base := s'; countw := sm.countw + d |>))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC (Q.SPECL [`s'`, `d`, `sm`] m0_mod_step_gen_thm) >>

  `sm.countw <=+ n2w (2 ** 64 − 1) − d` by (
    POP_ASSUM (K ALL_TAC) >>
    POP_ASSUM (fn t => POP_ASSUM (K (ASSUME_TAC t))) >>
    POP_ASSUM (fn t => POP_ASSUM (fn t2 => POP_ASSUM (K (ASSUME_TAC t >> ASSUME_TAC t2)))) >>

    FULL_SIMP_TAC std_ss [WORD_LS, w2n_min_thm] >>

    `w2n (0xFFFFFFFFFFFFFFFFw:word64) − w2n dmax <= w2n (0xFFFFFFFFFFFFFFFFw:word64) − w2n d` by (
      POP_ASSUM (fn t => POP_ASSUM (K (ASSUME_TAC t))) >>
      ASM_SIMP_TAC std_ss [LE_SUB_LCANCEL]
    ) >>

    METIS_TAC [LESS_EQ_TRANS]
  ) >>

  ASM_SIMP_TAC std_ss []
);


val _ = export_theory();
