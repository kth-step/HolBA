open HolKernel Parse boolLib bossLib;

open bir_symbTheory;

open birs_stepLib;
open birs_composeLib;

open birs_auxTheory;

  open birs_stepLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open birs_composeLib;
open birs_auxTheory;

open bir_program_transfTheory;


val _ = new_theory "bir_program_transf_example";

val birenvtyl_def = motorfuncTheory.birenvtyl_def;


val bir_frag_l_def = Define `
    bir_frag_l = <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>
`;
val bir_frag_L_def = Define `
    bir_frag_L =
     {<|bpc_label := BL_Address (Imm32 2850w); bpc_index := 2|>;
      <|bpc_label := BL_Address (Imm32 2850w); bpc_index := 1|>;
      <|bpc_label := BL_Address (Imm32 2850w); bpc_index := 0|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 6|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 5|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 4|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 3|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 2|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 1|>;
      <|bpc_label := BL_Address (Imm32 2848w); bpc_index := 0|>;
      <|bpc_label := BL_Address (Imm32 2846w); bpc_index := 3|>;
      <|bpc_label := BL_Address (Imm32 2846w); bpc_index := 2|>;
      <|bpc_label := BL_Address (Imm32 2846w); bpc_index := 1|>;
      <|bpc_label := BL_Address (Imm32 2846w); bpc_index := 0|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 7|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 6|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 5|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 4|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 3|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 2|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 1|>;
      <|bpc_label := BL_Address (Imm32 2844w); bpc_index := 0|>;
      <|bpc_label := BL_Address (Imm32 2842w); bpc_index := 4|>;
      <|bpc_label := BL_Address (Imm32 2842w); bpc_index := 3|>;
      <|bpc_label := BL_Address (Imm32 2842w); bpc_index := 2|>;
      <|bpc_label := BL_Address (Imm32 2842w); bpc_index := 1|>;
      <|bpc_label := BL_Address (Imm32 2842w); bpc_index := 0|>;
      <|bpc_label := BL_Address (Imm32 2840w); bpc_index := 7|>;
      <|bpc_label := BL_Address (Imm32 2840w); bpc_index := 6|>}
`;
val pre_bir_nL_def = Define `
    pre_bir_nL st =
      (
       st.bst_status = BST_Running /\

       (* TODO: this was added *)
       st.bst_pc.bpc_index = 0 /\

       bir_envty_list_b birenvtyl st.bst_environ /\
       bir_eval_exp (BExp_Den (BVar "SP_process" (BType_Imm Bit32))) st.bst_environ = SOME (BVal_Imm (Imm32 0x10w))
      )
`;
val post_bir_nL_def = Define `
    post_bir_nL st st' =
      (
         (st'.bst_pc = <|bpc_label := BL_Address (Imm32 2886w); bpc_index := 0|>) /\

         (* TODO: this was added *)
         st'.bst_status = BST_Running /\

         bir_eval_exp (BExp_Den (BVar "SP_process" (BType_Imm Bit32))) st'.bst_environ = SOME (BVal_Imm (Imm32 0x11w))
      )
`;

val bir_step_n_in_L_jgmt_example_thm = prove(``
bir_step_n_in_L_jgmt
  bprog
  bir_frag_l
  bir_frag_L
  pre_bir_nL
  post_bir_nL
``,
  cheat
);

val bir_frag_L_INTER_thm = prove(``
bir_frag_L INTER {<|bpc_label := BL_Address (Imm32 2886w); bpc_index := 0|>} = EMPTY
``,
  `!A B. A INTER {B} = (EMPTY:bir_programcounter_t -> bool) <=> B NOTIN A` by (
    REPEAT STRIP_TAC >>
    EQ_TAC >> (
      FULL_SIMP_TAC std_ss [bir_auxiliaryTheory.SING_DISJOINT_SING_NOT_IN_thm]
    ) >>
    REPEAT STRIP_TAC >>

    REWRITE_TAC [Once (GSYM INTER_COMM)] >>
    FULL_SIMP_TAC std_ss [INTER_EMPTY, INSERT_INTER]
  ) >>
  POP_ASSUM (fn thm => ASM_REWRITE_TAC [thm]) >>

  EVAL_TAC
);

val bir_abstract_jgmt_rel_example_thm = prove(``
abstract_jgmt_rel
  (bir_etl_wm bprog)
  (BL_Address (Imm32 2824w))
  {BL_Address (Imm32 2886w)}
  pre_bir_nL
  post_bir_nL
``,
  ASSUME_TAC
    (Q.SPEC `{BL_Address (Imm32 2886w)}`
      (MATCH_MP
        (REWRITE_RULE
           [bir_programTheory.bir_block_pc_def]
           bir_step_n_in_L_jgmt_TO_abstract_jgmt_rel_thm)
        (REWRITE_RULE
           [bir_frag_l_def]
           bir_step_n_in_L_jgmt_example_thm))) >>

  FULL_SIMP_TAC std_ss [pre_bir_nL_def] >>

  FULL_SIMP_TAC std_ss [IMAGE_SING, IN_SING, bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_frag_L_INTER_thm] >>

  FULL_SIMP_TAC std_ss [post_bir_nL_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [abstract_jgmt_rel_def]
);

val pre_m0_mod_def = Define `
    pre_m0_mod memms ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_mod_bmr (T,T)) ms) memms) /\
        ((m0_mod_bmr (T,T)).bmr_extra ms) /\

        (ms.base.REG RName_SP_process = 0x10w)
      )
`;
val post_m0_mod_def = Define `
    post_m0_mod ms ms' =
      (
        (ms'.base.REG RName_SP_process = 0x11w)
      )
`;

val m0_mod_thm = prove(``
abstract_jgmt_rel
  m0_mod_weak_model
  (2824w)
  {2886w}
  (pre_m0_mod memms)
  (post_m0_mod)
``,

  cheat
(*
bir_program_transfTheory.backlift_bir_m0_mod_contract_thm
*)
);


val m0_mod_R_IMP_bmr_ms_mem_contains_thm = prove(``
!mms ms memms.
  (m0_mod_R ms mms) ==>
  ((EVERY (bmr_ms_mem_contains (m0_mod_bmr (T,T)) mms) memms) =
   (EVERY (bmr_ms_mem_contains (m0_bmr (T,T)) ms) memms))
``,
  cheat
);
val m0_mod_R_IMP_REG_EQ_thm = prove(``
!mms ms regn.
  (m0_mod_R ms mms) ==>
  (mms.base.REG regn = ms.REG regn)
``,
  cheat
);
val m0_mod_R_IMP_bmr_extra_thm = prove(``
!mms ms.
  (m0_mod_R ms mms) ==>
  ((m0_mod_bmr (T,T)).bmr_extra mms = (m0_bmr (T,T)).bmr_extra ms)
``,
  cheat
);

val pre_m0_def = Define `
    pre_m0 memms ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_bmr (T,T)) ms) memms) /\
        ((m0_bmr (T,T)).bmr_extra ms) /\

        (ms.count < 2 ** 64) /\

        (ms.REG RName_SP_process = 0x10w)
      )
`;
val post_m0_def = Define `
    post_m0 ms ms' =
      (
        (ms'.REG RName_SP_process = 0x11w)
      )
`;

val m0_thm = prove(``
abstract_jgmt_rel
  m0_weak_model
  (2824w)
  {2886w}
  (pre_m0 memms)
  (post_m0)
``,

  ASSUME_TAC
    (Q.SPECL
      [`pre_m0 memms`, `pre_m0_mod memms`, `post_m0_mod`, `post_m0`, `(2824w)`, `{2886w}`]
      bir_program_transfTheory.backlift_m0_mod_m0_contract_thm) >>

  `!ms. pre_m0 memms ms ⇒ (\ms. ms.count < 2 ** 64) ms` by (
    FULL_SIMP_TAC std_ss [pre_m0_def]
  ) >>

  `backlift_m0_mod_m0_pre_abstr (pre_m0 memms) (pre_m0_mod memms)` by (
    FULL_SIMP_TAC std_ss [pre_m0_def, pre_m0_mod_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>
    METIS_TAC [m0_mod_R_IMP_bmr_ms_mem_contains_thm, m0_mod_R_IMP_bmr_extra_thm, m0_mod_R_IMP_REG_EQ_thm]
  ) >>

  `backlift_m0_mod_m0_post_concr post_m0_mod post_m0` by (
    FULL_SIMP_TAC std_ss [post_m0_mod_def, post_m0_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>
    METIS_TAC [m0_mod_R_IMP_bmr_ms_mem_contains_thm, m0_mod_R_IMP_bmr_extra_thm, m0_mod_R_IMP_REG_EQ_thm]
  ) >>

  FULL_SIMP_TAC std_ss [m0_mod_thm]
);


val _ = export_theory();

