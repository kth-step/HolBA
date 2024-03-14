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

val birenvtyl_def = bir_program_transfTheory.birenvtyl_def;

val bmemms_t = List.nth((snd o strip_comb o concl) bin_small_exampleTheory.bin_small_example_thm, 2);
Definition bmemms_def:
  bmemms = ^(bmemms_t)
End

val bprog_def = exampleTheory.bprog_def;
val bprog_tm = (fst o dest_eq o concl) bprog_def;

val bin_small_example_thm = REWRITE_RULE [GSYM bmemms_def, GSYM bprog_def] bin_small_exampleTheory.bin_small_example_thm;



val (sys_tm, L_tm, Pi_tm) = (birs_stepLib.symb_sound_struct_get_sysLPi_fun o concl) exampleTheory.bin_small_example_analysis_thm;
val bir_frag_l_tm = (birs_driveLib.birs_get_pc o snd o dest_comb) sys_tm;
val bir_frag_l_ml_tm = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl o EVAL) ``(^bir_frag_l_tm).bpc_label``;

Definition bir_frag_l_def:
  bir_frag_l = ^bir_frag_l_tm
End

Definition bir_frag_L_def:
  bir_frag_L = ^L_tm
End
val bir_frag_l_exit_ml_tm = ``2828w:word32``;
val bir_frag_l_exit_tm = ``<|bpc_label := BL_Address (Imm32 ^bir_frag_l_exit_ml_tm); bpc_index := 0|>``;

Definition bprecond_def:
  bprecond = BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
End

Definition pre_bir_def:
  pre_bir bs =
       (bir_eval_exp bprecond bs.bst_environ = SOME bir_val_true)
End

Definition post_bir_def:
  post_bir bs1 bs2 =
      (?v1 v2. bir_env_lookup "R7" bs1.bst_environ = SOME (BVal_Imm (Imm32 v1)) /\
               bir_env_lookup "R3" bs2.bst_environ = SOME (BVal_Imm (Imm32 v2)) /\
               (v2 = v1 + 15w))
End

Definition pre_bir_nL_def:
  pre_bir_nL st =
      (
       st.bst_status = BST_Running /\
       st.bst_pc.bpc_index = 0 /\
       bir_envty_list_b birenvtyl st.bst_environ /\

       pre_bir st
      )
End
Definition post_bir_nL_def:
  post_bir_nL (st:bir_state_t) st' =
      (
         (st'.bst_pc = ^bir_frag_l_exit_tm) /\
         st'.bst_status = BST_Running /\

         post_bir st st'
      )
End

Theorem bir_step_n_in_L_jgmt_example_thm[local]:
  bir_step_n_in_L_jgmt
  ^bprog_tm
  bir_frag_l
  bir_frag_L
  pre_bir_nL
  post_bir_nL
Proof
cheat
QED

Theorem bir_frag_L_INTER_thm[local]:
  bir_frag_L INTER {^bir_frag_l_exit_tm} = EMPTY
Proof
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
QED

Theorem bir_abstract_jgmt_rel_example_thm[local]:
  abstract_jgmt_rel
  (bir_ts ^bprog_tm)
  (BL_Address (Imm32 ^bir_frag_l_ml_tm))
  {BL_Address (Imm32 ^bir_frag_l_exit_ml_tm)}
  pre_bir_nL
  post_bir_nL
Proof
ASSUME_TAC
    (Q.SPEC `{BL_Address (Imm32 ^bir_frag_l_exit_ml_tm)}`
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
QED



Theorem bmr_rel_m0_mod_bmr_IMP_index_thm[local]:
  !ms bs.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bs.bst_status = BST_Running) ==>
  (bs.bst_pc.bpc_index = 0)
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "countw" bs.bst_environ = SOME (BVal_Imm (Imm64 ms.countw)))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_SP_process_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "SP_process" bs.bst_environ = SOME (BVal_Imm (Imm32 (ms.base.REG RName_SP_process))))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_R3_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "R3" bs.bst_environ = SOME (BVal_Imm (Imm32 (ms.base.REG RName_3))))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED

Theorem bmr_rel_m0_mod_bmr_IMP_R7_lookup_thm[local]:
  !bs ms.
  (bmr_rel (m0_mod_bmr (F,T)) bs ms) ==>
  (bir_env_lookup "R7" bs.bst_environ = SOME (BVal_Imm (Imm32 (ms.base.REG RName_7))))
Proof
EVAL_TAC >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >> (
    METIS_TAC []
  )
QED



Definition pre_m0_mod_def:
  pre_m0_mod ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms) bmemms) /\
        ((m0_mod_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.base.REG RName_SP_process /\
         ms.base.REG RName_SP_process && 0x3w = 0w /\
         ms.countw <=+ 0xFFFFFFFFFFFFFF00w)
      )
End
Definition post_m0_mod_def:
  post_m0_mod ms ms' =
      (
        (ms'.base.REG RName_3 = ms.base.REG RName_7 + 15w)
      )
End

Theorem backlift_bir_m0_mod_pre_abstr_ex_thm[local]:
  backlift_bir_m0_mod_pre_abstr pre_m0_mod pre_bir_nL
Proof
FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_pre_abstr_def, pre_m0_mod_def, pre_bir_nL_def, pre_bir_def] >>
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>

  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_index_thm >>
  FULL_SIMP_TAC std_ss [] >>

  REWRITE_TAC [bprecond_def] >>
  EVAL_TAC >>

  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_countw_lookup_thm >>
  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_SP_process_lookup_thm >>
  ASM_REWRITE_TAC [] >>
  EVAL_TAC >>
  ASM_REWRITE_TAC [] >>
  EVAL_TAC
QED

Theorem backlift_bir_m0_mod_post_concr_ex_thm[local]:
  backlift_bir_m0_mod_post_concr post_bir_nL post_m0_mod
Proof
FULL_SIMP_TAC std_ss [backlift_bir_m0_mod_post_concr_def, post_bir_nL_def, post_m0_mod_def, post_bir_def] >>
  REPEAT STRIP_TAC >>

  `v1 = ms.base.REG RName_7` by (
    IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_R7_lookup_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  IMP_RES_TAC bmr_rel_m0_mod_bmr_IMP_R3_lookup_thm >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED


Theorem m0_mod_thm[local]:
  abstract_jgmt_rel
  m0_mod_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  (pre_m0_mod)
  (post_m0_mod)
Proof
ASSUME_TAC
    (Q.SPECL
      [`pre_m0_mod`, `pre_bir_nL`, `post_bir_nL`, `post_m0_mod`, `(^bir_frag_l_ml_tm)`, `{^bir_frag_l_exit_ml_tm}`]
      (MATCH_MP
        bir_program_transfTheory.backlift_bir_m0_mod_contract_thm
        (bin_small_example_thm))) >>

  `!ms. pre_m0_mod ms ==>
           EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms) bmemms` by (
    FULL_SIMP_TAC std_ss [pre_m0_mod_def]
  ) >>

  `!ms. pre_m0_mod ms ==> (m0_mod_bmr (F,T)).bmr_extra ms` by (
    FULL_SIMP_TAC std_ss [pre_m0_mod_def]
  ) >>

  `!bs.    pre_bir_nL bs ==>
           ~bir_state_is_terminated bs` by (
    FULL_SIMP_TAC std_ss [pre_bir_nL_def, bir_programTheory.bir_state_is_terminated_def]
  ) >>

  `MEM (BL_Address (Imm32 ^bir_frag_l_ml_tm)) (bir_labels_of_program (bprog:'observation_type bir_program_t))` by (
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `!bs bs'. post_bir_nL bs bs' ==> ~bir_state_is_terminated bs'` by (
    FULL_SIMP_TAC std_ss [post_bir_nL_def, bir_programTheory.bir_state_is_terminated_def]
  ) >>

  ASSUME_TAC backlift_bir_m0_mod_pre_abstr_ex_thm >>
  ASSUME_TAC backlift_bir_m0_mod_post_concr_ex_thm >>

  FULL_SIMP_TAC std_ss [IMAGE_SING, IN_SING] >>
  FULL_SIMP_TAC std_ss [bir_abstract_jgmt_rel_example_thm] >>
  METIS_TAC []
QED


Theorem m0_mod_R_IMP_bmr_ms_mem_contains_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (bmr_ms_mem_contains (m0_mod_bmr (F,T)) mms =
   bmr_ms_mem_contains (m0_bmr (F,T)) ms)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  MATCH_MP_TAC boolTheory.EQ_EXT >>
  Cases_on `x` >>

  `(mms.base with count := w2n mms.countw).MEM = mms.base.MEM` by (
    SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
  ) >>

  Q.SPEC_TAC (`q`, `b`) >>
  Q.SPEC_TAC (`r`, `l`) >>

  Induct_on `l` >- (
    GEN_TAC >>
    EVAL_TAC
  ) >>

  REWRITE_TAC [bir_lifting_machinesTheory.bmr_ms_mem_contains_def] >>
  REPEAT STRIP_TAC >>
  POP_ASSUM (fn thm => SIMP_TAC std_ss [thm]) >>

  SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_mem_lf_def] >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.m0_mod_lifted_mem_def, bir_lifting_machinesTheory.m0_lifted_mem_def] >>
  CASE_TAC >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.bir_machine_lifted_mem_t_11] >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED
Theorem m0_mod_R_IMP_REG_EQ_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (mms.base.REG = ms.REG)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED
Theorem m0_mod_R_IMP_bmr_extra_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  ((m0_mod_bmr (F,T)).bmr_extra mms = (m0_bmr (F,T)).bmr_extra ms)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss++(rewrites (type_rws ``:('a,'b,'c) bir_lifting_machine_rec_t``))) [bir_lifting_machinesTheory.m0_mod_bmr_def, bir_lifting_machinesTheory.m0_bmr_def] >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_lifting_machinesTheory.m0_mod_state_is_OK_def, bir_lifting_machinesTheory.m0_state_is_OK_def] >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED

Definition pre_m0_def:
  pre_m0 ms =
      (
        (EVERY (bmr_ms_mem_contains (m0_bmr (F,T)) ms) bmemms) /\
        ((m0_bmr (F,T)).bmr_extra ms) /\

        (0xFFFFFFw <=+ ms.REG RName_SP_process /\
         ms.REG RName_SP_process && 0x3w = 0w /\
         ms.count <= 0xFFFFFFFFFFFFFF00:num)
      )
End
Definition post_m0_def:
  post_m0 ms ms' =
      (
        (ms'.REG RName_3 = ms.REG RName_7 + 15w)
      )
End

Theorem m0_mod_R_IMP_count_EQ_countw_thm[local]:
  !mms ms.
  (m0_mod_R ms mms) ==>
  (ms.count = w2n mms.countw)
Proof
REWRITE_TAC [m0_mod_R_def, m0_mod_stepTheory.m0_mod_inv_def] >>
  REPEAT STRIP_TAC >>

  ASM_SIMP_TAC (std_ss++(rewrites (type_rws ``:m0_state``))) []
QED

Theorem backlift_m0_mod_m0_pre_abstr_ex_thm[local]:
  backlift_m0_mod_m0_pre_abstr (pre_m0) (pre_m0_mod)
Proof
FULL_SIMP_TAC std_ss [pre_m0_def, pre_m0_mod_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>

  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC std_ss [] >>

  `(EVERY (bmr_ms_mem_contains (m0_mod_bmr (F,T)) mms) bmemms) /\
        ((m0_mod_bmr (F,T)).bmr_extra mms)` by (
    METIS_TAC [m0_mod_R_IMP_bmr_ms_mem_contains_thm, m0_mod_R_IMP_bmr_extra_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  `0xFFFFFFw <=+ mms.base.REG RName_SP_process /\
   mms.base.REG RName_SP_process && 0x3w = 0w` by (
    METIS_TAC [m0_mod_R_IMP_REG_EQ_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

(*
         ms.count <= 0xFFFFFFFFFFFFFF00:num ==>
         ms.countw <=+ 0xFFFFFFFFFFFFFF00w
*)
  REWRITE_TAC [wordsTheory.WORD_LS] >>

  IMP_RES_TAC m0_mod_R_IMP_count_EQ_countw_thm >>
  POP_ASSUM (fn thm => REWRITE_TAC [GSYM thm]) >>
  EVAL_TAC >>
  ASM_REWRITE_TAC []
QED

Theorem backlift_m0_mod_m0_post_concr_ex_thm[local]:
  backlift_m0_mod_m0_post_concr post_m0_mod post_m0
Proof
FULL_SIMP_TAC std_ss [post_m0_mod_def, post_m0_def, backlift_m0_mod_m0_pre_abstr_def, backlift_m0_mod_m0_post_concr_def] >>
  METIS_TAC [m0_mod_R_IMP_bmr_ms_mem_contains_thm, m0_mod_R_IMP_bmr_extra_thm, m0_mod_R_IMP_REG_EQ_thm]
QED

Theorem m0_thm:
  abstract_jgmt_rel
  m0_weak_model
  (^bir_frag_l_ml_tm)
  {^bir_frag_l_exit_ml_tm}
  (pre_m0)
  (post_m0)
Proof
ASSUME_TAC
    (Q.SPECL
      [`pre_m0`, `pre_m0_mod`, `post_m0_mod`, `post_m0`, `(^bir_frag_l_ml_tm)`, `{^bir_frag_l_exit_ml_tm}`]
      bir_program_transfTheory.backlift_m0_mod_m0_contract_thm) >>

  `!ms. pre_m0 ms ==> (\ms. ms.count < 2 ** 64) ms` by (
    FULL_SIMP_TAC std_ss [pre_m0_def] >>
    REPEAT STRIP_TAC >>

(*
    IMP_RES_TAC arithmeticTheory.LESS_EQ_IMP_LESS_SUC >>
    POP_ASSUM (ASSUME_TAC o CONV_RULE EVAL) >>
*)
    IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS >>
    POP_ASSUM MATCH_MP_TAC >>
    EVAL_TAC
  ) >>

  ASSUME_TAC backlift_m0_mod_m0_pre_abstr_ex_thm >>
  ASSUME_TAC backlift_m0_mod_m0_post_concr_ex_thm >>

  FULL_SIMP_TAC std_ss [m0_mod_thm]
QED


val _ = export_theory();

