open HolKernel Parse boolLib bossLib;
open bslSyntax;
open tutorial_bir_to_armSupportTheory;

open bir_program_multistep_propsTheory;
open bir_envTheory;
open bir_program_env_orderTheory;

val _ = new_theory "tutorial_compositionSupport";

val comp_seq_thm = store_thm("comp_seq_thm",
  ``!l l1 ls prog P R Q.
    bir_triple prog l (\x.x=l1) P R ==>
    bir_triple prog l1 ls (R l1) Q ==>
    bir_triple prog l ls P Q``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_triple_def] >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``bir_triple prog l (\x. x = l1) P R'``
            (fn thm =>
               ASSUME_TAC (Q.SPEC `s`
                 (SIMP_RULE std_ss [bir_triple_def] thm)
               )
            ) >>
REV_FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``bir_triple prog l1 ls (R' l1) Q``
            (fn thm =>
               ASSUME_TAC (Q.SPEC `s'`
                 (SIMP_RULE std_ss [bir_triple_def] thm)
               )
            ) >>
subgoal `bir_env_vars_are_initialised s'.bst_environ
           (bir_vars_of_program prog)` >- (
METIS_TAC [bir_exec_block_n_ENV_ORDER,
           bir_env_oldTheory.bir_env_vars_are_initialised_ORDER]
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>

Q.SUBGOAL_THEN `s'.bst_pc.bpc_label IN (\x. x = l1) ==>
                (s'.bst_pc.bpc_label = l1)` 
  (fn thm => IMP_RES_TAC thm) >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
FULL_SIMP_TAC std_ss [] >>
REV_FULL_SIMP_TAC std_ss [] >>
quantHeuristicsLib.QUANT_TAC [("n", `n+n'`, []),
			      ("l1", `l1' ++ l1''`, []),
			      ("c1", `c1 + c1'`, []),
			      ("c2", `c2 + c2'`, []),
			      ("s'", `s''`, [])] >>
FULL_SIMP_TAC std_ss [] >>
subgoal `bir_exec_block_n prog s (n + n') =
         (l1' ++ l1'',c1 + c1',c2 + c2',s'')` >- (
FULL_SIMP_TAC std_ss [bir_exec_block_n_combine]
)
);


val comp_loop_thm = store_thm("comp_loop_thm", 
``! l l1 ls prog invariant condition postcondition variant free_var.
(bir_triple prog l1 (\x.x=l)
  (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ]))
  (* TODO: ??? *)
  (\l. (^(bandl[``invariant:bir_exp_t``,
           bnot(bsle(``BExp_Const (Imm64 free_var)``, ``variant:bir_exp_t``)),
           bsle(bconst64 0, ``variant:bir_exp_t``)
           ]))))
==>
(bir_triple prog l (\x.x=l1)
  (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ]))
  (* TODO: ??? *)
  (\l1. (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ]))))
==>
(bir_triple prog l ls (^(band(``invariant:bir_exp_t``, bnot ``condition:bir_exp_t``))) postcondition) ==>
(bir_triple prog l ls invariant postcondition)
``, cheat
);



val _ = export_theory();
