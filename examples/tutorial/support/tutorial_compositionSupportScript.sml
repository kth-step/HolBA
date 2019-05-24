open HolKernel Parse boolLib bossLib;
open bslSyntax;
open tutorial_bir_to_armSupportTheory;

val _ = new_theory "tutorial_compositionSupport";

val comp_seq_thm = store_thm("comp_seq_thm", ``
! l l1 ls prog P R Q.
(bir_triple prog l (\x.x=l1) P R) ==>
(bir_triple prog l1 ls R Q) ==>
(bir_triple prog l ls P Q)
``, cheat
);


val comp_loop_thm = store_thm("comp_loop_thm", 
``! l l1 ls prog invariant condition postcondition variant free_var.
(bir_triple prog l1 (\x.x=l)
  (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ]))
  (^(bandl[``invariant:bir_exp_t``,
           bnot(bsle(``BExp_Const (Imm64 free_var)``, ``variant:bir_exp_t``)),
           bsle(bconst64 0, ``variant:bir_exp_t``)
           ])))
==>
(bir_triple prog l (\x.x=l1)
  (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ]))
  (^(bandl[``invariant:bir_exp_t``,
           ``condition:bir_exp_t``,
           beq(``variant:bir_exp_t``, ``BExp_Const (Imm64 free_var)``)
           ])))
==>
(bir_triple prog l ls (^(band(``invariant:bir_exp_t``, bnot ``condition:bir_exp_t``))) postcondition) ==>
(bir_triple prog l ls invariant postcondition)
``, cheat
);



val _ = export_theory();
