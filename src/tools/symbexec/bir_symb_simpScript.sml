open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

open symb_rulesTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open arithmeticTheory;
open pred_setTheory;

open symb_typesLib;

(*
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
*)

val _ = new_theory "bir_symb_simp";

val symb_simplification_e_def = Define `
    symb_simplification_e sr pcond symbexp symbexp' =
    (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs
            ((sr.sr_symbols_f pcond) UNION
             (sr.sr_symbols_f symbexp) UNION
             (sr.sr_symbols_f symbexp')) H) ==>

       (sr.sr_interpret_f H pcond = SOME sr.sr_val_true) ==>
       (sr.sr_interpret_f H symbexp = sr.sr_interpret_f H symbexp')
    )
`;

val symb_simplification_thm = store_thm(
   "symb_simplification_thm", ``
!sr.
!sys symbexp symbexp'.
  (symb_simplification sr sys symbexp symbexp') ==>
  (symb_simplification_e sr (symb_symbst_pcond sys) symbexp symbexp')
``,
  REWRITE_TAC [symb_simplification_def, symb_simplification_e_def, symb_interpr_symbpcond_def]
);

val symb_exp_imp_def = Define `
    symb_exp_imp sr pcond pcond' =
    ((sr.sr_symbols_f pcond' SUBSET sr.sr_symbols_f pcond) /\
     (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs
            (sr.sr_symbols_f pcond) H) ==>

       (sr.sr_interpret_f H pcond  = SOME sr.sr_val_true) ==>
       (sr.sr_interpret_f H pcond' = SOME sr.sr_val_true)
     )
    )
`;

val symb_simplification_IMP_thm = store_thm(
   "symb_simplification_IMP_thm", ``
!sr.
!pcond pcond' symbexp symbexp'.
  (symb_exp_imp sr pcond pcond') ==>
  (symb_simplification_e sr pcond' symbexp symbexp') ==>
  (symb_simplification_e sr pcond  symbexp symbexp')
``,
  REWRITE_TAC [symb_exp_imp_def, symb_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  `symb_interpr_for_symbs (sr.sr_symbols_f pcond) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET]
  ) >>

  `symb_interpr_for_symbs
          (sr.sr_symbols_f pcond' UNION sr.sr_symbols_f symbexp UNION
           sr.sr_symbols_f symbexp') H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
    METIS_TAC [SUBSET_TRANS]
  ) >>

  METIS_TAC []
);


val birs_simplification_e_def = Define `
    birs_simplification_e pcond symbexp symbexp' =
    (!H.
       (birs_interpr_welltyped H) ==>
       (symb_interpr_for_symbs
            ((bir_vars_of_exp pcond) UNION
             (bir_vars_of_exp symbexp) UNION
             (bir_vars_of_exp symbexp')) H) ==>

       (birs_interpret_fun H pcond = SOME bir_val_true) ==>
       (birs_interpret_fun H symbexp = birs_interpret_fun H symbexp')
    )
`;

val birs_simplification_e_thm = store_thm(
   "birs_simplification_e_thm", ``
!prog.
!pcond symbexp symbexp'.
  (symb_simplification_e (bir_symb_rec_sbir prog) pcond symbexp symbexp') <=>
  (birs_simplification_e pcond symbexp symbexp')
``,
  REWRITE_TAC [symb_simplification_e_def, birs_simplification_e_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def]
);

val birs_exp_imp_def = Define `
    birs_exp_imp pcond pcond' =
    ((bir_vars_of_exp pcond' SUBSET bir_vars_of_exp pcond) /\
     (!H.
       (birs_interpr_welltyped H) ==>
       (symb_interpr_for_symbs
            (bir_vars_of_exp pcond) H) ==>

       (birs_interpret_fun H pcond  = SOME bir_val_true) ==>
       (birs_interpret_fun H pcond' = SOME bir_val_true)
     )
    )
`;

val birs_exp_imp_thm = store_thm(
   "birs_exp_imp_thm", ``
!prog.
!pcond pcond'.
  (symb_exp_imp (bir_symb_rec_sbir prog) pcond pcond') <=>
  (birs_exp_imp pcond pcond')
``,
  REWRITE_TAC [symb_exp_imp_def, birs_exp_imp_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def]
);

val birs_simplification_IMP_thm = store_thm(
   "birs_simplification_IMP_thm", ``
!pcond pcond' symbexp symbexp'.
  (birs_exp_imp pcond pcond') ==>
  (birs_simplification_e pcond' symbexp symbexp') ==>
  (birs_simplification_e pcond  symbexp symbexp')
``,
  METIS_TAC [symb_simplification_IMP_thm, birs_simplification_e_thm, birs_exp_imp_thm]
);






val symb_simplification_UnsignedCast_thm = store_thm(
   "symb_simplification_UnsignedCast_thm", ``
!pcond symbexp symbexp' sz.
  (birs_simplification_e pcond symbexp symbexp') ==>
  (birs_simplification_e pcond (BExp_Cast BIExp_UnsignedCast symbexp sz) (BExp_Cast BIExp_UnsignedCast symbexp' sz))
``,
  cheat
);

val symb_simplification_IfThenElse_T_thm = store_thm(
   "symb_simplification_IfThenElse_T_thm", ``
!pcond ec et ef.
  (birs_simplification_e ec (BExp_IfThenElse ec et ef) et)
``,
  cheat
);

val symb_simplification_IfThenElse_F_thm = store_thm(
   "symb_simplification_IfThenElse_F_thm", ``
!pcond ec et ef.
  (birs_simplification_e (BExp_UnaryExp BIExp_Not ec) (BExp_IfThenElse ec et ef) ef)
``,
  cheat
);

(* TODO: need to typecheck the whole expression, also in the next theorem *)
val symb_simplification_Mem_Match_thm = store_thm(
   "symb_simplification_Mem_Match_thm", ``
!be_m be_sa be_v be_la sz masz mvsz.
  (type_of_bir_exp be_m = SOME (BType_Mem masz mvsz)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm sz)) ==>
  (birs_simplification_e
    (BExp_BinPred BIExp_Equal be_la be_sa)
    (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      sz)
    (be_v)
  )
``,
  cheat
);

(* TODO: corner cases? make it so it also works for these *)
(* TODO: need one of these for 32bit stores as well, and the other two combinations *)
val symb_simplification_Mem_Bypass_thm = store_thm(
   "symb_simplification_Mem_Bypass_thm", ``
!be_m be_sa be_v be_la.
  (type_of_bir_exp be_m = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit8)) ==>
  (birs_simplification_e
    (BExp_BinExp BIExp_Or
       (BExp_BinPred BIExp_LessOrEqual
         (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 4w)))
         be_sa)
       (BExp_BinPred BIExp_LessOrEqual
         (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w)))
         be_la))
    (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      Bit32)
    (BExp_Load
      be_m
      be_la
      BEnd_LittleEndian
      Bit32)
  )
``,
  cheat
);



val _ = export_theory();
