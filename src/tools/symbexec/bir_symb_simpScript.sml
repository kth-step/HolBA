open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

open symb_rulesTheory;

open arithmeticTheory;
open pred_setTheory;


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
  METIS_TAC [symb_simplification_def, symb_simplification_e_def, symb_interpr_symbpcond_def]
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
  cheat
);

val symb_simplification_UnsignedCast_thm = store_thm(
   "symb_simplification_UnsignedCast_thm", ``
!sr.
!pcond symbexp symbexp' sz.
  (symb_simplification_e sr pcond symbexp symbexp') ==>
  (symb_simplification_e sr pcond (BExp_Cast BIExp_UnsignedCast symbexp sz) (BExp_Cast BIExp_UnsignedCast symbexp' sz))
``,
  cheat
);

val symb_simplification_IfThenElse_T_thm = store_thm(
   "symb_simplification_IfThenElse_T_thm", ``
!sr.
!pcond ec et ef.
  (symb_simplification_e sr ec (BExp_IfThenElse ec et ef) et)
``,
  cheat
);

val symb_simplification_IfThenElse_F_thm = store_thm(
   "symb_simplification_IfThenElse_F_thm", ``
!sr.
!pcond ec et ef.
  (symb_simplification_e sr (BExp_UnaryExp BIExp_Not ec) (BExp_IfThenElse ec et ef) ef)
``,
  cheat
);

(* TODO: need to typecheck the whole expression, also in the next theorem *)
val symb_simplification_Mem_Match_thm = store_thm(
   "symb_simplification_Mem_Match_thm", ``
!sr.
!be_m be_sa be_v be_la sz masz mvsz.
  (type_of_bir_exp be_m = SOME (BType_Mem masz mvsz)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm sz)) ==>
  (symb_simplification_e sr
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
!sr.
!be_m be_sa be_v be_la.
  (type_of_bir_exp be_m = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit8)) ==>
  (symb_simplification_e sr
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
