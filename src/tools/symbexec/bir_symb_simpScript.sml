open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

open symb_rulesTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;
open bir_symb_soundTheory;

open arithmeticTheory;
open pred_setTheory;

open symb_typesLib;

(*
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
*)

val _ = new_theory "bir_symb_simp";

(* TODO: need to reorganize this a bit to better embed this in the symb_rulesTheory *)
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
    (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs
            (sr.sr_symbols_f pcond UNION
             sr.sr_symbols_f pcond') H) ==>

       (sr.sr_interpret_f H pcond  = SOME sr.sr_val_true) ==>
       (sr.sr_interpret_f H pcond' = SOME sr.sr_val_true)
    )
`;


(* ******************************************************* *)
(*     enable reasoning with stronger path conditions      *)
(* ******************************************************* *)
val symb_simplification_IMP_thm = store_thm(
   "symb_simplification_IMP_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>

!pcond pcond' symbexp symbexp'.
  (symb_exp_imp sr pcond pcond') ==>
  (symb_simplification_e sr pcond' symbexp symbexp') ==>
  (symb_simplification_e sr pcond  symbexp symbexp')
``,
  REWRITE_TAC [symb_exp_imp_def, symb_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H' = symb_interpr_extend_symbs_sr sr (sr.sr_symbols_f pcond') H` >>

  `symb_interpr_welltyped sr H'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_welltyped_thm]
  ) >>

  `symb_interpr_for_symbs
     (sr.sr_symbols_f pcond UNION
      sr.sr_symbols_f pcond' UNION
      sr.sr_symbols_f symbexp UNION
      sr.sr_symbols_f symbexp') H'` by (
    Q.UNABBREV_TAC `H'` >>
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET, symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_dom_thm] >>

    METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
  ) >>


  `symb_interprs_eq_for H H'
     (sr.sr_symbols_f pcond UNION
      sr.sr_symbols_f symbexp UNION
      sr.sr_symbols_f symbexp')` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_dom_thm] >>
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_def, symb_interprs_eq_for_SUBSET_thm, symb_interprs_eq_for_COMM_thm]
  ) >>

  `sr.sr_interpret_f H pcond = sr.sr_interpret_f H' pcond /\
   sr.sr_interpret_f H symbexp = sr.sr_interpret_f H' symbexp /\
   sr.sr_interpret_f H symbexp' = sr.sr_interpret_f H' symbexp'` by (
    METIS_TAC [symb_interprs_eq_for_UNION_thm, symb_interprs_eq_for_COMM_thm, symb_symbols_f_sound_def]
  ) >>

  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>

  REPEAT (PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H'`)) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss []
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
    (!H.
       (birs_interpr_welltyped H) ==>
       (symb_interpr_for_symbs
            (bir_vars_of_exp pcond UNION
             bir_vars_of_exp pcond') H) ==>

       (birs_interpret_fun H pcond  = SOME bir_val_true) ==>
       (birs_interpret_fun H pcond' = SOME bir_val_true)
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
  METIS_TAC [symb_simplification_IMP_thm, birs_simplification_e_thm, birs_exp_imp_thm,
             birs_symb_ARB_val_sound_thm, birs_symb_symbols_f_sound_thm]
);




(* ******************************************************* *)
(*      go into the symbolic expression                    *)
(* ******************************************************* *)

val birs_simplification_UnsignedCast_thm = store_thm(
   "birs_simplification_UnsignedCast_thm", ``
!pcond symbexp symbexp' sz.
  (birs_simplification_e pcond symbexp symbexp') ==>
  (birs_simplification_e pcond (BExp_Cast BIExp_UnsignedCast symbexp sz) (BExp_Cast BIExp_UnsignedCast symbexp' sz))
``,
  REWRITE_TAC [birs_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
);

val birs_simplification_Minus_thm = store_thm(
   "birs_simplification_Minus_thm", ``
!pcond symbexp1 symbexp1' symbexp2.
  (birs_simplification_e pcond symbexp1 symbexp1') ==>
  (birs_simplification_e pcond (BExp_BinExp BIExp_Minus symbexp1 symbexp2) (BExp_BinExp BIExp_Minus symbexp1' symbexp2))
``,
  REWRITE_TAC [birs_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
);





(* ******************************************************* *)
(*      special cases                                      *)
(* ******************************************************* *)
val birs_simplification_UnsignedCast_LowCast_Twice_thm = store_thm(
   "birs_simplification_UnsignedCast_LowCast_Twice_thm", ``
!pcond be.
  birs_simplification_e pcond
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast
        (BExp_Cast BIExp_UnsignedCast
          (BExp_Cast BIExp_LowCast be Bit8) Bit32) Bit8) Bit32)
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast be Bit8) Bit32)
``,
  cheat (* TODO: this should work like this *)
);


val birs_simplification_Pcond_Imm_Gen_thm = store_thm(
   "birs_simplification_Pcond_Imm_Gen_thm", ``
!exp1 exp2.
  (birs_simplification_e
     (BExp_BinPred BIExp_Equal
       exp1
       exp2)
     exp1
     exp2)
``,
  cheat (* TODO: this should work because Imm typing is implied from the "path condition true" assumption, then the contained values are just equal *)
);

(* TODO: can probably generalize this much more and still use it *)
val birs_simplification_And_Minus_thm = store_thm(
   "birs_simplification_And_Minus_thm", ``
!be w1.
  birs_simplification_e
    (BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_Minus
          be
          (BExp_Const (Imm32 w1)))
        (BExp_Const (Imm32 0xFFFFFFFCw)))
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm32 w1))))
    (BExp_BinExp BIExp_And
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 0xFFFFFFFCw)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm32 w1)))
``,
  (* the main thing with this is that the path condition implies alignment of be and the constant is also aligned. but we may just require the path condition to imply their combination to be always the same. this is more general *)
  REWRITE_TAC [birs_simplification_Pcond_Imm_Gen_thm]
);







(* ******************************************************* *)
(*      arithmetics with constants                         *)
(* ******************************************************* *)
val birs_simplification_Plus_Plus_Const_thm = store_thm(
   "birs_simplification_Plus_Plus_Const_thm", ``
!pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification_e pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 + w2)))))
``,
  REWRITE_TAC [birs_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
  cheat (* TODO: this should just work *)
);

(* TODO: need to add the proofs below, should work exactly like the one above *)
val birs_simplification_Minus_Plus_Const_thm = store_thm(
   "birs_simplification_Minus_Plus_Const_thm", ``
!pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification_e pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 - w2)))))
``,
  cheat
);

val birs_simplification_Minus_Minus_Const_thm = store_thm(
   "birs_simplification_Minus_Minus_Const_thm", ``
!pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification_e pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 + w2)))))
``,
  cheat
);

val birs_simplification_Plus_Minus_Const_thm = store_thm(
   "birs_simplification_Plus_Minus_Const_thm", ``
!pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification_e pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 - w2)))))
``,
  cheat
);





(* ******************************************************* *)
(*      if then else expressions                           *)
(* ******************************************************* *)
val birs_simplification_IfThenElse_T_thm = store_thm(
   "birs_simplification_IfThenElse_T_thm", ``
!pcond ec et ef.
(*
  (IS_SOME (type_of_bir_exp et)) ==>
  (type_of_bir_exp et = type_of_bir_exp ef) ==>
*)
  (IS_SOME (type_of_bir_exp (BExp_IfThenElse ec et ef))) ==>
  (birs_simplification_e ec (BExp_IfThenElse ec et ef) et)
``,
  REWRITE_TAC [birs_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>

  (* bir_expTheory.bir_eval_ifthenelse_REWRS *)

  cheat (* TODO: same needs to be proven in the F theorem *)
);

val birs_simplification_IfThenElse_F_thm = store_thm(
   "birs_simplification_IfThenElse_F_thm", ``
!pcond ec et ef.
(*
  (IS_SOME (type_of_bir_exp et)) ==>
  (type_of_bir_exp et = type_of_bir_exp ef) ==>
*)
  (IS_SOME (type_of_bir_exp (BExp_IfThenElse ec et ef))) ==>
  (birs_simplification_e (BExp_UnaryExp BIExp_Not ec) (BExp_IfThenElse ec et ef) ef)
``,
  REWRITE_TAC [birs_simplification_e_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>

  `birs_interpret_fun_ALT H ec = SOME (BVal_Imm (Imm1 0w))` by (
    cheat
  ) >>

  (* bir_expTheory.bir_eval_ifthenelse_REWRS *)

  cheat (* TODO: same needs to be proven in the T theorem *)
);







(* ******************************************************* *)
(*      memory match and bypass                            *)
(* ******************************************************* *)

val birs_simplification_Mem_Match_thm1 = store_thm(
   "birs_simplification_Mem_Match_thm1", ``
!be_ld be_m be_sa be_v be_la sz.
  (be_ld =
    (BExp_Load
      (BExp_Store
        be_m
        be_sa
        BEnd_LittleEndian
        be_v)
      be_la
      BEnd_LittleEndian
      sz)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm sz)) ==>
  (birs_simplification_e
    (BExp_BinPred BIExp_Equal be_la be_sa)
    be_ld
    (be_v)
  )
``,
  cheat
);

val birs_simplification_Mem_Match_thm = save_thm(
   "birs_simplification_Mem_Match_thm",
   SIMP_RULE std_ss [] birs_simplification_Mem_Match_thm1
);

val birs_simplification_Mem_Bypass_32_8_thm1 = store_thm(
   "birs_simplification_Mem_Bypass_32_8_thm1", ``
!be_st be_ld be_m be_sa be_v be_la.
  (be_st =
    (BExp_Store
      be_m
      be_sa
      BEnd_LittleEndian
      be_v)
    ) ==>
  (be_ld =
    (BExp_Load
      be_st
      be_la
      BEnd_LittleEndian
      Bit32)
    ) ==>
  (type_of_bir_exp be_st = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit8)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (birs_simplification_e
    (BExp_BinExp BIExp_Or
      (BExp_BinExp BIExp_And
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 4w)))
           be_sa)
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w)))
           be_la))
      (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessThan
          be_sa
          (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 4w)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w)))
             be_la))
      )
    )
    be_ld
    (BExp_Load
      be_m
      be_la
      BEnd_LittleEndian
      Bit32)
  )
``,
  cheat
);

val birs_simplification_Mem_Bypass_32_8_thm = save_thm(
   "birs_simplification_Mem_Bypass_32_8_thm",
   SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_8_thm1
);

val birs_simplification_Mem_Bypass_32_32_thm1 = store_thm(
   "birs_simplification_Mem_Bypass_32_32_thm1", ``
!be_st be_ld be_m be_sa be_v be_la.
  (be_st =
    (BExp_Store
      be_m
      be_sa
      BEnd_LittleEndian
      be_v)
    ) ==>
  (be_ld =
    (BExp_Load
      be_st
      be_la
      BEnd_LittleEndian
      Bit32)
    ) ==>
  (type_of_bir_exp be_st = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit32)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (birs_simplification_e
    (BExp_BinExp BIExp_Or
      (BExp_BinExp BIExp_And
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 4w)))
           be_sa)
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w)))
           be_la))
      (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessThan
          be_sa
          (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 4w)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w)))
             be_la))
      )
    )
    be_ld
    (BExp_Load
      be_m
      be_la
      BEnd_LittleEndian
      Bit32)
  )
``,
  cheat
);

val birs_simplification_Mem_Bypass_32_32_thm = save_thm(
   "birs_simplification_Mem_Bypass_32_32_thm",
   SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_32_thm1
);

val birs_simplification_Mem_Bypass_8_8_thm1 = store_thm(
   "birs_simplification_Mem_Bypass_8_8_thm1", ``
!be_st be_ld be_m be_sa be_v be_la.
  (be_st =
    (BExp_Store
      be_m
      be_sa
      BEnd_LittleEndian
      be_v)
    ) ==>
  (be_ld =
    (BExp_Load
      be_st
      be_la
      BEnd_LittleEndian
      Bit8)
    ) ==>
  (type_of_bir_exp be_st = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit8)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (birs_simplification_e
    (BExp_BinExp BIExp_Or
      (BExp_BinExp BIExp_And
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 1w)))
           be_sa)
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w)))
           be_la))
      (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessThan
          be_sa
          (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 1w)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 1w)))
             be_la))
      )
    )
    be_ld
    (BExp_Load
      be_m
      be_la
      BEnd_LittleEndian
      Bit8)
  )
``,
  cheat
);

val birs_simplification_Mem_Bypass_8_8_thm = save_thm(
   "birs_simplification_Mem_Bypass_8_8_thm",
   SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_8_8_thm1
);

val birs_simplification_Mem_Bypass_8_32_thm1 = store_thm(
   "birs_simplification_Mem_Bypass_8_32_thm1", ``
!be_st be_ld be_m be_sa be_v be_la.
  (be_st =
    (BExp_Store
      be_m
      be_sa
      BEnd_LittleEndian
      be_v)
    ) ==>
  (be_ld =
    (BExp_Load
      be_st
      be_la
      BEnd_LittleEndian
      Bit8)
    ) ==>
  (type_of_bir_exp be_st = SOME (BType_Mem Bit32 Bit8)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm Bit32)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (birs_simplification_e
    (BExp_BinExp BIExp_Or
      (BExp_BinExp BIExp_And
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 1w)))
           be_sa)
         (BExp_BinPred BIExp_LessOrEqual
           (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w)))
           be_la))
      (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessThan
          be_sa
          (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (Imm32 1w)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (Imm32 4w)))
             be_la))
      )
    )
    be_ld
    (BExp_Load
      be_m
      be_la
      BEnd_LittleEndian
      Bit8)
  )
``,
  cheat
);

val birs_simplification_Mem_Bypass_8_32_thm = save_thm(
   "birs_simplification_Mem_Bypass_8_32_thm",
   SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_8_32_thm1
);



val _ = export_theory();
