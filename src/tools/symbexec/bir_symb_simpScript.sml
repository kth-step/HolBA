open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;
open symb_auxTheory;

open symb_rulesTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;
open bir_symb_soundTheory;
open bir_bool_expTheory

open arithmeticTheory;
open pred_setTheory;

open HolBACoreSimps;
open symb_typesLib;

open bir_immSyntax;

(*
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
*)

val _ = new_theory "bir_symb_simp";

Theorem symb_simplification_ID_thm:
  !sr.
!pcond symbexp.
  (symb_simplification sr pcond symbexp symbexp)
Proof
REWRITE_TAC [symb_simplification_def]
QED

Theorem symb_simplification_COMM_thm:
  !sr.
!pcond symbexp1 symbexp2.
  (symb_simplification sr pcond symbexp1 symbexp2) ==>
  (symb_simplification sr pcond symbexp2 symbexp1)
Proof
REWRITE_TAC [symb_simplification_def] >>
  REPEAT STRIP_TAC >>

  `sr.sr_symbols_f pcond UNION sr.sr_symbols_f symbexp1 UNION sr.sr_symbols_f symbexp2 =
   sr.sr_symbols_f pcond UNION sr.sr_symbols_f symbexp2 UNION sr.sr_symbols_f symbexp1` by (
    METIS_TAC [UNION_COMM, UNION_ASSOC]
  ) >>

  METIS_TAC []
QED

Theorem symb_simplification_TRANS_thm:
  !sr.
(symb_symbols_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>

!pcond symbexp1 symbexp2 symbexp3.
  (symb_simplification sr pcond symbexp1 symbexp2) ==>
  (symb_simplification sr pcond symbexp2 symbexp3) ==>
  (symb_simplification sr pcond symbexp1 symbexp3)
Proof
REWRITE_TAC [symb_simplification_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H' = symb_interpr_extend_symbs_sr sr (sr.sr_symbols_f symbexp2) H` >>

  `symb_interpr_welltyped sr H'` by (
    METIS_TAC [symb_interpr_extend_symbs_sr_IMP_welltyped_thm]
  ) >>

  `symb_interpr_for_symbs
     (sr.sr_symbols_f pcond UNION
      sr.sr_symbols_f symbexp1 UNION
      sr.sr_symbols_f symbexp2 UNION
      sr.sr_symbols_f symbexp3) H'` by (
    Q.UNABBREV_TAC `H'` >>
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET, symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_dom_thm] >>

    METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
  ) >>


  `symb_interprs_eq_for H H'
     (sr.sr_symbols_f pcond UNION
      sr.sr_symbols_f symbexp1 UNION
      sr.sr_symbols_f symbexp3)` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, symb_interpr_extend_symbs_sr_def, symb_interpr_extend_symbs_IMP_dom_thm] >>
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_def, symb_interprs_eq_for_SUBSET_thm, symb_interprs_eq_for_COMM_thm]
  ) >>

  `sr.sr_interpret_f H pcond = sr.sr_interpret_f H' pcond /\
   sr.sr_interpret_f H symbexp1 = sr.sr_interpret_f H' symbexp1 /\
   sr.sr_interpret_f H symbexp3 = sr.sr_interpret_f H' symbexp3` by (
    METIS_TAC [symb_interprs_eq_for_UNION_thm, symb_interprs_eq_for_COMM_thm, symb_symbols_f_sound_def]
  ) >>

  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET]
QED

Definition symb_exp_imp_def:
  symb_exp_imp sr pcond pcond' =
    (!H.
       (symb_interpr_welltyped sr H) ==>
       (symb_interpr_for_symbs
            (sr.sr_symbols_f pcond UNION
             sr.sr_symbols_f pcond') H) ==>

       (sr.sr_interpret_f H pcond  = SOME sr.sr_val_true) ==>
       (sr.sr_interpret_f H pcond' = SOME sr.sr_val_true)
    )
End


(* ******************************************************* *)
(*     enable reasoning with stronger path conditions      *)
(* ******************************************************* *)
Theorem symb_simplification_IMP_thm:
  !sr.
(symb_symbols_f_sound sr) ==>
(symb_ARB_val_sound sr) ==>

!pcond pcond' symbexp symbexp'.
  (symb_exp_imp sr pcond pcond') ==>
  (symb_simplification sr pcond' symbexp symbexp') ==>
  (symb_simplification sr pcond  symbexp symbexp')
Proof
REWRITE_TAC [symb_exp_imp_def, symb_simplification_def] >>
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
QED


Definition birs_simplification_def:
  birs_simplification pcond symbexp symbexp' =
    (!H.
       (birs_interpr_welltyped H) ==>
       (symb_interpr_for_symbs
            ((bir_vars_of_exp pcond) UNION
             (bir_vars_of_exp symbexp) UNION
             (bir_vars_of_exp symbexp')) H) ==>

       (birs_interpret_fun H pcond = SOME bir_val_true) ==>
       (birs_interpret_fun H symbexp = birs_interpret_fun H symbexp')
    )
End

Theorem birs_simplification_thm:
  !prog.
!pcond symbexp symbexp'.
  (symb_simplification (bir_symb_rec_sbir prog) pcond symbexp symbexp') <=>
  (birs_simplification pcond symbexp symbexp')
Proof
REWRITE_TAC [symb_simplification_def, birs_simplification_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def]
QED

Definition birs_exp_imp_def:
  birs_exp_imp pcond pcond' =
    (!H.
       (birs_interpr_welltyped H) ==>
       (symb_interpr_for_symbs
            (bir_vars_of_exp pcond UNION
             bir_vars_of_exp pcond') H) ==>

       (birs_interpret_fun H pcond  = SOME bir_val_true) ==>
       (birs_interpret_fun H pcond' = SOME bir_val_true)
    )
End

Theorem birs_exp_imp_thm:
  !prog.
!pcond pcond'.
  (symb_exp_imp (bir_symb_rec_sbir prog) pcond pcond') <=>
  (birs_exp_imp pcond pcond')
Proof
REWRITE_TAC [symb_exp_imp_def, birs_exp_imp_def] >>
  REWRITE_TAC [birs_interpr_welltyped_EQ_thm] >>
  SIMP_TAC (std_ss++symb_TYPES_ss) [bir_symb_rec_sbir_def]
QED

Theorem birs_simplification_IMP_thm:
  !pcond pcond' symbexp symbexp'.
  (birs_exp_imp pcond pcond') ==>
  (birs_simplification pcond' symbexp symbexp') ==>
  (birs_simplification pcond  symbexp symbexp')
Proof
METIS_TAC [symb_simplification_IMP_thm, birs_simplification_thm, birs_exp_imp_thm,
             birs_symb_ARB_val_sound_thm, birs_symb_symbols_f_sound_thm]
QED

Theorem birs_simplification_ID_thm:
  !pcond symbexp.
  (birs_simplification pcond symbexp symbexp)
Proof
METIS_TAC [symb_simplification_ID_thm, birs_simplification_thm]
QED

Theorem birs_simplification_COMM_thm:
  !pcond symbexp1 symbexp2.
  (birs_simplification pcond symbexp1 symbexp2) ==>
  (birs_simplification pcond symbexp2 symbexp1)
Proof
METIS_TAC [symb_simplification_COMM_thm, birs_simplification_thm]
QED

Theorem birs_simplification_TRANS_thm:
  !pcond symbexp1 symbexp2 symbexp3.
  (birs_simplification pcond symbexp1 symbexp2) ==>
  (birs_simplification pcond symbexp2 symbexp3) ==>
  (birs_simplification pcond symbexp1 symbexp3)
Proof
METIS_TAC [symb_simplification_TRANS_thm, birs_simplification_thm,
             birs_symb_ARB_val_sound_thm, birs_symb_symbols_f_sound_thm]
QED



(* ******************************************************* *)
(*      go into the symbolic expression                    *)
(* ******************************************************* *)

Theorem birs_simplification_UnsignedCast_thm:
  !pcond symbexp symbexp' sz.
  (birs_simplification pcond symbexp symbexp') ==>
  (birs_simplification pcond (BExp_Cast BIExp_UnsignedCast symbexp sz) (BExp_Cast BIExp_UnsignedCast symbexp' sz))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

Theorem birs_simplification_SignedCast_thm:
  !pcond symbexp symbexp' sz.
  (birs_simplification pcond symbexp symbexp') ==>
  (birs_simplification pcond (BExp_Cast BIExp_SignedCast symbexp sz) (BExp_Cast BIExp_SignedCast symbexp' sz))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

Theorem birs_simplification_LowCast_thm:
  !pcond symbexp symbexp' sz.
  (birs_simplification pcond symbexp symbexp') ==>
  (birs_simplification pcond (BExp_Cast BIExp_LowCast symbexp sz) (BExp_Cast BIExp_LowCast symbexp' sz))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

Theorem birs_simplification_Minus_left_thm:
  !pcond symbexp1 symbexp1' symbexp2.
  (birs_simplification pcond symbexp1 symbexp1') ==>
  (birs_simplification pcond (BExp_BinExp BIExp_Minus symbexp1 symbexp2) (BExp_BinExp BIExp_Minus symbexp1' symbexp2))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

Theorem birs_simplification_Plus_left_thm:
  !pcond symbexp1 symbexp1' symbexp2.
  (birs_simplification pcond symbexp1 symbexp1') ==>
  (birs_simplification pcond (BExp_BinExp BIExp_Plus symbexp1 symbexp2) (BExp_BinExp BIExp_Plus symbexp1' symbexp2))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

Theorem birs_simplification_Plus_right_thm:
  !pcond symbexp1 symbexp1' symbexp2.
  (birs_simplification pcond symbexp1 symbexp1') ==>
  (birs_simplification pcond (BExp_BinExp BIExp_Plus symbexp2 symbexp1) (BExp_BinExp BIExp_Plus symbexp2 symbexp1'))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED

(* TODO: generalize *)
Theorem birs_simplification_Load_32_addr_thm:
  !pcond symbexp1 symbexp1' bme.
  (birs_simplification pcond symbexp1 symbexp1') ==>
  (birs_simplification pcond (BExp_Load bme symbexp1 BEnd_LittleEndian Bit32) (BExp_Load bme symbexp1' BEnd_LittleEndian Bit32))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED
Theorem birs_simplification_Store_32_addr_thm:
  !pcond symbexp1 symbexp1' bme bve.
  (birs_simplification pcond symbexp1 symbexp1') ==>
  (birs_simplification pcond (BExp_Store bme symbexp1 BEnd_LittleEndian bve) (BExp_Store bme symbexp1' BEnd_LittleEndian bve))
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `H`) >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def]
QED




(* ******************************************************* *)
(*      special cases                                      *)
(* ******************************************************* *)
Theorem birs_simplification_UnsignedCast_LowCast_Twice_thm:
  !pcond be.
  birs_simplification pcond
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast
        (BExp_Cast BIExp_UnsignedCast
          (BExp_Cast BIExp_LowCast be Bit8) Bit32) Bit8) Bit32)
    (BExp_Cast BIExp_UnsignedCast
      (BExp_Cast BIExp_LowCast be Bit8) Bit32)
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  Cases_on `birs_interpret_fun_ALT H be` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    blastLib.FULL_BBLAST_TAC
  )
QED


Theorem birs_simplification_Pcond_Imm_Gen_thm:
  !exp1 exp2.
  (birs_simplification
     (BExp_BinPred BIExp_Equal
       exp1
       exp2)
     exp1
     exp2)
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  Cases_on `birs_interpret_fun_ALT H exp1` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `birs_interpret_fun_ALT H exp2` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `x'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `b` >> Cases_on `b'` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_def, bir_val_true_def]
  )
QED

(* TODO: can probably generalize this much more and still use it, can also make a generic theorem for these two to easily add these kind of simplifications *)
Theorem birs_simplification_And_Minus_thm:
  !be w1.
  birs_simplification
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
Proof
(* the main thing with this is that the path condition implies alignment of be and the constant is also aligned. but we may just require the path condition to imply their combination to be always the same. this is more general *)
  REWRITE_TAC [birs_simplification_Pcond_Imm_Gen_thm]
QED
Theorem birs_simplification_LSB0_And64_thm:
  !be w1.
  birs_simplification
    (BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
        (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
        be)
      (be))
    (BExp_BinExp BIExp_And
      (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
      be)
    (be)
Proof
  REWRITE_TAC [birs_simplification_Pcond_Imm_Gen_thm]
QED
Theorem birs_simplification_SignedLowCast3264_thm:
  !be w1.
  birs_simplification
    (BExp_BinPred BIExp_Equal
      (BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast be Bit32)
         Bit64)
      (be))
    (BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast be Bit32)
         Bit64)
    (be)
Proof
  REWRITE_TAC [birs_simplification_Pcond_Imm_Gen_thm]
QED







(* ******************************************************* *)
(*      arithmetics with constants                         *)
(* ******************************************************* *)
val birs_simp_const_TAC =
  REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def] >>
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  Cases_on `birs_interpret_fun_ALT H be` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `x` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `b` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    blastLib.FULL_BBLAST_TAC
  );

Theorem birs_simplification_Plus_Const64_thm:
  !pcond w1 w2.
  (birs_simplification pcond
    (BExp_BinExp BIExp_Plus
      (BExp_Const (Imm64 w1))
      (BExp_Const (Imm64 w2)))
    (BExp_Const (Imm64 (w1 + w2))))
Proof
 birs_simp_const_TAC
QED

Theorem birs_simplification_Plus_Plus_Const64_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 + w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Minus_Plus_Const64_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm64 (w1 - w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Minus_Minus_Const64_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 + w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Plus_Minus_Const64_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit64)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm64 w1)))
      (BExp_Const (Imm64 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm64 (w1 - w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Plus_Plus_Const32_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit32)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm32 (w1 + w2)))))
Proof
birs_simp_const_TAC
QED
Theorem birs_simplification_Minus_Plus_Const32_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit32)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Plus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 w2)))
    (BExp_BinExp BIExp_Plus
      be
      (BExp_Const (Imm32 (w1 - w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Minus_Minus_Const32_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit32)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Minus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm32 (w1 + w2)))))
Proof
birs_simp_const_TAC
QED

Theorem birs_simplification_Plus_Minus_Const32_thm:
  !pcond be w1 w2.
  (type_of_bir_exp be = SOME (BType_Imm Bit32)) ==>
  (birs_simplification pcond
    (BExp_BinExp BIExp_Plus
      (BExp_BinExp BIExp_Minus
        be
        (BExp_Const (Imm32 w1)))
      (BExp_Const (Imm32 w2)))
    (BExp_BinExp BIExp_Minus
      be
      (BExp_Const (Imm32 (w1 - w2)))))
Proof
birs_simp_const_TAC
QED





(* ******************************************************* *)
(*      type correct expression evaluation                 *)
(* ******************************************************* *)
Theorem birs_interpret_fun_welltyped_IMP_thm:
  !H be ty.
  (birs_interpr_welltyped H) ==>
  (symb_interpr_for_symbs (bir_vars_of_exp be) H) ==>
  (type_of_bir_exp be = SOME ty) ==>
  (?v. birs_interpret_fun H be = SOME v /\
       type_of_bir_val v = ty)
Proof
FULL_SIMP_TAC std_ss [birs_interpret_fun_thm] >>
  Induct_on `be` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_ALT_def, bir_valuesTheory.bir_type_is_Imm_def]
  ) >- (
    (* variables *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, INSERT_SUBSET, EMPTY_SUBSET, birs_interpr_welltyped_def] >>

    METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, optionTheory.THE_DEF, bir_symbTheory.birs_interpret_get_var_def]
  ) >> (
    (* after fixing constants and variables *)
    REPEAT STRIP_TAC >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, UNION_SUBSET] >>

    REPEAT (PAT_X_ASSUM ``!x.A`` (IMP_RES_TAC)) >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_valuesTheory.type_of_bir_val_EQ_ELIMS, bir_valuesTheory.BType_Bool_def]
  ) >- (
    (* if-then-else *)
    CASE_TAC >> (
      ASM_REWRITE_TAC []
    )
  ) >- (
    (* load *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

    ASSUME_TAC (Q.SPECL [`vt`, `b1`, `at`, `f`, `b2`, `(b2n i)`] bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm) >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
    (*
    bir_exp_memTheory.bir_load_from_mem_def
    bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm
    bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm
    *)
  ) >> (
    (* and finally, store *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

    ASSUME_TAC (Q.SPECL [`rty`, `vt`, `at`, `i`, `f`, `b2`, `(b2n i')`] bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm) >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
  )
QED




(* ******************************************************* *)
(*      if then else expressions                           *)
(* ******************************************************* *)
Theorem birs_simplification_IfThenElse_T_thm:
  !pcond ec et ef.
(*
  (IS_SOME (type_of_bir_exp et)) ==>
  (type_of_bir_exp et = type_of_bir_exp ef) ==>
*)
  (IS_SOME (type_of_bir_exp (BExp_IfThenElse ec et ef))) ==>
  (birs_simplification ec (BExp_IfThenElse ec et ef) et)
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

(*
  Cases_on `birs_interpret_fun_ALT H et` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
*)

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def] >>
  Cases_on `type_of_bir_exp ec` >> Cases_on `type_of_bir_exp et` >> Cases_on `type_of_bir_exp ef` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  rename1 `type_of_bir_exp ec = SOME ecty` >>
  rename1 `type_of_bir_exp et = SOME etty` >>
  rename1 `type_of_bir_exp ef = SOME efty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp et) H /\
   symb_interpr_for_symbs (bir_vars_of_exp ef) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem birs_simplification_IfThenElse_F_thm:
  !pcond ec et ef.
(*
  (IS_SOME (type_of_bir_exp et)) ==>
  (type_of_bir_exp et = type_of_bir_exp ef) ==>
*)
  (IS_SOME (type_of_bir_exp (BExp_IfThenElse ec et ef))) ==>
  (birs_simplification (BExp_UnaryExp BIExp_Not ec) (BExp_IfThenElse ec et ef) ef)
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

(*
  Cases_on `birs_interpret_fun_ALT H et` >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
*)

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def] >>
  Cases_on `type_of_bir_exp ec` >> Cases_on `type_of_bir_exp et` >> Cases_on `type_of_bir_exp ef` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  rename1 `type_of_bir_exp ec = SOME ecty` >>
  rename1 `type_of_bir_exp et = SOME etty` >>
  rename1 `type_of_bir_exp ef = SOME efty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp et) H /\
   symb_interpr_for_symbs (bir_vars_of_exp ef) H /\
   symb_interpr_for_symbs (bir_vars_of_exp ec) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>

  `birs_interpret_fun_ALT H ec = SOME (BVal_Imm (Imm1 0w))` by (
    Cases_on `v` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    blastLib.FULL_BBLAST_TAC
  ) >>

  `0w:word1 <> 1w` by (
    blastLib.FULL_BBLAST_TAC
  ) >>

  ASM_SIMP_TAC (std_ss++holBACore_ss) []
QED







(* ******************************************************* *)
(*      memory match and bypass                            *)
(* ******************************************************* *)
(* TODO: could simplify condition for store bypassing with alignment requirement (if it holds in the target code, which should be the case) *)

Theorem birs_simplification_Mem_Match_thm1[local]:
  !at vt sz be_ld be_m be_sa be_v be_la.
  (type_of_bir_exp be_m = SOME (BType_Mem at vt)) ==>
  (size_of_bir_immtype sz MOD size_of_bir_immtype vt = 0) ==>
  (size_of_bir_immtype sz DIV size_of_bir_immtype vt <= 2 ** size_of_bir_immtype at) ==>
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
  (birs_simplification
    (BExp_BinPred BIExp_Equal be_la be_sa)
    be_ld
    (be_v)
  )
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `type_of_bir_exp be_m` >> Cases_on `type_of_bir_exp be_sa` >> Cases_on `type_of_bir_exp be_v` >> Cases_on `type_of_bir_exp be_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  rename1 `type_of_bir_exp be_m = SOME mty` >>
  rename1 `type_of_bir_exp be_sa = SOME saty` >>
  rename1 `type_of_bir_exp be_v = SOME vty` >>
  rename1 `type_of_bir_exp be_la = SOME laty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp be_m) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_sa) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_v) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_la) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>
  rename1 `birs_interpret_fun_ALT H be_m = SOME v_m` >>
  rename1 `birs_interpret_fun_ALT H be_sa = SOME v_sa` >>
  rename1 `birs_interpret_fun_ALT H be_v = SOME v_v` >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME v_la` >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  `v_la = v_sa` by (
    `type_of_bir_val v_la = type_of_bir_val v_sa` by (
      METIS_TAC []
    ) >>

    Cases_on `v_la` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `v_sa` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    Cases_on `b` >> Cases_on `b'` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exp_immTheory.bir_bin_pred_def, bir_val_true_def]
    )
  ) >>

(*
bir_expTheory.bir_eval_store_def
*)

  Cases_on `v_sa` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_m` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>


  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

(*
bir_exp_memTheory.bir_store_load_mem_disjoint_THM
bir_exp_memTheory.bir_store_load_mem_THM
*)

  `?mmap'. bir_store_in_mem vt at b'' f BEnd_LittleEndian (b2n b) = SOME mmap'` by (
    `bir_number_of_mem_splits vt sz at <> NONE` by (
      ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def]
    ) >>
    IMP_RES_TAC bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

  `bir_load_from_mem vt sz at mmap' BEnd_LittleEndian (b2n b) = SOME b''` by (
    METIS_TAC [bir_exp_memTheory.bir_store_load_mem_THM]
  ) >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

(*
val memadsz = 64;
val memvalsz = 8;
val ldstvalsz = 32;
*)
fun gen_mem_simp_helper_goal memadsz memvalsz ldstvalsz =
let
  val _ = if memvalsz = 8 then () else raise Feedback.mk_HOL_ERR "bir_symb_simpScript" "gen_mem_simp_helper_goal" "cannot handle memory that does not use bytes as values";
  val memadsz_tm = bir_immtype_t_of_size memadsz;
  val memvalsz_tm = bir_immtype_t_of_size memvalsz;
  val ldstvalsz_tm = bir_immtype_t_of_size ldstvalsz;
in
 “
  (size_of_bir_immtype ^ldstvalsz_tm MOD size_of_bir_immtype ^memvalsz_tm = 0) /\
  (size_of_bir_immtype ^ldstvalsz_tm DIV size_of_bir_immtype ^memvalsz_tm <= 2 ** size_of_bir_immtype ^memadsz_tm)
 ”
end;

(* the match theorems have consistent naming: MEMADDRSZ_MEMVALSZ_LOADSTOREVALSZ *)
Theorem mem_simp_32_8_8_helper_thm[local]:
  ^(gen_mem_simp_helper_goal 32 8 8)
Proof
EVAL_TAC
QED

Theorem mem_simp_32_8_32_helper_thm[local]:
  ^(gen_mem_simp_helper_goal 32 8 32)
Proof
EVAL_TAC
QED

Theorem mem_simp_64_8_8_helper_thm[local]:
  ^(gen_mem_simp_helper_goal 64 8 8)
Proof
EVAL_TAC
QED

Theorem mem_simp_64_8_32_helper_thm[local]:
  ^(gen_mem_simp_helper_goal 64 8 32)
Proof
EVAL_TAC
QED

Theorem mem_simp_64_8_64_helper_thm[local]:
  ^(gen_mem_simp_helper_goal 64 8 64)
Proof
EVAL_TAC
QED

Theorem birs_simplification_Mem_Match_32_8_8_thm = (SIMP_RULE std_ss [mem_simp_32_8_8_helper_thm] o
    Q.SPECL [`Bit32`, `Bit8`, `Bit8`]) birs_simplification_Mem_Match_thm1;


Theorem birs_simplification_Mem_Match_32_8_32_thm = (SIMP_RULE std_ss [mem_simp_32_8_32_helper_thm] o
    Q.SPECL [`Bit32`, `Bit8`, `Bit32`]) birs_simplification_Mem_Match_thm1;


Theorem birs_simplification_Mem_Match_64_8_8_thm = (SIMP_RULE std_ss [mem_simp_64_8_8_helper_thm] o
    Q.SPECL [`Bit64`, `Bit8`, `Bit8`]) birs_simplification_Mem_Match_thm1;


Theorem birs_simplification_Mem_Match_64_8_32_thm = (SIMP_RULE std_ss [mem_simp_64_8_32_helper_thm] o
    Q.SPECL [`Bit64`, `Bit8`, `Bit32`]) birs_simplification_Mem_Match_thm1;


Theorem birs_simplification_Mem_Match_64_8_64_thm = (SIMP_RULE std_ss [mem_simp_64_8_64_helper_thm] o
    Q.SPECL [`Bit64`, `Bit8`, `Bit64`]) birs_simplification_Mem_Match_thm1;


(* now the memory bypass theorems: *)

(*
val memadsz = 64;
val memvalsz = 8;
val ldsz = 8;
val stsz = 64;
*)
fun gen_simp_mem_bypass_goal memadsz memvalsz ldsz stsz =
let
  val endianness_tm = “BEnd_LittleEndian”;
  val _ = if memvalsz = 8 then () else raise Feedback.mk_HOL_ERR "bir_symb_simpScript" "gen_simp_mem_bypass_goal" "cannot handle memory that does not use bytes as values";
  val memadsz_tm = bir_immtype_t_of_size memadsz;
  val memadsz_imm_tm = bir_imm_of_size memadsz;
  val memvalsz_tm = bir_immtype_t_of_size memvalsz;
  val ldsz_tm = bir_immtype_t_of_size ldsz;
  val stsz_tm = bir_immtype_t_of_size stsz;
  val ldbytelen = ldsz div 8;
  val stbytelen = stsz div 8;
  val ldbytelen_w_tm = wordsSyntax.mk_wordii (ldbytelen, memadsz);
  val stbytelen_w_tm = wordsSyntax.mk_wordii (stbytelen, memadsz);
  val std_pcond =
    “(BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_And
          (BExp_BinPred BIExp_LessThan
            be_sa
            (BExp_BinExp BIExp_Plus be_sa (BExp_Const (^memadsz_imm_tm ^stbytelen_w_tm))))
          (BExp_BinPred BIExp_LessThan
            be_la
            (BExp_BinExp BIExp_Plus be_la (BExp_Const (^memadsz_imm_tm ^ldbytelen_w_tm)))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (^memadsz_imm_tm ^ldbytelen_w_tm)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (^memadsz_imm_tm ^stbytelen_w_tm)))
             be_la))
     )”;
  val spec_8_8_pcond =
    “(BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_LessThan
          be_sa
          (BExp_BinExp BIExp_Plus be_sa (BExp_Const (^memadsz_imm_tm 1w))))
        (BExp_BinExp BIExp_Or
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_la (BExp_Const (^memadsz_imm_tm 1w)))
             be_sa)
           (BExp_BinPred BIExp_LessOrEqual
             (BExp_BinExp BIExp_Plus be_sa (BExp_Const (^memadsz_imm_tm 1w)))
             be_la))
     )”;
  val pcond = if ldsz = 8 andalso stsz = 8 then spec_8_8_pcond else std_pcond;
in
 “
  !be_st be_ld be_m be_sa be_v be_la.
  (be_st =
    (BExp_Store
      be_m
      be_sa
      ^endianness_tm
      be_v)
    ) ==>
  (be_ld =
    (BExp_Load
      be_st
      be_la
      ^endianness_tm
      ^ldsz_tm)
    ) ==>
  (type_of_bir_exp be_st = SOME (BType_Mem ^memadsz_tm ^memvalsz_tm)) ==>
  (type_of_bir_exp be_v = SOME (BType_Imm ^stsz_tm)) ==>
  (IS_SOME (type_of_bir_exp be_ld)) ==>
  (birs_simplification
    ^pcond
    be_ld
    (BExp_Load
      be_m
      be_la
      ^endianness_tm
      ^ldsz_tm)
  )
 ”
end;

(* TODO: either mark as local or put into an aux theory *)
Theorem bool2w_OR_AND_REWRS_thm:
  (!A B. (bool2w A) || (bool2w B) = bool2w (A \/ B)) /\
  (!A B. (bool2w A) && (bool2w B) = bool2w (A /\ B))
Proof
REPEAT STRIP_TAC >> (
        SIMP_TAC std_ss [bir_immTheory.bool2w_def] >>
        Cases_on `A` >> Cases_on `B` >> (
          EVAL_TAC
        )
      )
QED

(*
val memadsz = 32;
val memvalsz = 8;
val ldsz = 32;
val stsz = 8;
*)
fun gen_bir_mem_acc_disjoint_goal memadsz memvalsz ldsz stsz =
let
  val _ = if memvalsz = 8 then () else raise Feedback.mk_HOL_ERR "bir_symb_simpScript" "gen_bir_mem_acc_disjoint_goal" "cannot handle memory that does not use bytes as values";
  val memadsz_tm = bir_immtype_t_of_size memadsz;
  val memadsz_wty_tm = wordsSyntax.mk_int_word_type memadsz;
  val w_la_tm = mk_var ("w_la", memadsz_wty_tm);
  val w_sa_tm = mk_var ("w_sa", memadsz_wty_tm);
  val ldbytelen = ldsz div 8;
  val stbytelen = stsz div 8;
  fun mk_ad_tm i = wordsSyntax.mk_wordii (i, memadsz);
  val ldbytelen_w_tm = mk_ad_tm ldbytelen;
  val stbytelen_w_tm = mk_ad_tm stbytelen;
  fun mk_bir_mem_addr_tm n_tm = “bir_mem_addr ^memadsz_tm ^n_tm”;
  fun mk_w_ad_off_tm w_tm i = (fn tm => if i = 0 then tm else “^tm + ^(numSyntax.term_of_int i)”) “w2n ^w_tm”;
  fun mk_ad_set_tm w_tm n = pred_setSyntax.mk_set (List.tabulate (n, (fn i => mk_bir_mem_addr_tm (mk_w_ad_off_tm w_tm i))));
  val ldad_set_tm = mk_ad_set_tm w_la_tm ldbytelen;
  val stad_set_tm = mk_ad_set_tm w_sa_tm stbytelen;
  val std_cond =
    “(^w_sa_tm <+ ^w_sa_tm + ^stbytelen_w_tm /\ ^w_la_tm <+ ^w_la_tm + ^ldbytelen_w_tm) /\ (^w_la_tm + ^ldbytelen_w_tm <=+ ^w_sa_tm \/ ^w_sa_tm + ^stbytelen_w_tm <=+ ^w_la_tm)”;
  val spec_8_8_cond =
    “(^w_sa_tm <+ ^w_sa_tm + 1w) /\ (^w_la_tm + 1w <=+ ^w_sa_tm \/ ^w_sa_tm + 1w <=+ ^w_la_tm)”;
  val cond = if ldsz = 8 andalso stsz = 8 then spec_8_8_cond else std_cond;
in
 “
  !(^w_sa_tm) (^w_la_tm).
  (^cond) ==>
  (DISJOINT
     ^stad_set_tm
     ^ldad_set_tm)
 ”
end;

val bir_mem_acc_disjoint_TAC =
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss) [bir_exp_memTheory.bir_mem_addr_w2n_SIZES, bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES, wordsTheory.w2n_11] >>
    blastLib.FULL_BBLAST_TAC
  );

(* core disjointness theorems first *)
Theorem bir_mem_acc_disjoint_32_8_32_8_thm[local]:
  ^(gen_bir_mem_acc_disjoint_goal 32 8 32 8)
Proof
  bir_mem_acc_disjoint_TAC
QED

Theorem bir_mem_acc_disjoint_32_8_32_32_thm[local]:
  ^(gen_bir_mem_acc_disjoint_goal 32 8 32 32)
Proof
  bir_mem_acc_disjoint_TAC
QED

Theorem bir_mem_acc_disjoint_32_8_8_8_thm[local]:
  ^(gen_bir_mem_acc_disjoint_goal 32 8 8 8)
Proof
  bir_mem_acc_disjoint_TAC
QED

Theorem bir_mem_acc_disjoint_32_8_8_32_thm[local]:
  ^(gen_bir_mem_acc_disjoint_goal 32 8 8 32)
Proof
  bir_mem_acc_disjoint_TAC
QED

(* the bypass theorems have consistent naming too: MEMADDRSZ_MEMVALSZ_LOADSZ_STOREVALSZ *)

Theorem birs_simplification_Mem_Bypass_32_8_32_8_thm1[local]:
  ^(gen_simp_mem_bypass_goal 32 8 32 8)
Proof
  REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `type_of_bir_exp be_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  rename1 `type_of_bir_exp be_la = SOME laty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp be_m) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_sa) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_v) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_la) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>
  rename1 `birs_interpret_fun_ALT H be_m = SOME v_m` >>
  rename1 `birs_interpret_fun_ALT H be_sa = SOME v_sa` >>
  rename1 `birs_interpret_fun_ALT H be_v = SOME v_v` >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME v_la` >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `v_sa` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_m` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  REPEAT (PAT_X_ASSUM T (K ALL_TAC)) >>
  PAT_X_ASSUM ``Bit8 = rty`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

(*
bir_exp_memTheory.bir_store_load_mem_disjoint_THM
bir_exp_memTheory.bir_store_load_mem_THM
*)

  `?mmap'. bir_store_in_mem Bit8 Bit32 b'' f BEnd_LittleEndian (b2n b) = SOME mmap'` by (
    `bir_number_of_mem_splits Bit8 Bit8 Bit32 <> NONE` by (
      ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
      EVAL_TAC
    ) >>
    IMP_RES_TAC bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `v_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm bi_la)` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 mmap' BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 f BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  `DISJOINT (bir_store_in_mem_used_addrs Bit8 b'' Bit32 BEnd_LittleEndian (b2n b))
         (bir_load_from_mem_used_addrs Bit8 Bit32 Bit32 BEnd_LittleEndian (b2n bi_la))` by (
    (*
    bir_exp_memTheory.bir_load_from_mem_used_addrs_def
    bir_exp_memTheory.bir_load_from_mem_used_addrs_REWRS
    bir_exp_memTheory.bir_store_in_mem_used_addrs_def
    bir_exp_memTheory.bir_store_in_mem_used_addrs_REWRS
    *)
    Cases_on `b''` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    Cases_on `bi_la` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm (Imm32 w_la))` >>
    rename1 `birs_interpret_fun_ALT H be_sa = SOME (BVal_Imm (Imm32 w_sa))` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_OR_AND_REWRS_thm] >>

    MATCH_MP_TAC bir_mem_acc_disjoint_32_8_32_8_thm >>
    FULL_SIMP_TAC std_ss [bir_immTheory.bool2w_EQ_ELIMS]
  ) >>

  IMP_RES_TAC bir_exp_memTheory.bir_store_load_mem_disjoint_THM >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem birs_simplification_Mem_Bypass_32_8_32_8_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_8_32_8_thm1

Theorem birs_simplification_Mem_Bypass_64_8_64_8_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 64 8)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_64_8_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_64_8_thm1

Theorem birs_simplification_Mem_Bypass_32_8_32_32_thm1[local]:
  ^(gen_simp_mem_bypass_goal 32 8 32 32)
Proof
  REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `type_of_bir_exp be_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  rename1 `type_of_bir_exp be_la = SOME laty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp be_m) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_sa) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_v) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_la) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>
  rename1 `birs_interpret_fun_ALT H be_m = SOME v_m` >>
  rename1 `birs_interpret_fun_ALT H be_sa = SOME v_sa` >>
  rename1 `birs_interpret_fun_ALT H be_v = SOME v_v` >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME v_la` >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `v_sa` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_m` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  REPEAT (PAT_X_ASSUM T (K ALL_TAC)) >>
  PAT_X_ASSUM ``Bit32 = rty`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

(*
bir_exp_memTheory.bir_store_load_mem_disjoint_THM
bir_exp_memTheory.bir_store_load_mem_THM
*)

  `?mmap'. bir_store_in_mem Bit8 Bit32 b'' f BEnd_LittleEndian (b2n b) = SOME mmap'` by (
    `bir_number_of_mem_splits Bit8 Bit32 Bit32 <> NONE` by (
      ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
      EVAL_TAC
    ) >>
    IMP_RES_TAC bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `v_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm bi_la)` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

  `?bv_res. bir_load_from_mem Bit8 Bit32 Bit32 mmap' BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  `?bv_res. bir_load_from_mem Bit8 Bit32 Bit32 f BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  `DISJOINT (bir_store_in_mem_used_addrs Bit8 b'' Bit32 BEnd_LittleEndian (b2n b))
         (bir_load_from_mem_used_addrs Bit8 Bit32 Bit32 BEnd_LittleEndian (b2n bi_la))` by (
    (*
    bir_exp_memTheory.bir_load_from_mem_used_addrs_def
    bir_exp_memTheory.bir_load_from_mem_used_addrs_REWRS
    bir_exp_memTheory.bir_store_in_mem_used_addrs_def
    bir_exp_memTheory.bir_store_in_mem_used_addrs_REWRS
    *)
    Cases_on `b''` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    Cases_on `bi_la` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm (Imm32 w_la))` >>
    rename1 `birs_interpret_fun_ALT H be_sa = SOME (BVal_Imm (Imm32 w_sa))` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_OR_AND_REWRS_thm] >>

    MATCH_MP_TAC bir_mem_acc_disjoint_32_8_32_32_thm >>
    FULL_SIMP_TAC std_ss [bir_immTheory.bool2w_EQ_ELIMS]
  ) >>

  IMP_RES_TAC bir_exp_memTheory.bir_store_load_mem_disjoint_THM >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem birs_simplification_Mem_Bypass_32_8_32_32_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_8_32_32_thm1

Theorem birs_simplification_Mem_Bypass_64_8_64_64_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 64 64)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_64_64_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_64_64_thm1

Theorem birs_simplification_Mem_Bypass_32_8_8_8_thm1[local]:
  ^(gen_simp_mem_bypass_goal 32 8 8 8)
Proof
REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `type_of_bir_exp be_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  rename1 `type_of_bir_exp be_la = SOME laty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp be_m) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_sa) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_v) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_la) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>
  rename1 `birs_interpret_fun_ALT H be_m = SOME v_m` >>
  rename1 `birs_interpret_fun_ALT H be_sa = SOME v_sa` >>
  rename1 `birs_interpret_fun_ALT H be_v = SOME v_v` >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME v_la` >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `v_sa` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_m` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  REPEAT (PAT_X_ASSUM T (K ALL_TAC)) >>
  PAT_X_ASSUM ``Bit8 = rty`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

(*
bir_exp_memTheory.bir_store_load_mem_disjoint_THM
bir_exp_memTheory.bir_store_load_mem_THM
*)

  `?mmap'. bir_store_in_mem Bit8 Bit32 b'' f BEnd_LittleEndian (b2n b) = SOME mmap'` by (
    `bir_number_of_mem_splits Bit8 Bit8 Bit32 <> NONE` by (
      ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
      EVAL_TAC
    ) >>
    IMP_RES_TAC bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `v_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm bi_la)` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 mmap' BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 f BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  `DISJOINT (bir_store_in_mem_used_addrs Bit8 b'' Bit32 BEnd_LittleEndian (b2n b))
         (bir_load_from_mem_used_addrs Bit8 Bit8 Bit32 BEnd_LittleEndian (b2n bi_la))` by (
    (*
    bir_exp_memTheory.bir_load_from_mem_used_addrs_def
    bir_exp_memTheory.bir_load_from_mem_used_addrs_REWRS
    bir_exp_memTheory.bir_store_in_mem_used_addrs_def
    bir_exp_memTheory.bir_store_in_mem_used_addrs_REWRS
    *)
    Cases_on `b''` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    Cases_on `bi_la` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm (Imm32 w_la))` >>
    rename1 `birs_interpret_fun_ALT H be_sa = SOME (BVal_Imm (Imm32 w_sa))` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_OR_AND_REWRS_thm] >>

    MATCH_MP_TAC bir_mem_acc_disjoint_32_8_8_8_thm >>
    FULL_SIMP_TAC std_ss [bir_immTheory.bool2w_EQ_ELIMS]
  ) >>

  IMP_RES_TAC bir_exp_memTheory.bir_store_load_mem_disjoint_THM >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem birs_simplification_Mem_Bypass_32_8_8_8_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_8_8_8_thm1

Theorem birs_simplification_Mem_Bypass_64_8_8_8_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 8 8)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_8_8_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_8_8_thm1


Theorem birs_simplification_Mem_Bypass_32_8_8_32_thm1[local]:
  ^(gen_simp_mem_bypass_goal 32 8 8 32)
Proof
  REWRITE_TAC [birs_simplification_def] >>
  REPEAT STRIP_TAC >>

  FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>

  FULL_SIMP_TAC std_ss [bir_bool_expTheory.bir_val_true_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `type_of_bir_exp be_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    FULL_SIMP_TAC std_ss [optionTheory.option_CLAUSES, pairTheory.pair_CASE_def]
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  rename1 `type_of_bir_exp be_la = SOME laty` >>

  `symb_interpr_for_symbs (bir_vars_of_exp be_m) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_sa) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_v) H /\
   symb_interpr_for_symbs (bir_vars_of_exp be_la) H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET]
  ) >>
  REV_FULL_SIMP_TAC (std_ss) [] >>
  IMP_RES_TAC (REWRITE_RULE [birs_interpret_fun_thm] birs_interpret_fun_welltyped_IMP_thm) >>
  rename1 `birs_interpret_fun_ALT H be_m = SOME v_m` >>
  rename1 `birs_interpret_fun_ALT H be_sa = SOME v_sa` >>
  rename1 `birs_interpret_fun_ALT H be_v = SOME v_v` >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME v_la` >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Cases_on `v_sa` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_m` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  Cases_on `v_v` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  REPEAT (PAT_X_ASSUM T (K ALL_TAC)) >>
  PAT_X_ASSUM ``Bit32 = rty`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_store_def] >>

(*
bir_exp_memTheory.bir_store_load_mem_disjoint_THM
bir_exp_memTheory.bir_store_load_mem_THM
*)

  `?mmap'. bir_store_in_mem Bit8 Bit32 b'' f BEnd_LittleEndian (b2n b) = SOME mmap'` by (
    `bir_number_of_mem_splits Bit8 Bit32 Bit32 <> NONE` by (
      ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
      EVAL_TAC
    ) >>
    IMP_RES_TAC bir_symb_supportTheory.bir_store_in_mem_IS_SOME_thm >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `v_la` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>
  rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm bi_la)` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_expTheory.bir_eval_load_def] >>

  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 mmap' BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  `?bv_res. bir_load_from_mem Bit8 Bit8 Bit32 f BEnd_LittleEndian (b2n bi_la) = SOME bv_res` by (
    MATCH_MP_TAC bir_symb_supportTheory.bir_load_from_mem_IS_SOME_thm1 >>
    ASM_SIMP_TAC std_ss [bir_exp_memTheory.bir_number_of_mem_splits_def] >>
    EVAL_TAC
  ) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  `DISJOINT (bir_store_in_mem_used_addrs Bit8 b'' Bit32 BEnd_LittleEndian (b2n b))
         (bir_load_from_mem_used_addrs Bit8 Bit8 Bit32 BEnd_LittleEndian (b2n bi_la))` by (
    (*
    bir_exp_memTheory.bir_load_from_mem_used_addrs_def
    bir_exp_memTheory.bir_load_from_mem_used_addrs_REWRS
    bir_exp_memTheory.bir_store_in_mem_used_addrs_def
    bir_exp_memTheory.bir_store_in_mem_used_addrs_REWRS
    *)
    Cases_on `b''` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    Cases_on `bi_la` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    Cases_on `b` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>

    rename1 `birs_interpret_fun_ALT H be_la = SOME (BVal_Imm (Imm32 w_la))` >>
    rename1 `birs_interpret_fun_ALT H be_sa = SOME (BVal_Imm (Imm32 w_sa))` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_immTheory.bool2b_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bool2w_OR_AND_REWRS_thm] >>

    MATCH_MP_TAC bir_mem_acc_disjoint_32_8_8_32_thm >>
    FULL_SIMP_TAC std_ss [bir_immTheory.bool2w_EQ_ELIMS]
  ) >>

  IMP_RES_TAC bir_exp_memTheory.bir_store_load_mem_disjoint_THM >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem birs_simplification_Mem_Bypass_32_8_8_32_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_32_8_8_32_thm1

Theorem birs_simplification_Mem_Bypass_64_8_8_64_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 8 64)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_8_64_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_8_64_thm1



Theorem birs_simplification_Mem_Bypass_64_8_8_32_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 8 32)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_8_32_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_8_32_thm1

Theorem birs_simplification_Mem_Bypass_64_8_32_32_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 32 32)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_32_32_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_32_32_thm1

Theorem birs_simplification_Mem_Bypass_64_8_32_8_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 32 8)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_32_8_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_32_8_thm1



Theorem birs_simplification_Mem_Bypass_64_8_64_32_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 64 32)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_64_32_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_64_32_thm1

Theorem birs_simplification_Mem_Bypass_64_8_32_64_thm1[local]:
  ^(gen_simp_mem_bypass_goal 64 8 32 64)
Proof
  cheat
QED

Theorem birs_simplification_Mem_Bypass_64_8_32_64_thm = SIMP_RULE std_ss [] birs_simplification_Mem_Bypass_64_8_32_64_thm1



val _ = export_theory();
