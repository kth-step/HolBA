open HolKernel Parse boolLib bossLib;

open HolBACoreSimps
open bir_expTheory bir_exp_immTheory bir_valuesTheory
open bir_typing_expTheory bir_envTheory wordsTheory
open bir_exp_immSyntax

open listTheory;

val _ = new_theory "bir_angr";

val BExp_Mask_def = Define `
    BExp_Mask sz u l e =
      BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_RightShift e (BExp_Const (n2bs l sz)))
        (BExp_Const (n2bs (2 ** (u - l + 1) - 1) sz))
`;
(*
EVAL ``BExp_Const (Imm16 (((1w) << (7-0+1))-1w))``

EVAL ``n2bs (2 ** (size_of_bir_immtype Bit8) - (2 ** 1)) Bit8``

EVAL ``n2bs (2 ** (size_of_bir_immtype Bit8) - 1) Bit8``

val test_exp2 = ``(BExp_Const (n2bs 0x731 Bit16))``;
val test_exp = ``BExp_Mask Bit16 6 3 (BExp_Const (n2bs 0x731 Bit16))``;
EVAL ``^test_exp``

bir_immTheory.n2bs_def
EVAL ``type_of_bir_exp ^test_exp``
(bir_valuesSyntax.dest_BType_Imm o optionSyntax.dest_some o snd o dest_eq o concl o EVAL) ``type_of_bir_exp ^test_exp2``

EVAL ``bir_eval_exp ^test_exp bir_env_empty``
``0x6``
*)
  
val BExp_Mask_type_of = store_thm
  ("BExp_Mask_type_of", ``
!sz u l e. type_of_bir_exp (BExp_Mask sz u l e) =
           if (type_of_bir_exp e = SOME (BType_Imm sz)) then
               SOME (BType_Imm sz) else NONE
``,
  REPEAT GEN_TAC >>
  SIMP_TAC (std_ss++holBACore_ss) [BExp_Mask_def, type_of_bir_exp_def,
    pairTheory.pair_case_thm] >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
  )
);



val masklist_size_def = Define `
    masklist_size l =
      bir_immtype_of_size (SUM (MAP (\(u,l,_). u-l+1) l))
`;

val masklist_exp_def = Define `
    masklist_exp sz (u,l,e) orbits =
      (BExp_BinExp BIExp_LeftShift
         (BExp_Mask sz u l (BExp_Cast BIExp_LowCast e sz))
         (BExp_Const (n2bs orbits sz)))
`;

val masklist_fold_def = Define `
    masklist_fold sz (u,l,e) (orbits, ore) =
      (orbits + u-l+1,
       BExp_BinExp BIExp_Or
         (masklist_exp sz (u,l,e) orbits)
         ore)
`;

val BExp_AppendMask_def = Define `
    BExp_AppendMask l =
      if IS_NONE (masklist_size l) then
        BExp_BinExp BIExp_And (BExp_Const (Imm1 0w)) (BExp_Const (Imm8 0w))
      else
        SND (FOLDR (masklist_fold (THE (masklist_size l)))
                   (0, BExp_Const (n2bs 0 (THE (masklist_size l))))
                   l)
`;
(*
EVAL ``FOLDR (\x. \a. (x+1)::a) [] [1;2;3]``
type_of ``masklist_fold``
type_of ``Bit1``

val test_exp = ``BExp_AppendMask [
  (10, 3, BExp_Const (n2bs 0xBEEF Bit32));
  (6, 3, BExp_Const (n2bs 0xBEEF Bit32));
  (6, 3, BExp_Const (n2bs 0xBEEF Bit32))]``;
val test_exp_expanded = (snd o dest_eq o concl o EVAL) ``^test_exp``;
bir_type_of test_exp_expanded;

EVAL ``bir_eval_exp ^test_exp bir_env_empty``
``0xDDDD``
*)

val masklist_size_EMPTY_thm = store_thm
  ("masklist_size_EMPTY_thm", ``
!l. (NULL l) ==>
    (masklist_size l = NONE)
``,
  Cases_on `l` >> (
    REWRITE_TAC [NULL_DEF, masklist_size_def]
  ) >>

  REWRITE_TAC [MAP, SUM, bir_immTheory.bir_immtype_of_size_def] >>
  SIMP_TAC std_ss []
);


val type_of_masklist_exp_thm = store_thm
  ("type_of_masklist_exp_thm", ``
!sz u l e orbits sz'.
  (type_of_bir_exp e = SOME (BType_Imm sz')) ==>
  (type_of_bir_exp (masklist_exp sz (u,l,e) orbits) = SOME (BType_Imm sz))
``,
  REWRITE_TAC [masklist_exp_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [type_of_bir_exp_def, BExp_Mask_type_of, bir_type_is_Imm_def] >>

  REPEAT STRIP_TAC >>
  CASE_TAC >>
  POP_ASSUM (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

val type_of_SND_masklist_fold_thm = store_thm
  ("type_of_SND_masklist_fold_thm", ``
!sz u l e orbits ore.
  (type_of_bir_exp ore = SOME (BType_Imm sz)) ==>
  (?sz'. type_of_bir_exp e = SOME (BType_Imm sz')) ==>
  (type_of_bir_exp (SND (masklist_fold sz (u,l,e) (orbits, ore))) = SOME (BType_Imm sz))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [masklist_fold_def, type_of_masklist_exp_thm]
);


val BExp_AppendMask_type_of = store_thm
  ("BExp_AppendMask_type_of", ``
!l. (EVERY (\(_,_,e). ?sz. type_of_bir_exp e = SOME (BType_Imm sz)) l) ==>
    type_of_bir_exp (BExp_AppendMask l) =
    case masklist_size l of
         NONE => NONE
       | SOME ty => SOME (BType_Imm ty)
``,
  REPEAT STRIP_TAC >>
  Cases_on `masklist_size l` >- (
    ASM_SIMP_TAC std_ss [BExp_AppendMask_def] >>
    SIMP_TAC (std_ss) [type_of_bir_exp_def, optionLib.option_rws] >>
    CASE_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  ASM_SIMP_TAC std_ss [BExp_AppendMask_def] >>
  POP_ASSUM (K ALL_TAC) >>

  Induct_on `l` >- (
    SIMP_TAC (std_ss++listSimps.LIST_ss)
      [type_of_bir_exp_def, bir_immTheory.type_of_n2bs]
  ) >>

  SIMP_TAC (std_ss++listSimps.LIST_ss) [] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  POP_ASSUM (K ALL_TAC) >>

  Cases_on `h` >>
  rename1 `masklist_fold x (hu,hle)` >>
  Cases_on `hle` >>
  rename1 `masklist_fold x (hu,hl,he)` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

  Q.ABBREV_TAC `orbitsore = FOLDR (masklist_fold x) (0,BExp_Const (n2bs 0 x)) l` >>
  POP_ASSUM (K ALL_TAC) >>

  Cases_on `orbitsore` >>
  METIS_TAC [type_of_SND_masklist_fold_thm, pairTheory.SND]
);


val _ = export_theory();
