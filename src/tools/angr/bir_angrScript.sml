open HolKernel Parse boolLib bossLib;

open HolBACoreSimps
open bir_expTheory bir_exp_immTheory bir_valuesTheory
open bir_typing_expTheory bir_envTheory wordsTheory
open bir_exp_immSyntax

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

val masklist_fold_def = Define `
    masklist_fold sz (u,l,e) (orbits, ore) =
      (orbits + u-l+1,
       BExp_BinExp BIExp_Or
         (BExp_BinExp BIExp_LeftShift (BExp_Mask sz u l e) (BExp_Const (n2bs orbits sz)))
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
  (10, 3, BExp_Const (n2bs 0xBEEF Bit16));
  (6, 3, BExp_Const (n2bs 0xBEEF Bit16));
  (6, 3, BExp_Const (n2bs 0xBEEF Bit16))]``;
EVAL ``^test_exp``;

EVAL ``bir_eval_exp ^test_exp bir_env_empty``
``0xDDDD``
*)

val BExp_AppendMask_type_of = store_thm
  ("BExp_AppendMask_type_of", ``
!l. type_of_bir_exp (BExp_AppendMask l) =
 if LENGTH l > 0
 then case masklist_size l of
         NONE => NONE
       | SOME ty => SOME (BType_Imm ty)
 else NONE
``,
  cheat
);

val _ = export_theory();
