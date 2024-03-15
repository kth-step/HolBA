open HolKernel Parse boolLib bossLib;
open wordsTheory integer_wordTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_immSyntax;

val _ = new_theory "bir_exp_imm";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));


(* ------------------------------------------------------------------------- *)
(*  Unary expressions                                                        *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_unary_exp_t =
  | BIExp_ChangeSign
  | BIExp_Not
  | BIExp_CLZ
  | BIExp_CLS
End


(*
arm8Theory.HighestSetBit_def
arm8Theory.CountLeadingZeroBits_def
arm8Theory.CountLeadingSignBits_def
*)

Definition bir_HighestSetBit_def:
  bir_HighestSetBit (w:'a word) = if w = 0w then -1 else w2i (word_log2 w)
End
Definition bir_CountLeadingZeroBits_def:
  bir_CountLeadingZeroBits (w:'a word) = Num (((&(word_len (0w:'a word))) - 1) - (bir_HighestSetBit w))
End
Definition bir_CountLeadingSignBits_def:
  bir_CountLeadingSignBits (w:'a word) = bir_CountLeadingZeroBits (word_xor (w >>> 1) (w && (word_1comp(word_ror (1w:'a word) 1)))) -1
End

Definition bir_word_countleadingzeros_def:
  bir_word_countleadingzeros (w:'a word) = (n2w (bir_CountLeadingZeroBits w) :'a word)
End
Definition bir_word_countleadingsigns_def:
  bir_word_countleadingsigns (w:'a word) = (n2w (bir_CountLeadingSignBits w) :'a word)
End

Definition bir_unary_exp_GET_OPER_def:
  (bir_unary_exp_GET_OPER BIExp_Not = word_1comp) /\
   (bir_unary_exp_GET_OPER BIExp_ChangeSign = word_2comp) /\
   (bir_unary_exp_GET_OPER BIExp_CLZ = bir_word_countleadingzeros) /\
   (bir_unary_exp_GET_OPER BIExp_CLS = bir_word_countleadingsigns)
End

Definition bir_unary_exp_def:
  (bir_unary_exp uo (Imm128 w) = Imm128 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm64 w)  = Imm64 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm32 w)  = Imm32 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm16 w)  = Imm16 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm8 w)   = Imm8  (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm1 w)   = Imm1  (bir_unary_exp_GET_OPER uo w))
End

Theorem bir_unary_exp_REWRS:
  !uo.
  (!w. (bir_unary_exp uo (Imm1 w)   = Imm1   (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm8 w)   = Imm8   (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm16 w)  = Imm16  (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm32 w)  = Imm32  (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm64 w)  = Imm64  (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm128 w) = Imm128 (bir_unary_exp_GET_OPER uo w)))
Proof
SIMP_TAC std_ss [bir_unary_exp_def]
QED


Theorem type_of_bir_unary_exp:
  !uo r. type_of_bir_imm (bir_unary_exp uo r) = type_of_bir_imm r
Proof
GEN_TAC >> Cases >> (
  SIMP_TAC std_ss [type_of_bir_imm_def, bir_unary_exp_def]
)
QED


(* ------------------------------------------------------------------------- *)
(*  Binary expressions                                                       *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_bin_exp_t =
  | BIExp_And
  | BIExp_Or
  | BIExp_Xor
  | BIExp_Plus
  | BIExp_Minus
  | BIExp_Mult
  | BIExp_Div
  | BIExp_SignedDiv
  | BIExp_Mod
  | BIExp_SignedMod
  | BIExp_LeftShift
  | BIExp_RightShift
  | BIExp_SignedRightShift
End

Definition bir_bin_exp_GET_OPER_def:
  (bir_bin_exp_GET_OPER BIExp_And = word_and) /\
   (bir_bin_exp_GET_OPER BIExp_Or = word_or) /\
   (bir_bin_exp_GET_OPER BIExp_Xor = word_xor) /\
   (bir_bin_exp_GET_OPER BIExp_Plus = $+) /\
   (bir_bin_exp_GET_OPER BIExp_Minus = $-) /\
   (bir_bin_exp_GET_OPER BIExp_Mult = $*) /\
   (bir_bin_exp_GET_OPER BIExp_Div = $//) /\
   (bir_bin_exp_GET_OPER BIExp_SignedDiv = $/) /\
   (bir_bin_exp_GET_OPER BIExp_Mod =  word_mod) /\
   (bir_bin_exp_GET_OPER BIExp_SignedMod = word_smod) /\
   (bir_bin_exp_GET_OPER BIExp_LeftShift = word_lsl_bv) /\
   (bir_bin_exp_GET_OPER BIExp_RightShift = word_lsr_bv) /\
   (bir_bin_exp_GET_OPER BIExp_SignedRightShift = word_asr_bv) /\
   (bir_bin_exp_GET_OPER _ = ARB) (* Should never fire *)
End

Definition bir_bin_exp_def:
  (bir_bin_exp uo (Imm128 w1) (Imm128 w2) = Imm128 (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm64  w1) (Imm64  w2) = Imm64  (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm32  w1) (Imm32  w2) = Imm32  (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm16  w1) (Imm16  w2) = Imm16  (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm8   w1) (Imm8   w2) = Imm8   (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm1   w1) (Imm1   w2) = Imm1   (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo _ _ = ARB)
End

Theorem bir_bin_exp_REWRS:
  !uo.
  (!w1 w2. (bir_bin_exp uo (Imm128 w1) (Imm128 w2) = Imm128 (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm64  w1) (Imm64  w2) = Imm64  (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm32  w1) (Imm32  w2) = Imm32  (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm16  w1) (Imm16  w2) = Imm16  (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm8   w1) (Imm8   w2) = Imm8   (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm1   w1) (Imm1   w2) = Imm1   (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bir_imm r1 <> type_of_bir_imm r2) ==>
           (bir_bin_exp uo r1 r2 = ARB))
Proof
GEN_TAC >>
SIMP_TAC std_ss [bir_bin_exp_def] >>
REPEAT Cases >> (
  SIMP_TAC std_ss [bir_bin_exp_def, type_of_bir_imm_def]
)
QED

Theorem type_of_bir_bin_exp:
  !oper_r r1 r2. (type_of_bir_imm r1 = type_of_bir_imm r2) ==>
    (type_of_bir_imm (bir_bin_exp oper_r r1 r2) = type_of_bir_imm r1)
Proof
REPEAT Cases >>
SIMP_TAC (srw_ss()) [type_of_bir_imm_def, bir_bin_exp_REWRS]
QED



(* ------------------------------------------------------------------------- *)
(*  Binary predicates                                                        *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_bin_pred_t =
  | BIExp_Equal
  | BIExp_NotEqual
  | BIExp_LessThan
  | BIExp_SignedLessThan
  | BIExp_LessOrEqual
  | BIExp_SignedLessOrEqual
End

Definition bir_bin_pred_GET_OPER_def:
  (bir_bin_pred_GET_OPER BIExp_Equal = $=) /\
   (bir_bin_pred_GET_OPER BIExp_NotEqual = $<>) /\
   (bir_bin_pred_GET_OPER BIExp_LessThan = word_lo) /\
   (bir_bin_pred_GET_OPER BIExp_SignedLessThan = word_lt) /\
   (bir_bin_pred_GET_OPER BIExp_LessOrEqual = word_ls) /\
   (bir_bin_pred_GET_OPER BIExp_SignedLessOrEqual = word_le)
End

Definition bir_bin_pred_def:
  (bir_bin_pred uo (Imm128 w1) (Imm128 w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm64  w1) (Imm64  w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm32  w1) (Imm32  w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm16  w1) (Imm16  w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm8   w1) (Imm8   w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm1   w1) (Imm1   w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo _ _ = F)
End

Theorem bir_bin_pred_REWRS:
  !uo.
  (!w1 w2. (bir_bin_pred uo (Imm128 w1) (Imm128 w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm64  w1) (Imm64  w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm32  w1) (Imm32  w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm16  w1) (Imm16  w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm8   w1) (Imm8   w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm1   w1) (Imm1   w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bir_imm r1 <> type_of_bir_imm r2) ==>
     (bir_bin_pred uo r1 r2 = F))
Proof
GEN_TAC >>
SIMP_TAC std_ss [bir_bin_pred_def] >>
REPEAT Cases >> (
  SIMP_TAC (srw_ss()) [type_of_bir_imm_def, bir_bin_pred_def]
)
QED


Theorem bir_bin_pred_Equal_REWR:
  !b1 b2. (bir_bin_pred BIExp_Equal b1 b2) <=> (b1 = b2)
Proof
REPEAT Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_bin_pred_def, bir_bin_pred_GET_OPER_def]
)
QED

Theorem bir_bin_pred_NotEqual_REWR:
  !b1 b2. (bir_bin_pred BIExp_NotEqual b1 b2) <=>
          ((type_of_bir_imm b1 = type_of_bir_imm b2) /\ (b1 <> b2))
Proof
REPEAT Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_bin_pred_def, bir_bin_pred_GET_OPER_def,
    type_of_bir_imm_def]
)
QED


(* ------------------------------------------------------------------------- *)
(*  Casts                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ============= *)
(* Cast          *)
(* ============= *)

Definition bir_cast_def:
  bir_cast r s = n2bs (b2n r) s
End

Theorem bir_cast_REWRS0_aux[local]:
  !s1 s (w:'a word).
  (size_of_bir_immtype s1 = dimindex (:'a)) ==>
  (bir_cast (w2bs w s1) s = w2bs w s)
Proof
SIMP_TAC std_ss [bir_cast_def, w2bs_def, b2n_n2bs, w2n_MOD_2EXP_ID]
QED

Theorem bir_cast_REWRS0 = REWRITE_RULE [w2bs_REWRS, w2w_id] (LIST_CONJ (MP_size_of_bir_immtype_t_EQ_dimindex
     bir_cast_REWRS0_aux))


Theorem bir_cast_REWRS = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [bir_immtype_t_ty])
    [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] bir_cast_REWRS0



(* ============= *)
(* lcast         *)
(* ============= *)

Definition bir_lcast_def:
  bir_lcast = bir_cast
End

Theorem bir_lcast_REWRS0 = REWRITE_RULE [GSYM bir_lcast_def] bir_cast_REWRS0


Theorem bir_lcast_REWRS = REWRITE_RULE [GSYM bir_lcast_def] bir_cast_REWRS




(* ============= *)
(* hcast         *)
(* ============= *)

Definition bir_hcast_def:
  bir_hcast r s =
  n2bs (DIV_2EXP ((size_of_bir_immtype (type_of_bir_imm r) - (size_of_bir_immtype s))) (b2n r)) s
End

Definition w2wh_def:
  w2wh (w : 'a word) = (word_extract (dimindex (:'a) - 1) (dimindex (:'a) - dimindex (:'b)) w) :'b word
End

Theorem w2wh_id:
  !w. w2wh (w : 'a word) = w
Proof
SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def,
  INST_TYPE [beta |-> alpha] wordsTheory.EXTRACT_ALL_BITS, w2w_id]
QED

Theorem w2wh_w2w:
  !w.
  (dimindex (:'a) <= dimindex (:'b)) ==> ((w2wh (w : 'a word) : 'b word) = w2w w)
Proof
REPEAT STRIP_TAC >>
`(dimindex (:'a) - dimindex (:'b)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def, WORD_w2w_EXTRACT]
QED


Theorem w2n_w2wh:
  !w:'a word.
    w2n ((w2wh w):'b word) =
    (DIV_2EXP (dimindex (:'a) - dimindex (:'b)) (w2n w))
Proof
REPEAT STRIP_TAC >>
`0 < dimindex (:'a)` by METIS_TAC[wordsTheory.DIMINDEX_GT_0] >>
`0 < dimindex (:'b)` by METIS_TAC[wordsTheory.DIMINDEX_GT_0] >>
SIMP_TAC arith_ss [w2wh_def, bitTheory.DIV_2EXP_def, GSYM wordsTheory.w2n_lsr,
  wordsTheory.word_lsr_n2w, word_extract_bits_w2w, w2n_n2w, w2w_def] >>

`w2n ((dimindex (:'a) - 1 -- dimindex (:'a) - dimindex (:'b)) w) < dimword (:'b)`
  suffices_by SIMP_TAC arith_ss [] >>

`w2n ((dimindex (:'a) - 1 -- dimindex (:'a) - dimindex (:'b)) w) < 2**
    (SUC (dimindex (:'a) - 1) - (dimindex (:'a) - dimindex (:'b)))` by
  METIS_TAC[wordsTheory.WORD_BITS_LT] >>

`SUC (dimindex (:'a) - 1) - (dimindex (:'a) - dimindex (:'b)) <= dimindex (:'b)` by
  DECIDE_TAC >>

ASM_SIMP_TAC arith_ss [wordsTheory.dimword_def] >>
METIS_TAC[bitTheory.TWOEXP_MONO2, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED



Theorem bir_hcast_REWRS_aux[local]:
  !s1 s2 (w:'a word).
  (size_of_bir_immtype s1 = dimindex (:'a)) ==>
  (size_of_bir_immtype s2 = dimindex (:'b)) ==>
  (bir_hcast (w2bs w s1) s2 = w2bs ((w2wh w):'b word) s2)
Proof
SIMP_TAC std_ss [bir_hcast_def, type_of_w2bs, w2bs_def, w2n_w2wh,
  b2n_n2bs, w2n_MOD_2EXP_ID]
QED


val bir_hcast_REWRS = save_thm ("bir_hcast_REWRS", let
  val thms0 = MP_size_of_bir_immtype_t_EQ_dimindex bir_hcast_REWRS_aux
  val thms1 = flatten (map (MP_size_of_bir_immtype_t_EQ_dimindex) thms0)
  val thm0 = LIST_CONJ thms1
  val thm1 = SIMP_RULE (std_ss++wordsLib.WORD_ss)
    [GSYM CONJ_ASSOC, w2bs_REWRS, w2wh_id, w2w_id, w2wh_w2w] thm0
in
  thm1
end);



(* ============= *)
(* scast         *)
(* ============= *)

Definition bir_scast_def:
  bir_scast r s =
  n2bs (if (type_of_bir_imm r = Bit1) then (b2n r) else
     (SIGN_EXTEND (size_of_bir_immtype (type_of_bir_imm r))
                  (size_of_bir_immtype s) (b2n r))) s
End


Theorem bir_scast_REWRS_aux[local]:
  !s1 s2 (w:'a word).
  (size_of_bir_immtype s1 = dimindex (:'a)) ==>
  (size_of_bir_immtype s2 = dimindex (:'b)) ==>
  (bir_scast (w2bs w s1) s2 = w2bs (if (s1 = Bit1) then (w2w w) else (sw2sw w):'b word) s2)
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_scast_def, type_of_w2bs, w2bs_def, w2w_def,
  b2n_n2bs, w2n_MOD_2EXP_ID, wordsTheory.sw2sw_def, w2n_n2w, wordsTheory.dimword_def,
  GSYM bitTheory.MOD_2EXP_def] >>
METIS_TAC[n2bs_MOD_size_of_bir_immtype]
QED


val bir_scast_REWRS = save_thm ("bir_scast_REWRS", let
  val thms0 = MP_size_of_bir_immtype_t_EQ_dimindex bir_scast_REWRS_aux
  val thms1 = flatten (map (MP_size_of_bir_immtype_t_EQ_dimindex) thms0)
  val thm0 = LIST_CONJ thms1
  val thm1 = SIMP_RULE (std_ss++wordsLib.WORD_ss++bir_imm_ss)
    [GSYM CONJ_ASSOC, w2bs_REWRS, sw2sw_id, w2w_id, sw2sw_w2w_downcast] thm0
in
  thm1
end);



(* ============= *)
(* combination   *)
(* ============= *)

Datatype:
  bir_cast_t =
  | BIExp_UnsignedCast
  | BIExp_SignedCast
  | BIExp_HighCast
  | BIExp_LowCast
End

Definition bir_gencast_def:
  (bir_gencast BIExp_UnsignedCast = bir_cast) /\
  (bir_gencast BIExp_SignedCast = bir_scast) /\
  (bir_gencast BIExp_HighCast = bir_hcast) /\
  (bir_gencast BIExp_LowCast = bir_lcast)
End

Theorem bir_casts_DEFS = LIST_CONJ [bir_cast_def, bir_scast_def, bir_hcast_def, bir_lcast_def]


Theorem bir_casts_REWRS = LIST_CONJ [bir_cast_REWRS, bir_scast_REWRS, bir_hcast_REWRS, bir_lcast_REWRS]



Theorem type_of_bir_gencast:
  !ct b s. type_of_bir_imm (bir_gencast ct b s) = s
Proof
Cases >> SIMP_TAC std_ss [bir_gencast_def, bir_casts_DEFS, type_of_n2bs]
QED


Theorem bir_gencast_ID:
  !ct b s. (type_of_bir_imm b = s) ==> ((bir_gencast ct b s) = b)
Proof
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_gencast_def, bir_casts_REWRS, type_of_bir_imm_def]
)
QED


val bir_casts_list = TypeBase.constructors_of ``:bir_cast_t``;

fun inst_CONJ_THM tms thm =
  REWRITE_RULE [GSYM CONJ_ASSOC] (LIST_CONJ (map (fn t => SPEC t thm) tms));

Theorem bir_casts_ID = REWRITE_RULE [bir_gencast_def] (
  inst_CONJ_THM bir_casts_list bir_gencast_ID)


Theorem type_of_bir_casts = REWRITE_RULE [bir_gencast_def] (
   inst_CONJ_THM bir_casts_list type_of_bir_gencast)



Theorem bir_casts_Bit1:
  !ct b c. (type_of_bir_imm b = Bit1) ==>
             (bir_gencast ct b c = bir_cast b c)
Proof
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_casts_REWRS, bir_gencast_def, type_of_bir_imm_def]
)
QED


val _ = export_theory();
