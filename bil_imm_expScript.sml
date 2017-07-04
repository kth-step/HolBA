(* ========================================================================= *)
(* FILE          : bilScript.sml                                             *)
(* DESCRIPTION   : A model of immediate expressions                          *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory;

val _ = new_theory "bil_imm_exp";

val bil_imm_ss = rewrites ((type_rws ``:bil_imm_t``) @ (type_rws ``:bil_immtype_t``));


(* ------------------------------------------------------------------------- *)
(*  Unary expressions                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_unary_exp_t =
  | BIExp_ChangeSign
  | BIExp_Not`;

val bil_unary_exp_GET_OPER_def = Define
  `(bil_unary_exp_GET_OPER BIExp_Not = word_1comp) /\
   (bil_unary_exp_GET_OPER BiExp_ChangeSign = word_2comp)`;

val bil_unary_exp_def = Define `
  (bil_unary_exp uo (Imm64 w) = Imm64 (bil_unary_exp_GET_OPER uo w)) /\
  (bil_unary_exp uo (Imm32 w) = Imm32 (bil_unary_exp_GET_OPER uo w)) /\
  (bil_unary_exp uo (Imm16 w) = Imm16 (bil_unary_exp_GET_OPER uo w)) /\
  (bil_unary_exp uo (Imm8 w)  = Imm8  (bil_unary_exp_GET_OPER uo w)) /\
  (bil_unary_exp uo (Imm1 w)  = Imm1  (bil_unary_exp_GET_OPER uo w))`;

val bil_unary_exp_REWRS = store_thm ("bil_unary_exp_REWRS", ``!uo.
  (!w. (bil_unary_exp uo (Imm1 w)  = Imm1  (bil_unary_exp_GET_OPER uo w))) /\
  (!w. (bil_unary_exp uo (Imm8 w)  = Imm8  (bil_unary_exp_GET_OPER uo w))) /\
  (!w. (bil_unary_exp uo (Imm16 w) = Imm16 (bil_unary_exp_GET_OPER uo w))) /\
  (!w. (bil_unary_exp uo (Imm32 w) = Imm32 (bil_unary_exp_GET_OPER uo w))) /\
  (!w. (bil_unary_exp uo (Imm64 w) = Imm64 (bil_unary_exp_GET_OPER uo w)))``,
SIMP_TAC std_ss [bil_unary_exp_def]);


val type_of_bil_unary_exp = store_thm ("type_of_bil_unary_exp",
  ``!uo r. type_of_bil_imm (bil_unary_exp uo r) = type_of_bil_imm r``,
GEN_TAC >> Cases >> (
  SIMP_TAC std_ss [type_of_bil_imm_def, bil_unary_exp_def]
));


(* Instantiate everything *)
val bil_not_def = Define `bil_not = bil_unary_exp BIExp_Not`
val bil_neg_def = Define `bil_neg = bil_unary_exp BIExp_ChangeSign`

val bil_unary_exps_DEFS = save_thm ("bil_unary_exps_DEFS",
  LIST_CONJ [bil_not_def, bil_neg_def]);


val bil_unary_exp_list = TypeBase.constructors_of ``:bil_unary_exp_t``;

fun inst_CONJ_THM tms thm =
  REWRITE_RULE [GSYM CONJ_ASSOC] (LIST_CONJ (map (fn t => SPEC t thm) tms));

val type_of_bil_unary_exps = save_thm ("type_of_bil_unary_exps",
SIMP_RULE (std_ss) [GSYM bil_unary_exps_DEFS] (
  inst_CONJ_THM bil_unary_exp_list type_of_bil_unary_exp));

val bil_unary_exps_REWRS = save_thm ("bil_unary_exps_REWRS",
SIMP_RULE std_ss [GSYM bil_unary_exps_DEFS, bil_unary_exp_GET_OPER_def] (
  inst_CONJ_THM bil_unary_exp_list bil_unary_exp_REWRS));



(* ------------------------------------------------------------------------- *)
(*  Binary expressions                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_bin_exp_t =
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
  | BIExp_SignedRightShift`;

val bil_bin_exp_GET_OPER_def = Define
  `(bil_bin_exp_GET_OPER BIExp_And = word_and) /\
   (bil_bin_exp_GET_OPER BIExp_Or = word_or) /\
   (bil_bin_exp_GET_OPER BIExp_Xor = word_xor) /\
   (bil_bin_exp_GET_OPER BIExp_Plus = $+) /\
   (bil_bin_exp_GET_OPER BIExp_Minus = $-) /\
   (bil_bin_exp_GET_OPER BIExp_Mult = $*) /\
   (bil_bin_exp_GET_OPER BIExp_Div = $//) /\
   (bil_bin_exp_GET_OPER BIExp_SignedDiv = $/) /\
   (bil_bin_exp_GET_OPER BIExp_Mod =  word_mod) /\
   (bil_bin_exp_GET_OPER BIExp_SignedMod = word_smod) /\
   (bil_bin_exp_GET_OPER BIExp_LeftShift = word_lsl_bv) /\
   (bil_bin_exp_GET_OPER BIExp_RightShift = word_lsr_bv) /\
   (bil_bin_exp_GET_OPER BIExp_SignedRightShift = word_asr_bv) /\
   (bil_bin_exp_GET_OPER _ = ARB) (* Should never fire *)`;

val bil_bin_exp_def = Define `
  (bil_bin_exp uo (Imm64 w1) (Imm64 w2) = Imm64 (bil_bin_exp_GET_OPER uo w1 w2)) /\
  (bil_bin_exp uo (Imm32 w1) (Imm32 w2) = Imm32 (bil_bin_exp_GET_OPER uo w1 w2)) /\
  (bil_bin_exp uo (Imm16 w1) (Imm16 w2) = Imm16 (bil_bin_exp_GET_OPER uo w1 w2)) /\
  (bil_bin_exp uo (Imm8  w1) (Imm8  w2) = Imm8  (bil_bin_exp_GET_OPER uo w1 w2)) /\
  (bil_bin_exp uo (Imm1  w1) (Imm1  w2) = Imm1  (bil_bin_exp_GET_OPER uo w1 w2)) /\
  (bil_bin_exp uo _ _ = ARB)`

val bil_bin_exp_REWRS = store_thm ("bil_bin_exp_REWRS", ``!uo.
  (!w1 w2. (bil_bin_exp uo (Imm64 w1) (Imm64 w2) = Imm64 (bil_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_exp uo (Imm32 w1) (Imm32 w2) = Imm32 (bil_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_exp uo (Imm16 w1) (Imm16 w2) = Imm16 (bil_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_exp uo (Imm8  w1) (Imm8  w2) = Imm8  (bil_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_exp uo (Imm1  w1) (Imm1  w2) = Imm1  (bil_bin_exp_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bil_imm r1 <> type_of_bil_imm r2) ==>
           (bil_bin_exp uo r1 r2 = ARB))``,

GEN_TAC >>
SIMP_TAC std_ss [bil_bin_exp_def] >>
REPEAT Cases >> (
  SIMP_TAC std_ss [bil_bin_exp_def, type_of_bil_imm_def]
));

val type_of_bil_bin_exp = store_thm ("type_of_bil_bin_exp",
  ``!oper_r r1 r2. (type_of_bil_imm r1 = type_of_bil_imm r2) ==>
    (type_of_bil_imm (bil_bin_exp oper_r r1 r2) = type_of_bil_imm r1)``,
REPEAT Cases >>
SIMP_TAC (srw_ss()) [type_of_bil_imm_def, bil_bin_exp_REWRS]);


val bil_add_def  = Define `bil_add  = bil_bin_exp BIExp_Plus`;
val bil_sub_def  = Define `bil_sub  = bil_bin_exp BIExp_Minus`;
val bil_mul_def  = Define `bil_mul  = bil_bin_exp BIExp_Mult`;
val bil_div_def  = Define `bil_div  = bil_bin_exp BIExp_Div`;
val bil_sdiv_def = Define `bil_sdiv = bil_bin_exp BIExp_SignedDiv`;
val bil_mod_def  = Define `bil_mod  = bil_bin_exp BIExp_Mod`
val bil_smod_def = Define `bil_smod = bil_bin_exp BIExp_SignedMod`
val bil_lsl_def  = Define `bil_lsl  = bil_bin_exp BIExp_LeftShift`
val bil_lsr_def  = Define `bil_lsr  = bil_bin_exp BIExp_RightShift`
val bil_asr_def  = Define `bil_asr  = bil_bin_exp BIExp_SignedRightShift`
val bil_and_def  = Define `bil_and  = bil_bin_exp BIExp_And`
val bil_or_def   = Define `bil_or   = bil_bin_exp BIExp_Or`
val bil_xor_def  = Define `bil_xor  = bil_bin_exp BIExp_Xor`;

val bil_bin_exps_DEFS = save_thm ("bil_bin_exps_DEFS",
  LIST_CONJ [bil_add_def, bil_sub_def, bil_mul_def, bil_div_def, bil_sdiv_def,
     bil_mod_def, bil_smod_def, bil_lsl_def, bil_lsr_def, bil_asr_def, bil_and_def,
     bil_or_def, bil_xor_def]);

val bil_bin_exp_list = TypeBase.constructors_of ``:bil_bin_exp_t``;

val type_of_bil_bin_exps = save_thm ("type_of_bil_bin_exps",
REWRITE_RULE [GSYM bil_bin_exps_DEFS] (
  inst_CONJ_THM bil_bin_exp_list type_of_bil_bin_exp));

val bil_bin_exps_REWRS = save_thm ("bil_bin_exps_REWRS",
SIMP_RULE (std_ss) [GSYM bil_bin_exps_DEFS, bil_bin_exp_GET_OPER_def] (
  inst_CONJ_THM bil_bin_exp_list bil_bin_exp_REWRS));


(* ------------------------------------------------------------------------- *)
(*  Binary predicates                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_bin_pred_t =
  | BIExp_Equal
  | BIExp_NotEqual
  | BIExp_LessThan
  | BIExp_SignedLessThan
  | BIExp_LessOrEqual
  | BIExp_SignedLessOrEqual`;

val bil_bin_pred_GET_OPER_def = Define
  `(bil_bin_pred_GET_OPER BIExp_Equal = $=) /\
   (bil_bin_pred_GET_OPER BIExp_NotEqual = $<>) /\
   (bil_bin_pred_GET_OPER BIExp_LessThan = word_lo) /\
   (bil_bin_pred_GET_OPER BIExp_SignedLessThan = word_lt) /\
   (bil_bin_pred_GET_OPER BIExp_LessOrEqual = word_ls) /\
   (bil_bin_pred_GET_OPER BIExp_SignedLessOrEqual = word_le)`;

val bil_bin_pred_def = Define `
  (bil_bin_pred uo (Imm64 w1) (Imm64 w2) = (bil_bin_pred_GET_OPER uo w1 w2)) /\
  (bil_bin_pred uo (Imm32 w1) (Imm32 w2) = (bil_bin_pred_GET_OPER uo w1 w2)) /\
  (bil_bin_pred uo (Imm16 w1) (Imm16 w2) = (bil_bin_pred_GET_OPER uo w1 w2)) /\
  (bil_bin_pred uo (Imm8  w1) (Imm8  w2) = (bil_bin_pred_GET_OPER uo w1 w2)) /\
  (bil_bin_pred uo (Imm1  w1) (Imm1  w2) = (bil_bin_pred_GET_OPER uo w1 w2)) /\
  (bil_bin_pred uo _ _ = F)`;

val bil_bin_pred_REWRS = store_thm ("bil_bin_pred_REWRS", ``!uo.
  (!w1 w2. (bil_bin_pred uo (Imm64 w1) (Imm64 w2) = (bil_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_pred uo (Imm32 w1) (Imm32 w2) = (bil_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_pred uo (Imm16 w1) (Imm16 w2) = (bil_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_pred uo (Imm8  w1) (Imm8  w2) = (bil_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bil_bin_pred uo (Imm1  w1) (Imm1  w2) = (bil_bin_pred_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bil_imm r1 <> type_of_bil_imm r2) ==>
     (bil_bin_pred uo r1 r2 = F))``,

GEN_TAC >>
SIMP_TAC std_ss [bil_bin_pred_def] >>
REPEAT Cases >> (
  SIMP_TAC (srw_ss()) [type_of_bil_imm_def, bil_bin_pred_def]
));

val bil_eq_def  = Define `bil_eq  = bil_bin_pred BIExp_Equal`
val bil_neq_def = Define `bil_neq = bil_bin_pred BIExp_NotEqual`
val bil_lt_def  = Define `bil_lt  = bil_bin_pred BIExp_SignedLessThan`
val bil_le_def  = Define `bil_le  = bil_bin_pred BIExp_SignedLessOrEqual`
val bil_ult_def = Define `bil_ult = bil_bin_pred BIExp_LessThan`
val bil_ule_def = Define `bil_ule = bil_bin_pred BIExp_LessOrEqual`

val bil_bin_preds_DEFS = save_thm ("bil_bin_preds_DEFS",
  LIST_CONJ [bil_eq_def, bil_neq_def, bil_lt_def, bil_le_def, bil_ult_def,
     bil_ule_def]);

val bil_bin_pred_list = TypeBase.constructors_of ``:bil_bin_pred_t``;

val bil_bin_preds_REWRS = save_thm ("bil_bin_preds_REWRS",
SIMP_RULE (std_ss) [GSYM bil_bin_preds_DEFS, bil_bin_pred_GET_OPER_def] (
  inst_CONJ_THM bil_bin_pred_list bil_bin_pred_REWRS));



(* ------------------------------------------------------------------------- *)
(*  Casts                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ============= *)
(* Cast          *)
(* ============= *)

val bil_cast_def = Define `bil_cast r s = n2bs (b2n r) s`

val bil_cast_REWRS = store_thm ("bil_cast_REWRS", ``
     (!w. bil_cast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bil_cast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bil_cast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bil_cast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bil_cast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bil_cast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_cast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_cast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_cast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_cast (Imm8  w) Bit1  = Imm1  (w2w w))
  /\ (!w. bil_cast (Imm8  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_cast (Imm8  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_cast (Imm8  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_cast (Imm16 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bil_cast (Imm16 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_cast (Imm16 w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_cast (Imm16 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_cast (Imm32 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bil_cast (Imm32 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_cast (Imm32 w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_cast (Imm32 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_cast (Imm64 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bil_cast (Imm64 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_cast (Imm64 w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_cast (Imm64 w) Bit32 = Imm32 (w2w w))
``,
SIMP_TAC std_ss [bil_cast_def, b2n_def, n2bs_def, GSYM w2w_def, w2w_id])


(* ============= *)
(* lcast         *)
(* ============= *)

val bil_lcast_def = Define `bil_lcast = bil_cast`;

val bil_lcast_REWRS = save_thm ("bil_lcast_REWRS",
  REWRITE_RULE [GSYM bil_lcast_def] bil_cast_REWRS);



(* ============= *)
(* hcast         *)
(* ============= *)

val bil_hcast_def = Define `bil_hcast r s =
  n2bs (DIV_2EXP ((size_of_bil_immtype (type_of_bil_imm r) - (size_of_bil_immtype s))) (b2n r)) s`;

val w2wh_def = Define `w2wh (w : 'a word) = (word_extract (dimindex (:'a) - 1) (dimindex (:'a) - dimindex (:'b)) w) :'b word`;

val w2wh_id = store_thm ("w2wh_id", ``!w. w2wh (w : 'a word) = w``,
SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def,
  INST_TYPE [beta |-> alpha] wordsTheory.EXTRACT_ALL_BITS, w2w_id]);

val w2wh_w2w = store_thm ("w2wh_w2w", ``!w.
  (dimindex (:'a) <= dimindex (:'b)) ==> ((w2wh (w : 'a word) : 'b word) = w2w w)``,

REPEAT STRIP_TAC >>
`(dimindex (:'a) - dimindex (:'b)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def, WORD_w2w_EXTRACT]);


val bil_hcast_REWRS0 = store_thm ("bil_hcast_REWRS0", ``
     (!w. bil_hcast (Imm1  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm1  w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm1  w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm1  w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bil_hcast (Imm1  w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit64 = Imm64 (w2wh w))
``,

Q.ABBREV_TAC `MY_POW = \x. 2 ** x` >>
`MY_POW 0 = 1` by (UNABBREV_ALL_TAC >> ASM_SIMP_TAC std_ss []) >>
ASM_SIMP_TAC std_ss [bil_hcast_def, bitTheory.DIV_2EXP_def] >>
ASM_SIMP_TAC (std_ss++bil_imm_ss++wordsLib.WORD_ss) [w2wh_def, n2bs_def,
  b2n_def, size_of_bil_immtype_def, type_of_bil_imm_def, n2w_w2n] >>
REPEAT CONJ_TAC >> Cases >> (
  FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [word_extract_mask, w2n_n2w] >>
  blastLib.BBLAST_TAC >>
  UNABBREV_ALL_TAC >> BETA_TAC >>
  ASM_SIMP_TAC arith_ss [bitTheory.BIT_SHIFT_THM4, bitTheory.NOT_BIT_GT_TWOEXP] >>
  METIS_TAC[]
));


val bil_hcast_REWRS = store_thm ("bil_hcast_REWRS", ``
  (* Not very casts *)
     (!w. bil_hcast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bil_hcast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bil_hcast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bil_hcast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bil_hcast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bil_hcast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_hcast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_hcast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_hcast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_hcast (Imm8  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm8  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_hcast (Imm8  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_hcast (Imm8  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_hcast (Imm16 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm16 w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_hcast (Imm16 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_hcast (Imm32 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm32 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_hcast (Imm64 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bil_hcast (Imm64 w) Bit32 = Imm32 (w2wh w))
``,

SIMP_TAC (std_ss++wordsLib.WORD_ss) [bil_hcast_REWRS0, w2wh_id,
 w2wh_w2w]);


(* ============= *)
(* scast         *)
(* ============= *)

val bil_scast_def = Define `bil_scast r s =
  n2bs (if (type_of_bil_imm r = Bit1) then (b2n r) else
     (SIGN_EXTEND (size_of_bil_immtype (type_of_bil_imm r))
                  (size_of_bil_immtype s) (b2n r))) s`;

val bil_scast_REWRS0 = store_thm ("bil_scast_REWRS0", ``
     (!w. bil_scast (Imm1  w) Bit1  = Imm1  (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_scast (Imm8  w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit64 = Imm64 (sw2sw w))
``,
SIMP_TAC (std_ss++bil_imm_ss++wordsLib.WORD_ss) [
  bil_scast_def, n2bs_def, sw2sw_def,
  size_of_bil_immtype_def, type_of_bil_imm_def, b2n_def, GSYM w2w_def]);


val bil_scast_REWRS = store_thm ("bil_scast_REWRS", ``
  (* Indentity *)
     (!w. bil_scast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bil_scast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bil_scast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bil_scast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bil_scast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bil_scast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bil_scast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bil_scast (Imm8  w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm8  w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bil_scast (Imm16 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm32 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bil_scast (Imm64 w) Bit32 = Imm32 (sw2sw w))
``,
SIMP_TAC (std_ss) [bil_scast_REWRS0, w2w_id, sw2sw_id]);


(* ============= *)
(* combination   *)
(* ============= *)

val _ = Datatype `bil_cast_t =
  | BIExp_UnsignedCast
  | BIExp_SignedCast
  | BIExp_HighCast
  | BIExp_LowCast`;

val bil_gencast_def = Define `
  (bil_gencast BIExp_UnsignedCast = bil_cast) /\
  (bil_gencast BIExp_SignedCast = bil_scast) /\
  (bil_gencast BIExp_HighCast = bil_hcast) /\
  (bil_gencast BIExp_LowCast = bil_lcast)`;

val bil_casts_DEFS = save_thm ("bil_casts_DEFS",
  LIST_CONJ [bil_cast_def, bil_scast_def, bil_hcast_def, bil_lcast_def]);

val bil_casts_REWRS = save_thm ("bil_casts_REWRS",
  LIST_CONJ [bil_cast_REWRS, bil_scast_REWRS, bil_hcast_REWRS, bil_lcast_REWRS]);


val type_of_bil_gencast = store_thm ("type_of_bil_gencast",
  ``!ct b s. type_of_bil_imm (bil_gencast ct b s) = s``,
Cases >> SIMP_TAC std_ss [bil_gencast_def, bil_casts_DEFS, type_of_n2bs]);


val bil_gencast_ID = store_thm ("bil_gencast_ID",
  ``!ct b s. (type_of_bil_imm b = s) ==> ((bil_gencast ct b s) = b)``,
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bil_imm_ss) [bil_gencast_def, bil_casts_REWRS, type_of_bil_imm_def]
));


val bil_casts_list = TypeBase.constructors_of ``:bil_cast_t``;

val bil_casts_ID = save_thm ("bil_casts_ID",
REWRITE_RULE [bil_gencast_def] (
  inst_CONJ_THM bil_casts_list bil_gencast_ID));

val type_of_bil_casts = save_thm ("type_of_bil_casts",
REWRITE_RULE [bil_gencast_def] (
   inst_CONJ_THM bil_casts_list type_of_bil_gencast));


val bil_casts_Bit1 = store_thm ("bil_casts_Bit1",
  ``!ct b c. (type_of_bil_imm b = Bit1) ==>
             (bil_gencast ct b c = bil_cast b c)``,
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bil_imm_ss) [bil_casts_REWRS, bil_gencast_def, type_of_bil_imm_def]
));


val _ = export_theory();
