open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory;

val _ = new_theory "bir_imm_exp";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));


(* ------------------------------------------------------------------------- *)
(*  Unary expressions                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_unary_exp_t =
  | BIExp_ChangeSign
  | BIExp_Not`;

val bir_unary_exp_GET_OPER_def = Define
  `(bir_unary_exp_GET_OPER BIExp_Not = word_1comp) /\
   (bir_unary_exp_GET_OPER BiExp_ChangeSign = word_2comp)`;

val bir_unary_exp_def = Define `
  (bir_unary_exp uo (Imm64 w) = Imm64 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm32 w) = Imm32 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm16 w) = Imm16 (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm8 w)  = Imm8  (bir_unary_exp_GET_OPER uo w)) /\
  (bir_unary_exp uo (Imm1 w)  = Imm1  (bir_unary_exp_GET_OPER uo w))`;

val bir_unary_exp_REWRS = store_thm ("bir_unary_exp_REWRS", ``!uo.
  (!w. (bir_unary_exp uo (Imm1 w)  = Imm1  (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm8 w)  = Imm8  (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm16 w) = Imm16 (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm32 w) = Imm32 (bir_unary_exp_GET_OPER uo w))) /\
  (!w. (bir_unary_exp uo (Imm64 w) = Imm64 (bir_unary_exp_GET_OPER uo w)))``,
SIMP_TAC std_ss [bir_unary_exp_def]);


val type_of_bir_unary_exp = store_thm ("type_of_bir_unary_exp",
  ``!uo r. type_of_bir_imm (bir_unary_exp uo r) = type_of_bir_imm r``,
GEN_TAC >> Cases >> (
  SIMP_TAC std_ss [type_of_bir_imm_def, bir_unary_exp_def]
));


(* Instantiate everything *)
val bir_not_def = Define `bir_not = bir_unary_exp BIExp_Not`
val bir_neg_def = Define `bir_neg = bir_unary_exp BIExp_ChangeSign`

val bir_unary_exps_DEFS = save_thm ("bir_unary_exps_DEFS",
  LIST_CONJ [bir_not_def, bir_neg_def]);


val bir_unary_exp_list = TypeBase.constructors_of ``:bir_unary_exp_t``;

fun inst_CONJ_THM tms thm =
  REWRITE_RULE [GSYM CONJ_ASSOC] (LIST_CONJ (map (fn t => SPEC t thm) tms));

val type_of_bir_unary_exps = save_thm ("type_of_bir_unary_exps",
SIMP_RULE (std_ss) [GSYM bir_unary_exps_DEFS] (
  inst_CONJ_THM bir_unary_exp_list type_of_bir_unary_exp));

val bir_unary_exps_REWRS = save_thm ("bir_unary_exps_REWRS",
SIMP_RULE std_ss [GSYM bir_unary_exps_DEFS, bir_unary_exp_GET_OPER_def] (
  inst_CONJ_THM bir_unary_exp_list bir_unary_exp_REWRS));



(* ------------------------------------------------------------------------- *)
(*  Binary expressions                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_bin_exp_t =
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

val bir_bin_exp_GET_OPER_def = Define
  `(bir_bin_exp_GET_OPER BIExp_And = word_and) /\
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
   (bir_bin_exp_GET_OPER _ = ARB) (* Should never fire *)`;

val bir_bin_exp_def = Define `
  (bir_bin_exp uo (Imm64 w1) (Imm64 w2) = Imm64 (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm32 w1) (Imm32 w2) = Imm32 (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm16 w1) (Imm16 w2) = Imm16 (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm8  w1) (Imm8  w2) = Imm8  (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo (Imm1  w1) (Imm1  w2) = Imm1  (bir_bin_exp_GET_OPER uo w1 w2)) /\
  (bir_bin_exp uo _ _ = ARB)`

val bir_bin_exp_REWRS = store_thm ("bir_bin_exp_REWRS", ``!uo.
  (!w1 w2. (bir_bin_exp uo (Imm64 w1) (Imm64 w2) = Imm64 (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm32 w1) (Imm32 w2) = Imm32 (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm16 w1) (Imm16 w2) = Imm16 (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm8  w1) (Imm8  w2) = Imm8  (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_exp uo (Imm1  w1) (Imm1  w2) = Imm1  (bir_bin_exp_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bir_imm r1 <> type_of_bir_imm r2) ==>
           (bir_bin_exp uo r1 r2 = ARB))``,

GEN_TAC >>
SIMP_TAC std_ss [bir_bin_exp_def] >>
REPEAT Cases >> (
  SIMP_TAC std_ss [bir_bin_exp_def, type_of_bir_imm_def]
));

val type_of_bir_bin_exp = store_thm ("type_of_bir_bin_exp",
  ``!oper_r r1 r2. (type_of_bir_imm r1 = type_of_bir_imm r2) ==>
    (type_of_bir_imm (bir_bin_exp oper_r r1 r2) = type_of_bir_imm r1)``,
REPEAT Cases >>
SIMP_TAC (srw_ss()) [type_of_bir_imm_def, bir_bin_exp_REWRS]);


val bir_add_def  = Define `bir_add  = bir_bin_exp BIExp_Plus`;
val bir_sub_def  = Define `bir_sub  = bir_bin_exp BIExp_Minus`;
val bir_mul_def  = Define `bir_mul  = bir_bin_exp BIExp_Mult`;
val bir_div_def  = Define `bir_div  = bir_bin_exp BIExp_Div`;
val bir_sdiv_def = Define `bir_sdiv = bir_bin_exp BIExp_SignedDiv`;
val bir_mod_def  = Define `bir_mod  = bir_bin_exp BIExp_Mod`
val bir_smod_def = Define `bir_smod = bir_bin_exp BIExp_SignedMod`
val bir_lsl_def  = Define `bir_lsl  = bir_bin_exp BIExp_LeftShift`
val bir_lsr_def  = Define `bir_lsr  = bir_bin_exp BIExp_RightShift`
val bir_asr_def  = Define `bir_asr  = bir_bin_exp BIExp_SignedRightShift`
val bir_and_def  = Define `bir_and  = bir_bin_exp BIExp_And`
val bir_or_def   = Define `bir_or   = bir_bin_exp BIExp_Or`
val bir_xor_def  = Define `bir_xor  = bir_bin_exp BIExp_Xor`;

val bir_bin_exps_DEFS = save_thm ("bir_bin_exps_DEFS",
  LIST_CONJ [bir_add_def, bir_sub_def, bir_mul_def, bir_div_def, bir_sdiv_def,
     bir_mod_def, bir_smod_def, bir_lsl_def, bir_lsr_def, bir_asr_def, bir_and_def,
     bir_or_def, bir_xor_def]);

val bir_bin_exp_list = TypeBase.constructors_of ``:bir_bin_exp_t``;

val type_of_bir_bin_exps = save_thm ("type_of_bir_bin_exps",
REWRITE_RULE [GSYM bir_bin_exps_DEFS] (
  inst_CONJ_THM bir_bin_exp_list type_of_bir_bin_exp));

val bir_bin_exps_REWRS = save_thm ("bir_bin_exps_REWRS",
SIMP_RULE (std_ss) [GSYM bir_bin_exps_DEFS, bir_bin_exp_GET_OPER_def] (
  inst_CONJ_THM bir_bin_exp_list bir_bin_exp_REWRS));


(* ------------------------------------------------------------------------- *)
(*  Binary predicates                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_bin_pred_t =
  | BIExp_Equal
  | BIExp_NotEqual
  | BIExp_LessThan
  | BIExp_SignedLessThan
  | BIExp_LessOrEqual
  | BIExp_SignedLessOrEqual`;

val bir_bin_pred_GET_OPER_def = Define
  `(bir_bin_pred_GET_OPER BIExp_Equal = $=) /\
   (bir_bin_pred_GET_OPER BIExp_NotEqual = $<>) /\
   (bir_bin_pred_GET_OPER BIExp_LessThan = word_lo) /\
   (bir_bin_pred_GET_OPER BIExp_SignedLessThan = word_lt) /\
   (bir_bin_pred_GET_OPER BIExp_LessOrEqual = word_ls) /\
   (bir_bin_pred_GET_OPER BIExp_SignedLessOrEqual = word_le)`;

val bir_bin_pred_def = Define `
  (bir_bin_pred uo (Imm64 w1) (Imm64 w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm32 w1) (Imm32 w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm16 w1) (Imm16 w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm8  w1) (Imm8  w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo (Imm1  w1) (Imm1  w2) = (bir_bin_pred_GET_OPER uo w1 w2)) /\
  (bir_bin_pred uo _ _ = F)`;

val bir_bin_pred_REWRS = store_thm ("bir_bin_pred_REWRS", ``!uo.
  (!w1 w2. (bir_bin_pred uo (Imm64 w1) (Imm64 w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm32 w1) (Imm32 w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm16 w1) (Imm16 w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm8  w1) (Imm8  w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!w1 w2. (bir_bin_pred uo (Imm1  w1) (Imm1  w2) = (bir_bin_pred_GET_OPER uo w1 w2))) /\
  (!r1 r2. (type_of_bir_imm r1 <> type_of_bir_imm r2) ==>
     (bir_bin_pred uo r1 r2 = F))``,

GEN_TAC >>
SIMP_TAC std_ss [bir_bin_pred_def] >>
REPEAT Cases >> (
  SIMP_TAC (srw_ss()) [type_of_bir_imm_def, bir_bin_pred_def]
));

val bir_eq_def  = Define `bir_eq  = bir_bin_pred BIExp_Equal`
val bir_neq_def = Define `bir_neq = bir_bin_pred BIExp_NotEqual`
val bir_lt_def  = Define `bir_lt  = bir_bin_pred BIExp_SignedLessThan`
val bir_le_def  = Define `bir_le  = bir_bin_pred BIExp_SignedLessOrEqual`
val bir_ult_def = Define `bir_ult = bir_bin_pred BIExp_LessThan`
val bir_ule_def = Define `bir_ule = bir_bin_pred BIExp_LessOrEqual`

val bir_bin_preds_DEFS = save_thm ("bir_bin_preds_DEFS",
  LIST_CONJ [bir_eq_def, bir_neq_def, bir_lt_def, bir_le_def, bir_ult_def,
     bir_ule_def]);

val bir_bin_pred_list = TypeBase.constructors_of ``:bir_bin_pred_t``;

val bir_bin_preds_REWRS = save_thm ("bir_bin_preds_REWRS",
SIMP_RULE (std_ss) [GSYM bir_bin_preds_DEFS, bir_bin_pred_GET_OPER_def] (
  inst_CONJ_THM bir_bin_pred_list bir_bin_pred_REWRS));



(* ------------------------------------------------------------------------- *)
(*  Casts                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ============= *)
(* Cast          *)
(* ============= *)

val bir_cast_def = Define `bir_cast r s = n2bs (b2n r) s`

val bir_cast_REWRS = store_thm ("bir_cast_REWRS", ``
     (!w. bir_cast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bir_cast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bir_cast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bir_cast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bir_cast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bir_cast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_cast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_cast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_cast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_cast (Imm8  w) Bit1  = Imm1  (w2w w))
  /\ (!w. bir_cast (Imm8  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_cast (Imm8  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_cast (Imm8  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_cast (Imm16 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bir_cast (Imm16 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_cast (Imm16 w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_cast (Imm16 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_cast (Imm32 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bir_cast (Imm32 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_cast (Imm32 w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_cast (Imm32 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_cast (Imm64 w) Bit1  = Imm1  (w2w w))
  /\ (!w. bir_cast (Imm64 w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_cast (Imm64 w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_cast (Imm64 w) Bit32 = Imm32 (w2w w))
``,
SIMP_TAC std_ss [bir_cast_def, b2n_def, n2bs_def, GSYM w2w_def, w2w_id])


(* ============= *)
(* lcast         *)
(* ============= *)

val bir_lcast_def = Define `bir_lcast = bir_cast`;

val bir_lcast_REWRS = save_thm ("bir_lcast_REWRS",
  REWRITE_RULE [GSYM bir_lcast_def] bir_cast_REWRS);



(* ============= *)
(* hcast         *)
(* ============= *)

val bir_hcast_def = Define `bir_hcast r s =
  n2bs (DIV_2EXP ((size_of_bir_immtype (type_of_bir_imm r) - (size_of_bir_immtype s))) (b2n r)) s`;

val w2wh_def = Define `w2wh (w : 'a word) = (word_extract (dimindex (:'a) - 1) (dimindex (:'a) - dimindex (:'b)) w) :'b word`;

val w2wh_id = store_thm ("w2wh_id", ``!w. w2wh (w : 'a word) = w``,
SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def,
  INST_TYPE [beta |-> alpha] wordsTheory.EXTRACT_ALL_BITS, w2w_id]);

val w2wh_w2w = store_thm ("w2wh_w2w", ``!w.
  (dimindex (:'a) <= dimindex (:'b)) ==> ((w2wh (w : 'a word) : 'b word) = w2w w)``,

REPEAT STRIP_TAC >>
`(dimindex (:'a) - dimindex (:'b)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2wh_def, WORD_w2w_EXTRACT]);


val bir_hcast_REWRS0 = store_thm ("bir_hcast_REWRS0", ``
     (!w. bir_hcast (Imm1  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm1  w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm1  w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm1  w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bir_hcast (Imm1  w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit64 = Imm64 (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit32 = Imm32 (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit64 = Imm64 (w2wh w))
``,

Q.ABBREV_TAC `MY_POW = \x. 2 ** x` >>
`MY_POW 0 = 1` by (UNABBREV_ALL_TAC >> ASM_SIMP_TAC std_ss []) >>
ASM_SIMP_TAC std_ss [bir_hcast_def, bitTheory.DIV_2EXP_def] >>
ASM_SIMP_TAC (std_ss++bir_imm_ss++wordsLib.WORD_ss) [w2wh_def, n2bs_def,
  b2n_def, size_of_bir_immtype_def, type_of_bir_imm_def, n2w_w2n] >>
REPEAT CONJ_TAC >> Cases >> (
  FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [word_extract_mask, w2n_n2w] >>
  blastLib.BBLAST_TAC >>
  UNABBREV_ALL_TAC >> BETA_TAC >>
  ASM_SIMP_TAC arith_ss [bitTheory.BIT_SHIFT_THM4, bitTheory.NOT_BIT_GT_TWOEXP] >>
  METIS_TAC[]
));


val bir_hcast_REWRS = store_thm ("bir_hcast_REWRS", ``
  (* Not very casts *)
     (!w. bir_hcast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bir_hcast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bir_hcast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bir_hcast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bir_hcast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bir_hcast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_hcast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_hcast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_hcast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_hcast (Imm8  w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm8  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_hcast (Imm8  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_hcast (Imm8  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_hcast (Imm16 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm16 w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_hcast (Imm16 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_hcast (Imm32 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm32 w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_hcast (Imm64 w) Bit1  = Imm1  (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit8  = Imm8  (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit16 = Imm16 (w2wh w))
  /\ (!w. bir_hcast (Imm64 w) Bit32 = Imm32 (w2wh w))
``,

SIMP_TAC (std_ss++wordsLib.WORD_ss) [bir_hcast_REWRS0, w2wh_id,
 w2wh_w2w]);


(* ============= *)
(* scast         *)
(* ============= *)

val bir_scast_def = Define `bir_scast r s =
  n2bs (if (type_of_bir_imm r = Bit1) then (b2n r) else
     (SIGN_EXTEND (size_of_bir_immtype (type_of_bir_imm r))
                  (size_of_bir_immtype s) (b2n r))) s`;

val bir_scast_REWRS0 = store_thm ("bir_scast_REWRS0", ``
     (!w. bir_scast (Imm1  w) Bit1  = Imm1  (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_scast (Imm8  w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit64 = Imm64 (sw2sw w))
``,
SIMP_TAC (std_ss++bir_imm_ss++wordsLib.WORD_ss) [
  bir_scast_def, n2bs_def, sw2sw_def,
  size_of_bir_immtype_def, type_of_bir_imm_def, b2n_def, GSYM w2w_def]);


val bir_scast_REWRS = store_thm ("bir_scast_REWRS", ``
  (* Indentity *)
     (!w. bir_scast (Imm1  w) Bit1  = Imm1  w)
  /\ (!w. bir_scast (Imm8  w) Bit8  = Imm8  w)
  /\ (!w. bir_scast (Imm16 w) Bit16 = Imm16 w)
  /\ (!w. bir_scast (Imm32 w) Bit32 = Imm32 w)
  /\ (!w. bir_scast (Imm64 w) Bit64 = Imm64 w)

  (* Casts *)
  /\ (!w. bir_scast (Imm1  w) Bit8  = Imm8  (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit16 = Imm16 (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit32 = Imm32 (w2w w))
  /\ (!w. bir_scast (Imm1  w) Bit64 = Imm64 (w2w w))
  /\ (!w. bir_scast (Imm8  w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm8  w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit32 = Imm32 (sw2sw w))
  /\ (!w. bir_scast (Imm16 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm32 w) Bit64 = Imm64 (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit1  = Imm1  (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit8  = Imm8  (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit16 = Imm16 (sw2sw w))
  /\ (!w. bir_scast (Imm64 w) Bit32 = Imm32 (sw2sw w))
``,
SIMP_TAC (std_ss) [bir_scast_REWRS0, w2w_id, sw2sw_id]);


(* ============= *)
(* combination   *)
(* ============= *)

val _ = Datatype `bir_cast_t =
  | BIExp_UnsignedCast
  | BIExp_SignedCast
  | BIExp_HighCast
  | BIExp_LowCast`;

val bir_gencast_def = Define `
  (bir_gencast BIExp_UnsignedCast = bir_cast) /\
  (bir_gencast BIExp_SignedCast = bir_scast) /\
  (bir_gencast BIExp_HighCast = bir_hcast) /\
  (bir_gencast BIExp_LowCast = bir_lcast)`;

val bir_casts_DEFS = save_thm ("bir_casts_DEFS",
  LIST_CONJ [bir_cast_def, bir_scast_def, bir_hcast_def, bir_lcast_def]);

val bir_casts_REWRS = save_thm ("bir_casts_REWRS",
  LIST_CONJ [bir_cast_REWRS, bir_scast_REWRS, bir_hcast_REWRS, bir_lcast_REWRS]);


val type_of_bir_gencast = store_thm ("type_of_bir_gencast",
  ``!ct b s. type_of_bir_imm (bir_gencast ct b s) = s``,
Cases >> SIMP_TAC std_ss [bir_gencast_def, bir_casts_DEFS, type_of_n2bs]);


val bir_gencast_ID = store_thm ("bir_gencast_ID",
  ``!ct b s. (type_of_bir_imm b = s) ==> ((bir_gencast ct b s) = b)``,
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_gencast_def, bir_casts_REWRS, type_of_bir_imm_def]
));


val bir_casts_list = TypeBase.constructors_of ``:bir_cast_t``;

val bir_casts_ID = save_thm ("bir_casts_ID",
REWRITE_RULE [bir_gencast_def] (
  inst_CONJ_THM bir_casts_list bir_gencast_ID));

val type_of_bir_casts = save_thm ("type_of_bir_casts",
REWRITE_RULE [bir_gencast_def] (
   inst_CONJ_THM bir_casts_list type_of_bir_gencast));


val bir_casts_Bit1 = store_thm ("bir_casts_Bit1",
  ``!ct b c. (type_of_bir_imm b = Bit1) ==>
             (bir_gencast ct b c = bir_cast b c)``,
Cases >> Cases >> Cases >> (
  SIMP_TAC (std_ss++bir_imm_ss) [bir_casts_REWRS, bir_gencast_def, type_of_bir_imm_def]
));


val _ = export_theory();
