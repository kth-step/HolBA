open HolKernel Parse boolLib bossLib;
open HolBACoreSimps
open bir_expTheory bir_imm_expTheory bir_valuesTheory
open bir_typing_expTheory bir_envTheory wordsTheory

(* Some extra expressions that are sometimes useful. *)

val _ = new_theory "bir_extra_exps";


(*********)
(* Align *)
(*********)



val BExp_Align_def = Define `BExp_Align sz p e =
  (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2 ** (size_of_bir_immtype sz) - (2 ** p)) sz)))`;


val BExp_Align_vars_of = store_thm ("BExp_Align_vars_of",
``!sz p e. bir_vars_of_exp (BExp_Align sz p e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, pred_setTheory.UNION_EMPTY]);


val BExp_Align_type_of = store_thm ("BExp_Align_type_of",
``!sz p e. type_of_bir_exp (BExp_Align sz p e) =
           if (type_of_bir_exp e = SOME (BType_Imm sz)) then
               SOME (BType_Imm sz) else NONE``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));


val BExp_Align_eval = store_thm ("BExp_Align_eval",
``!sz p e env. bir_eval_exp (BExp_Align sz p e) env =
     case (sz, bir_eval_exp e env) of
         (Bit1,  BVal_Imm (Imm1 w))  => BVal_Imm (Imm1 (align p w))
       | (Bit8,  BVal_Imm (Imm8 w))  => BVal_Imm (Imm8 (align p w))
       | (Bit16, BVal_Imm (Imm16 w)) => BVal_Imm (Imm16 (align p w))
       | (Bit32, BVal_Imm (Imm32 w)) => BVal_Imm (Imm32 (align p w))
       | (Bit64, BVal_Imm (Imm64 w)) => BVal_Imm (Imm64 (align p w))
       | (_, _) => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, alignmentTheory.align_bitwise_and,
  pairTheory.pair_case_thm, LSL_UINT_MAX] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) []
));


val align_AND_INTROS = save_thm ("align_AND_INTROS", let
  val thm0 = prove (``!w:'a word p.
     (MEM p (COUNT_LIST (dimindex (:'a)))) ==> (0 < p) ==>
     (((w && n2w (dimword (:'a) - 2 ** p) = align p w)) /\
      (((n2w (dimword (:'a) - 2 ** p) && w) = align p w)))``,
   SIMP_TAC std_ss [alignmentTheory.align_bitwise_and, LSL_UINT_MAX] >>
   METIS_TAC[wordsTheory.WORD_AND_COMM]);

  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;
  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'a`` |-> sz] thm0) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_def_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM, GSYM CONJ_ASSOC] thm2
in thm3 end);


(***********)
(* Aligned *)
(***********)

val BExp_Aligned_def = Define `BExp_Aligned sz p e =
   (BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2 ** p - 1) sz)))
      (BExp_Const (n2bs 0 sz)))`

val BExp_Aligned_vars_of = store_thm ("BExp_Aligned_vars_of",
``!sz p e. bir_vars_of_exp (BExp_Aligned sz p e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, pred_setTheory.UNION_EMPTY]);


val BExp_Aligned_type_of = store_thm ("BExp_Aligned_type_of",
``!sz p e. type_of_bir_exp (BExp_Aligned sz p e) =
           if (type_of_bir_exp e = SOME (BType_Imm sz)) then
               SOME BType_Bool else NONE``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));

val BExp_Aligned_eval = store_thm ("BExp_Aligned_eval",
``!sz p e env. bir_eval_exp (BExp_Aligned sz p e) env =
     case (sz, bir_eval_exp e env) of
         (Bit1,  BVal_Imm (Imm1 w))  => BVal_Imm (bool2b (aligned p w))
       | (Bit8,  BVal_Imm (Imm8 w))  => BVal_Imm (bool2b (aligned p w))
       | (Bit16, BVal_Imm (Imm16 w)) => BVal_Imm (bool2b (aligned p w))
       | (Bit32, BVal_Imm (Imm32 w)) => BVal_Imm (bool2b (aligned p w))
       | (Bit64, BVal_Imm (Imm64 w)) => BVal_Imm (bool2b (aligned p w))
       | (_, _) => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, alignmentTheory.aligned_bitwise_and] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [
     bir_bool_expTheory.bir_bin_exp_BOOL_OPER_EVAL]
));




(******************)
(* Reverse Endian *)
(******************)

val reverse_endian16_def = Define `
  reverse_endian16 (w:word16) =
    (((((7 >< 0) w):word8) @@ (((16 >< 8) w):word8)) : word16)`

val reverse_endian32_def = Define `
 reverse_endian32 (w:word32) =
     (((((7 :num) >< (0 :num)) w :word8) @@
       (((((15 :num) >< (8 :num)) w :word8) @@
        (((((23 :num) >< (16 :num)) w :word8) @@
         (((31 :num) >< (24 :num)) w :word8))
           :word16))
          :word24))
        :word32)`

val reverse_endian64_def = Define `
 reverse_endian64 (w:word64) =
     (((((7 :num) >< (0 :num)) w :word8) @@
       (((((15 :num) >< (8 :num)) w :word8) @@
        (((((23 :num) >< (16 :num)) w :word8) @@
         (((((31 :num) >< (24 :num)) w :word8) @@
          (((((39 :num) >< (32 :num)) w :word8) @@
           (((((47 :num) >< (40 :num)) w :word8) @@
            (((((55 :num) >< (48 :num)) w :word8) @@
             (((63 :num) >< (56 :num)) w :word8))
           :word16))
          :word24))
        :word32))
           :40 word))
          :48 word))
        :56 word)):word64)`;


val reverse_endian16_id = store_thm ("reverse_endian16_id",
``!w:word16. reverse_endian16 (reverse_endian16 w) = w``,

Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian16_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]);


val reverse_endian32_id = store_thm ("reverse_endian32_id",
``!w:word32. reverse_endian32 (reverse_endian32 w) = w``,

Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]);


val reverse_endian64_id = store_thm ("reverse_endian64_id",
``!w:word64. reverse_endian64 (reverse_endian64 w) = w``,

Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]);




val word_extract_byte_def = Define `word_extract_byte (w:'a word) (n:num) =
  (w && ((n2w 255) << n))`



val word_extract_byte_index = store_thm ("word_extract_byte_index",
``!w:'a word m n. m < dimindex (:'a) ==>
  ((word_extract_byte w n) ' m =
  ((w ' m) /\ (n <= m) /\ (m < n + 8)))``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_lsl_def, word_and_def, word_index, word_extract_byte_def] >>

MP_TAC (Q.SPECL [`m-n`, `8`] bitTheory.BIT_EXP_SUB1) >>
ASM_SIMP_TAC arith_ss []);




val reverse_endian16_ALT_DEF = store_thm ("reverse_endian16_ALT_DEF",
``!w:word16. reverse_endian16 w = (w >>> 8) || (w << 8)``,

Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian16_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_lsr_def, word_lsl_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []);


val reverse_endian32_ALT_DEF_aux = prove (
``!w:word32. reverse_endian32 w = (w >>> 24) || (word_extract_byte (w >>> 8) 8) ||
                                  (word_extract_byte (w << 8) 16) || (w << 24)``,

GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_byte_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []);

val reverse_endian32_ALT_DEF = save_thm ("reverse_endian32_ALT_DEF",
  SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_byte_def, word_lsl_n2w] reverse_endian32_ALT_DEF_aux);


val reverse_endian64_ALT_DEF_aux = prove (
``!w:word64. reverse_endian64 w = (w >>> 56) || (word_extract_byte (w >>> 40) 8) ||
                                  (word_extract_byte (w >>> 24) 16) ||
                                  (word_extract_byte (w >>> 8) 24) ||
                                  (word_extract_byte (w << 8) 32) ||
                                  (word_extract_byte (w << 24) 40) ||
                                  (word_extract_byte (w << 40) 48) ||
                                  (w << 56)``,

GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  reverse_endian64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_byte_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []);


val reverse_endian64_ALT_DEF = save_thm ("reverse_endian64_ALT_DEF",
  SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_byte_def, word_lsl_n2w] reverse_endian64_ALT_DEF_aux);


val BExp_reverse_endian64_def = Define `BExp_reverse_endian64 e1 =
      (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm64 56w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm64 40w)))
              (BExp_Const (Imm64 65280w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_RightShift e1
                    (BExp_Const (Imm64 24w)))
                 (BExp_Const (Imm64 0xFF0000w)))
              (BExp_BinExp BIExp_Or
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_RightShift e1
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFF000000w)))
                 (BExp_BinExp BIExp_Or
                    (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_LeftShift e1
                          (BExp_Const (Imm64 8w)))
                       (BExp_Const (Imm64 0xFF00000000w)))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm64 24w)))
                          (BExp_Const (Imm64 0xFF0000000000w)))
                       (BExp_BinExp BIExp_Or
                          (BExp_BinExp BIExp_And
                             (BExp_BinExp BIExp_LeftShift e1
                                (BExp_Const (Imm64 40w)))
                             (BExp_Const (Imm64 0xFF000000000000w)))
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm64 56w))))))))))`

val BExp_reverse_endian32_def = Define `BExp_reverse_endian32 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm32 24w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm32 8w)))
              (BExp_Const (Imm32 65280w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_LeftShift e1
                    (BExp_Const (Imm32 8w)))
                 (BExp_Const (Imm32 0xFF0000w)))
              (BExp_BinExp BIExp_LeftShift e1
                 (BExp_Const (Imm32 24w))))))`

val BExp_reverse_endian16_def = Define `BExp_reverse_endian16 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm16 8w)))
        (BExp_BinExp BIExp_LeftShift e1 (BExp_Const (Imm16 8w))))`



val BExp_reverse_endian16_vars_of = store_thm ("BExp_reverse_endian16_vars_of",
``!e. bir_vars_of_exp (BExp_reverse_endian16 e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian16_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]);



val BExp_reverse_endian32_vars_of = store_thm ("BExp_reverse_endian32_vars_of",
``!e. bir_vars_of_exp (BExp_reverse_endian32 e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian32_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]);


val BExp_reverse_endian64_vars_of = store_thm ("BExp_reverse_endian64_vars_of",
``!e. bir_vars_of_exp (BExp_reverse_endian64 e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian64_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]);


val BExp_reverse_endian16_type_of = store_thm ("BExp_reverse_endian16_type_of",
``!e. type_of_bir_exp (BExp_reverse_endian16 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit16)) then SOME (BType_Imm Bit16) else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian16_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));

val BExp_reverse_endian32_type_of = store_thm ("BExp_reverse_endian32_type_of",
``!e. type_of_bir_exp (BExp_reverse_endian32 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit32)) then SOME (BType_Imm Bit32) else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian32_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));

val BExp_reverse_endian64_type_of = store_thm ("BExp_reverse_endian64_type_of",
``!e. type_of_bir_exp (BExp_reverse_endian64 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit64)) then SOME (BType_Imm Bit64) else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian64_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));


val BExp_reverse_endian16_eval = store_thm ("BExp_reverse_endian16_eval",
``!e env. bir_eval_exp (BExp_reverse_endian16 e) env =
     case (bir_eval_exp e env) of
       | (BVal_Imm (Imm16 w)) => BVal_Imm (Imm16 (reverse_endian16 w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian16_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [reverse_endian16_ALT_DEF,
    wordsTheory.word_shift_bv]
));

val BExp_reverse_endian32_eval = store_thm ("BExp_reverse_endian32_eval",
``!e env. bir_eval_exp (BExp_reverse_endian32 e) env =
     case (bir_eval_exp e env) of
       | (BVal_Imm (Imm32 w)) => BVal_Imm (Imm32 (reverse_endian32 w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian32_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [reverse_endian32_ALT_DEF,
    wordsTheory.word_shift_bv]
));


val BExp_reverse_endian64_eval = store_thm ("BExp_reverse_endian64_eval",
``!e env. bir_eval_exp (BExp_reverse_endian64 e) env =
     case (bir_eval_exp e env) of
       | (BVal_Imm (Imm64 w)) => BVal_Imm (Imm64 (reverse_endian64 w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_reverse_endian64_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [reverse_endian64_ALT_DEF,
    wordsTheory.word_shift_bv]
));


(************)
(* word_msb *)
(************)

val BExp_MSB_def = Define `BExp_MSB sz e =
   BExp_BinPred BIExp_SignedLessThan e (BExp_Const (n2bs 0 sz))`;

val BExp_MSB_vars_of = store_thm ("BExp_MSB_vars_of",
``!sz e. bir_vars_of_exp (BExp_MSB sz e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, pred_setTheory.UNION_EMPTY]);

val BExp_MSB_type_of = store_thm ("BExp_MSB_type_of",
``!sz e. type_of_bir_exp (BExp_MSB sz e) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));


val BExp_MSB_eval = store_thm ("BExp_MSB_eval",
``!sz e env. bir_eval_exp (BExp_MSB sz e) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,  BVal_Imm (Imm1  w)) => BVal_Imm (bool2b (word_msb w))
       | (Bit8,  BVal_Imm (Imm8  w)) => BVal_Imm (bool2b (word_msb w))
       | (Bit16, BVal_Imm (Imm16 w)) => BVal_Imm (bool2b (word_msb w))
       | (Bit32, BVal_Imm (Imm32 w)) => BVal_Imm (bool2b (word_msb w))
       | (Bit64, BVal_Imm (Imm64 w)) => BVal_Imm (bool2b (word_msb w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, wordsTheory.word_msb_neg] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));




(************)
(* word_lsb *)
(************)

val bool2b_word_lsb = prove (``!w. bool2w (word_lsb w) = w2w w``,
SIMP_TAC std_ss [bir_immTheory.bool2w_def, word_lsb_def] >>
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
Cases >> SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [] >>
FULL_SIMP_TAC (arith_ss++wordsLib.WORD_ss ++
  boolSimps.LIFT_COND_ss) [
  fcpTheory.FCP_BETA, w2w]);

val BExp_LSB_def = Define `BExp_LSB e = BExp_Cast BIExp_LowCast e Bit1`

val BExp_LSB_vars_of = store_thm ("BExp_LSB_vars_of",
``!e. bir_vars_of_exp (BExp_LSB e) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def]);

val BExp_LSB_type_of = store_thm ("BExp_LSB_type_of",
``!e. type_of_bir_exp (BExp_LSB e) =
      (if (?sz. type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def]
));


val BExp_LSB_eval = store_thm ("BExp_LSB_eval",
``!e env. bir_eval_exp (BExp_LSB e) env =
     case (bir_eval_exp e env) of
       | (BVal_Imm (Imm1  w)) => BVal_Imm (bool2b (word_lsb w))
       | (BVal_Imm (Imm8  w)) => BVal_Imm (bool2b (word_lsb w))
       | (BVal_Imm (Imm16 w)) => BVal_Imm (bool2b (word_lsb w))
       | (BVal_Imm (Imm32 w)) => BVal_Imm (bool2b (word_lsb w))
       | (BVal_Imm (Imm64 w)) => BVal_Imm (bool2b (word_lsb w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def, bir_immTheory.bool2b_def, bool2b_word_lsb] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [w2w_id]
));



(*********************)
(* Word-Bit-Constant *)
(*********************)

val word_bit_ALT_DEF = prove (``!w n. (word_bit n w = ((w && n2w (2**n)) <> 0w))``,
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
`0 < dimindex (:'a)` by METIS_TAC[DIMINDEX_GT_0] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [
  word_bit_def, word_0, word_and_def, fcpTheory.FCP_BETA, word_index,
  bitTheory.BIT_TWO_POW] >>
DECIDE_TAC);


val BExp_word_bit_def = Define `BExp_word_bit sz e n =
   BExp_BinPred BIExp_NotEqual
   (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2**n) sz))) (BExp_Const (n2bs 0 sz))`;

val BExp_word_bit_vars_of = store_thm ("BExp_word_bit_vars_of",
``!sz e n. bir_vars_of_exp (BExp_word_bit sz e n) = bir_vars_of_exp e``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, pred_setTheory.UNION_EMPTY]);

val BExp_word_bit_type_of = store_thm ("BExp_word_bit_type_of",
``!sz e n. type_of_bir_exp (BExp_word_bit sz e n) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));


val BExp_word_bit_eval = store_thm ("BExp_word_bit_eval",
``!sz e n env. bir_eval_exp (BExp_word_bit sz e n) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,  BVal_Imm (Imm1  w)) => BVal_Imm (bool2b (word_bit n w))
       | (Bit8,  BVal_Imm (Imm8  w)) => BVal_Imm (bool2b (word_bit n w))
       | (Bit16, BVal_Imm (Imm16 w)) => BVal_Imm (bool2b (word_bit n w))
       | (Bit32, BVal_Imm (Imm32 w)) => BVal_Imm (bool2b (word_bit n w))
       | (Bit64, BVal_Imm (Imm64 w)) => BVal_Imm (bool2b (word_bit n w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, word_bit_ALT_DEF] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));




(****************)
(* Word-Bit Exp *)
(****************)

val BExp_word_bit_exp_def = Define `BExp_word_bit_exp sz e ne =
   BExp_BinPred BIExp_NotEqual
   (BExp_BinExp BIExp_And e (BExp_BinExp BIExp_LeftShift (BExp_Const (n2bs 1 sz)) ne))
      (BExp_Const (n2bs 0 sz))`;

val BExp_word_bit_exp_vars_of = store_thm ("BExp_word_bit_exp_vars_of",
``!sz e en. bir_vars_of_exp (BExp_word_bit_exp sz e en) = bir_vars_of_exp e UNION bir_vars_of_exp en``,
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, pred_setTheory.UNION_EMPTY]);


val BExp_word_bit_exp_type_of = store_thm ("BExp_word_bit_exp_type_of",
``!sz e en. type_of_bir_exp (BExp_word_bit_exp sz e en) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) /\
          (type_of_bir_exp en = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
));


val BExp_word_bit_exp_eval = store_thm ("BExp_word_bit_exp_eval",
``!sz e en env. bir_eval_exp (BExp_word_bit_exp sz e en) env =
     case (sz, bir_eval_exp e env, bir_eval_exp en env) of
       | (Bit1,  BVal_Imm (Imm1  w), BVal_Imm (Imm1  wn)) =>
            BVal_Imm (bool2b (word_bit (w2n wn) w))
       | (Bit8,  BVal_Imm (Imm8  w), BVal_Imm (Imm8  wn)) =>
            BVal_Imm (bool2b (word_bit (w2n wn) w))
       | (Bit16, BVal_Imm (Imm16 w), BVal_Imm (Imm16 wn)) =>
            BVal_Imm (bool2b (word_bit (w2n wn) w))
       | (Bit32, BVal_Imm (Imm32 w), BVal_Imm (Imm32 wn)) =>
            BVal_Imm (bool2b (word_bit (w2n wn) w))
       | (Bit64, BVal_Imm (Imm64 w), BVal_Imm (Imm64 wn)) =>
            BVal_Imm (bool2b (word_bit (w2n wn) w))
       | _ => BVal_Unknown``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, word_bit_ALT_DEF] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  SIMP_TAC std_ss [GSYM wordsTheory.word_1_lsl, GSYM wordsTheory.word_lsl_bv_def]
));


val _ = export_theory();
