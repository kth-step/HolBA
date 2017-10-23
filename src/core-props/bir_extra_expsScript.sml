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


val _ = export_theory();
