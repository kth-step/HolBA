open HolKernel Parse boolLib bossLib;
open HolBACoreSimps
open bir_expTheory bir_exp_immTheory bir_valuesTheory
open bir_typing_expTheory bir_envTheory wordsTheory
open bir_exp_immSyntax
open bir_exp_substitutionsTheory;

(* Some extra expressions that are sometimes useful. *)

val _ = new_theory "bir_extra_exps";


(*********)
(* Align *)
(*********)

Definition BExp_Align_def:
  BExp_Align sz p e =
  (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2 ** (size_of_bir_immtype sz) - (2 ** p)) sz)))
End


Theorem BExp_Align_vars_of:
  !sz p e. bir_vars_of_exp (BExp_Align sz p e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, pred_setTheory.UNION_EMPTY]
QED


Theorem BExp_Align_type_of:
  !sz p e. type_of_bir_exp (BExp_Align sz p e) =
           if (type_of_bir_exp e = SOME (BType_Imm sz)) then
               SOME (BType_Imm sz) else NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_Align_eval:
  !sz p e env. bir_eval_exp (BExp_Align sz p e) env =
     case (sz, bir_eval_exp e env) of
         (Bit1,   SOME (BVal_Imm (Imm1   w))) => SOME (BVal_Imm (Imm1   (align p w)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w))) => SOME (BVal_Imm (Imm8   (align p w)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w))) => SOME (BVal_Imm (Imm16  (align p w)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w))) => SOME (BVal_Imm (Imm32  (align p w)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w))) => SOME (BVal_Imm (Imm64  (align p w)))
       | (Bit128, SOME (BVal_Imm (Imm128 w))) => SOME (BVal_Imm (Imm128 (align p w)))
       | (_, _) => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Align_def, alignmentTheory.align_bitwise_and,
  pairTheory.pair_case_thm, LSL_UINT_MAX] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) []
)
QED


val align_AND_INTROS = save_thm ("align_AND_INTROS", let
Theorem thm0[local]:
  !w:'a word p.
     (MEM p (COUNT_LIST (dimindex (:'a)))) ==> (0 < p) ==>
     (((w && n2w (dimword (:'a) - 2 ** p) = align p w)) /\
      (((n2w (dimword (:'a) - 2 ** p) && w) = align p w)))
Proof
SIMP_TAC std_ss [alignmentTheory.align_bitwise_and, LSL_UINT_MAX] >>
   METIS_TAC[wordsTheory.WORD_AND_COMM]
QED

  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;
  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'a`` |-> sz] thm0) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM, FORALL_AND_THM, GSYM CONJ_ASSOC] thm2
in thm3 end);


(***********)
(* Aligned *)
(***********)

Definition BExp_Aligned_def:
  BExp_Aligned sz p e =
   (BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2 ** p - 1) sz)))
      (BExp_Const (n2bs 0 sz)))
End

Theorem BExp_Aligned_vars_of:
  !sz p e. bir_vars_of_exp (BExp_Aligned sz p e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, pred_setTheory.UNION_EMPTY]
QED


Theorem BExp_Aligned_type_of:
  !sz p e. type_of_bir_exp (BExp_Aligned sz p e) =
           if (type_of_bir_exp e = SOME (BType_Imm sz)) then
               SOME BType_Bool else NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_Aligned_eval:
  !sz p e env. bir_eval_exp (BExp_Aligned sz p e) env =
     case (sz, bir_eval_exp e env) of
         (Bit1,   SOME (BVal_Imm (Imm1   w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (Bit128, SOME (BVal_Imm (Imm128 w))) => SOME (BVal_Imm (bool2b (aligned p w)))
       | (_, _) => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_Aligned_def, alignmentTheory.aligned_bitwise_and] >>
REPEAT CASE_TAC >> (
   FULL_SIMP_TAC (std_ss++holBACore_ss) [
     bir_bool_expTheory.bir_bin_exp_BOOL_OPER_EVAL]
)
QED

(******************)
(* Reverse Word 1 *)
(******************)

fun mk_word_reverse_exp sz = let
  val wty = fcpSyntax.mk_int_numeric_type sz
  val we_tm = mk_var ("we", bir_expSyntax.bir_exp_t_ty)

  fun mk_for_bit bit_no = let
    val new_bit_no = (sz - 1) - bit_no

    val (shift_no, shift_tm) = if new_bit_no < bit_no then
      (bit_no - new_bit_no, BIExp_RightShift_tm)
     else
      (new_bit_no - bit_no, BIExp_LeftShift_tm)

    val mask_tm =      bir_expSyntax.mk_BExp_Const (
     bir_immSyntax.gen_mk_Imm (wordsSyntax.mk_n2w (
          numSyntax.mk_exp (numSyntax.term_of_int 2,
          numSyntax.term_of_int new_bit_no), wty)))
    val d0 = bir_expSyntax.mk_BExp_BinExp (shift_tm, we_tm,
               bir_expSyntax.mk_BExp_Const (
                 bir_immSyntax.mk_Imm_of_int sz shift_no))
    val d1 = if (bit_no = 0) orelse (new_bit_no = 0) then d0 else
             bir_expSyntax.mk_BExp_BinExp (BIExp_And_tm,
                d0, mask_tm)
  in d1 end

  val dl = List.rev (List.tabulate (sz, mk_for_bit))

  val tm = foldl (fn (t1, t2) => bir_expSyntax.mk_BExp_BinExp (BIExp_Or_tm,
             t1, t2)) (hd dl) (tl dl)
in
  tm
end;


Definition BExp_word_reverse_1_8_def:
  BExp_word_reverse_1_8  we  = ^(mk_word_reverse_exp 8)
End
Definition BExp_word_reverse_1_16_def:
  BExp_word_reverse_1_16 we  = ^(mk_word_reverse_exp 16)
End
Definition BExp_word_reverse_1_32_def:
  BExp_word_reverse_1_32 we  = ^(mk_word_reverse_exp 32)
End
Definition BExp_word_reverse_1_64_def:
  BExp_word_reverse_1_64 we  = ^(mk_word_reverse_exp 64)
End
Definition BExp_word_reverse_1_128_def:
  BExp_word_reverse_1_128 we = ^(mk_word_reverse_exp 128)
End



Theorem BExp_word_reverse_1_vars_of:
  (!e. bir_vars_of_exp (BExp_word_reverse_1_8 e) = bir_vars_of_exp e) /\
  (!e. bir_vars_of_exp (BExp_word_reverse_1_16 e) = bir_vars_of_exp e) /\
  (!e. bir_vars_of_exp (BExp_word_reverse_1_32 e) = bir_vars_of_exp e) /\
  (!e. bir_vars_of_exp (BExp_word_reverse_1_64 e) = bir_vars_of_exp e) /\
  (!e. bir_vars_of_exp (BExp_word_reverse_1_128 e) = bir_vars_of_exp e)
Proof
SIMP_TAC (std_ss++holBACore_ss) [
  BExp_word_reverse_1_128_def,
  BExp_word_reverse_1_64_def,
  BExp_word_reverse_1_32_def,
  BExp_word_reverse_1_16_def,
  BExp_word_reverse_1_8_def,
  pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_1_type_of:
  (!e. type_of_bir_exp (BExp_word_reverse_1_8 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit8)) then SOME (BType_Imm Bit8) else NONE)) /\
  (!e. type_of_bir_exp (BExp_word_reverse_1_16 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit16)) then SOME (BType_Imm Bit16) else NONE)) /\
  (!e. type_of_bir_exp (BExp_word_reverse_1_32 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit32)) then SOME (BType_Imm Bit32) else NONE)) /\
  (!e. type_of_bir_exp (BExp_word_reverse_1_64 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit64)) then SOME (BType_Imm Bit64) else NONE)) /\
  (!e. type_of_bir_exp (BExp_word_reverse_1_128 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit128)) then SOME (BType_Imm Bit128) else NONE))
Proof
SIMP_TAC (std_ss++holBACore_ss) [
  BExp_word_reverse_1_128_def,
  BExp_word_reverse_1_64_def,
  BExp_word_reverse_1_32_def,
  BExp_word_reverse_1_16_def,
  BExp_word_reverse_1_8_def,
  type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

(* To increase power of EVAL_TAC against nasty bit manipulation stuff *)
(* TODO: Change the below proof to something less brutal later... *)
val _ = bitLib.add_bit_compset computeLib.the_compset

Theorem BExp_word_reverse_1_eval:
  (!e env. bir_eval_exp (BExp_word_reverse_1_8 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm8 w)) => SOME (BVal_Imm (Imm8 (word_reverse w)))
       | _ => NONE) /\
  (!e env. bir_eval_exp (BExp_word_reverse_1_16 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm16 w)) => SOME (BVal_Imm (Imm16 (word_reverse w)))
       | _ => NONE) /\
  (!e env. bir_eval_exp (BExp_word_reverse_1_32 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm32 w)) => SOME (BVal_Imm (Imm32 (word_reverse w)))
       | _ => NONE) /\
  (!e env. bir_eval_exp (BExp_word_reverse_1_64 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm64 w)) => SOME (BVal_Imm (Imm64 (word_reverse w)))
       | _ => NONE) /\
  (!e env. bir_eval_exp (BExp_word_reverse_1_128 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (Imm128 (word_reverse w)))
       | _ => NONE)
Proof
SIMP_TAC (std_ss++holBACore_ss)
  [BExp_word_reverse_1_8_def, BExp_word_reverse_1_16_def,
   BExp_word_reverse_1_32_def, BExp_word_reverse_1_64_def,
   BExp_word_reverse_1_128_def] >>
REPEAT STRIP_TAC >> REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) []
) >> (
  ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_or_def, fcpTheory.FCP_BETA,
    word_and_def, word_index, bitTheory.BIT_TWO_POW] >>
  SIMP_TAC (std_ss++boolSimps.CONJ_ss++wordsLib.SIZES_ss) [wordsTheory.word_lsl_bv_def,
    word_lsr_bv_def, w2n_n2w, word_lsl_def, fcpTheory.FCP_BETA,
    word_lsr_def, word_reverse_def] >>
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `i < _` (STRIP_ASSUME_TAC o SIMP_RULE std_ss [GSYM rich_listTheory.MEM_COUNT_LIST,
    rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, listTheory.MEM]) >>
  ASM_SIMP_TAC std_ss [] >> (
      EVAL_TAC
  )
)
QED

(******************)
(* Reverse Word 8 *)
(******************)

Definition word_reverse_8_16_def:
  word_reverse_8_16 (w:word16) =
    (((((7 >< 0) w):word8) @@ (((15 >< 8) w):word8)) : word16)
End


Definition word_reverse_8_32_def:
  word_reverse_8_32 (w:word32) =
     (((((7 :num) >< (0 :num)) w :word8) @@
       (((((15 :num) >< (8 :num)) w :word8) @@
        (((((23 :num) >< (16 :num)) w :word8) @@
         (((31 :num) >< (24 :num)) w :word8))
           :word16))
          :word24))
        :word32)
End

Definition word_reverse_8_64_def:
  word_reverse_8_64 (w:word64) =
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
        :56 word)):word64)
End

Definition word_reverse_8_128_def:
  word_reverse_8_128 (w:word128) =
     (((((7 :num) >< (0 :num)) w :word8) @@
       (((((15 :num) >< (8 :num)) w :word8) @@
        (((((23 :num) >< (16 :num)) w :word8) @@
         (((((31 :num) >< (24 :num)) w :word8) @@
          (((((39 :num) >< (32 :num)) w :word8) @@
           (((((47 :num) >< (40 :num)) w :word8) @@
            (((((55 :num) >< (48 :num)) w :word8) @@
             (((((63 :num) >< (56 :num)) w :word8) @@
     (((((71 :num) >< (64 :num)) w :word8) @@
       (((((79 :num) >< (72 :num)) w :word8) @@
        (((((87 :num) >< (80 :num)) w :word8) @@
         (((((95 :num) >< (88 :num)) w :word8) @@
          (((((103 :num) >< (96 :num)) w :word8) @@
           (((((111 :num) >< (104 :num)) w :word8) @@
            (((((119 :num) >< (112 :num)) w :word8) @@
             (((127 :num) >< (120 :num)) w :word8))
           :word16))
          :word24))
        :word32))
           :40 word))
          :48 word))
        :56 word)):word64))
           :72 word))
          :80 word))
        :88 word))
           :96 word))
          :104 word))
        :112 word)):120 word)):word128)
End


Theorem word_reverse_8_16_id:
  !w:word16. word_reverse_8_16 (word_reverse_8_16 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_16_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED


Theorem word_reverse_8_32_id:
  !w:word32. word_reverse_8_32 (word_reverse_8_32 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED


Theorem word_reverse_8_64_id:
  !w:word64. word_reverse_8_64 (word_reverse_8_64 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED

Theorem word_reverse_8_128_id:
  !w:word128. word_reverse_8_128 (word_reverse_8_128 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED




Definition word_extract_byte_def:
  word_extract_byte (w:'a word) (n:num) =
  (w && ((n2w 255) << n))
End



Theorem word_extract_byte_index:
  !w:'a word m n. m < dimindex (:'a) ==>
  ((word_extract_byte w n) ' m =
  ((w ' m) /\ (n <= m) /\ (m < n + 8)))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_lsl_def, word_and_def, word_index, word_extract_byte_def] >>

MP_TAC (Q.SPECL [`m-n`, `8`] bitTheory.BIT_EXP_SUB1) >>
ASM_SIMP_TAC arith_ss []
QED




Theorem word_reverse_8_16_ALT_DEF:
  !w:word16. word_reverse_8_16 w = (w >>> 8) || (w << 8)
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_16_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_lsr_def, word_lsl_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_8_32_ALT_DEF_aux[local]:
  !w:word32. word_reverse_8_32 w = (w >>> 24) || (word_extract_byte (w >>> 8) 8) ||
                                  (word_extract_byte (w << 8) 16) || (w << 24)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_byte_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED

Theorem word_reverse_8_32_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_byte_def, word_lsl_n2w] word_reverse_8_32_ALT_DEF_aux



Theorem word_reverse_8_64_ALT_DEF_aux[local]:
  !w:word64. word_reverse_8_64 w = (w >>> 56) || (word_extract_byte (w >>> 40) 8) ||
                                  (word_extract_byte (w >>> 24) 16) ||
                                  (word_extract_byte (w >>> 8) 24) ||
                                  (word_extract_byte (w << 8) 32) ||
                                  (word_extract_byte (w << 24) 40) ||
                                  (word_extract_byte (w << 40) 48) ||
                                  (w << 56)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_byte_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_8_64_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_byte_def, word_lsl_n2w] word_reverse_8_64_ALT_DEF_aux



Theorem word_reverse_8_128_ALT_DEF_aux[local]:
  !w:word128. word_reverse_8_128 w = (w >>> 120) || (word_extract_byte (w >>> 104) 8) ||
                                    (word_extract_byte (w >>> 88) 16)  ||
                                    (word_extract_byte (w >>> 72) 24)  ||
                                    (word_extract_byte (w >>> 56) 32)  ||
                                    (word_extract_byte (w >>> 40) 40)  ||
                                    (word_extract_byte (w >>> 24) 48)  ||
                                    (word_extract_byte (w >>>  8) 56)  ||
                                    (word_extract_byte (w <<   8) 64)  ||
                                    (word_extract_byte (w <<  24) 72)  ||
                                    (word_extract_byte (w <<  40) 80)  ||
                                    (word_extract_byte (w <<  56) 88)  ||
                                    (word_extract_byte (w <<  72) 96)  ||
                                    (word_extract_byte (w <<  88) 104) ||
                                    (word_extract_byte (w << 104) 112) ||
                                    (w << 120)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_8_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_byte_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_8_128_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_byte_def, word_lsl_n2w] word_reverse_8_128_ALT_DEF_aux



Definition BExp_word_reverse_8_128_def:
  BExp_word_reverse_8_128 e1 =
      (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 120w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 104w)))
              (BExp_Const (Imm128 0xFF00w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_RightShift e1
                    (BExp_Const (Imm128 88w)))
                 (BExp_Const (Imm128 0xFF0000w)))
              (BExp_BinExp BIExp_Or
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_RightShift e1
                       (BExp_Const (Imm128 72w)))
                    (BExp_Const (Imm128 0xFF000000w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_RightShift e1
                    (BExp_Const (Imm128 56w)))
                 (BExp_Const (Imm128 0xFF00000000w)))
              (BExp_BinExp BIExp_Or
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_RightShift e1
                       (BExp_Const (Imm128 40w)))
                    (BExp_Const (Imm128 0xFF0000000000w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_RightShift e1
                    (BExp_Const (Imm128 24w)))
                 (BExp_Const (Imm128 0xFF000000000000w)))
              (BExp_BinExp BIExp_Or
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_RightShift e1
                       (BExp_Const (Imm128 8w)))
                    (BExp_Const (Imm128 0xFF00000000000000w)))
                 (BExp_BinExp BIExp_Or
                    (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_LeftShift e1
                          (BExp_Const (Imm128 8w)))
                       (BExp_Const (Imm128 0xFF0000000000000000w)))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 24w)))
                          (BExp_Const (Imm128 0xFF000000000000000000w)))
                 (BExp_BinExp BIExp_Or
                    (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_LeftShift e1
                          (BExp_Const (Imm128 40w)))
                       (BExp_Const (Imm128 0xFF00000000000000000000w)))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 56w)))
                          (BExp_Const (Imm128 0xFF0000000000000000000000w)))
                 (BExp_BinExp BIExp_Or
                    (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_LeftShift e1
                          (BExp_Const (Imm128 72w)))
                       (BExp_Const (Imm128 0xFF000000000000000000000000w)))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 88w)))
                          (BExp_Const (Imm128 0xFF00000000000000000000000000w)))
                       (BExp_BinExp BIExp_Or
                          (BExp_BinExp BIExp_And
                             (BExp_BinExp BIExp_LeftShift e1
                                (BExp_Const (Imm128 104w)))
                             (BExp_Const (Imm128 0xFF0000000000000000000000000000w)))
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 120w))))))))))))))))))
End


Definition BExp_word_reverse_8_64_def:
  BExp_word_reverse_8_64 e1 =
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
                             (BExp_Const (Imm64 56w))))))))))
End

Definition BExp_word_reverse_8_32_def:
  BExp_word_reverse_8_32 e1 =
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
                 (BExp_Const (Imm32 24w))))))
End

Definition BExp_word_reverse_8_16_def:
  BExp_word_reverse_8_16 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm16 8w)))
        (BExp_BinExp BIExp_LeftShift e1 (BExp_Const (Imm16 8w))))
End



Theorem BExp_word_reverse_8_16_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_8_16 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_16_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED



Theorem BExp_word_reverse_8_32_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_8_32 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_32_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_8_64_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_8_64 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_64_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_8_128_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_8_128 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_128_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_8_16_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_8_16 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit16)) then SOME (BType_Imm Bit16) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_16_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_8_32_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_8_32 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit32)) then SOME (BType_Imm Bit32) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_32_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_8_64_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_8_64 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit64)) then SOME (BType_Imm Bit64) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_64_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_8_128_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_8_128 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit128)) then SOME (BType_Imm Bit128) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_128_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_word_reverse_8_16_eval:
  !e env. bir_eval_exp (BExp_word_reverse_8_16 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm16 w)) => SOME (BVal_Imm (Imm16 (word_reverse_8_16 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_16_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_8_16_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED

Theorem BExp_word_reverse_8_32_eval:
  !e env. bir_eval_exp (BExp_word_reverse_8_32 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm32 w)) => SOME (BVal_Imm (Imm32 (word_reverse_8_32 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_32_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_8_32_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED


Theorem BExp_word_reverse_8_64_eval:
  !e env. bir_eval_exp (BExp_word_reverse_8_64 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm64 w)) => SOME (BVal_Imm (Imm64 (word_reverse_8_64 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_64_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_8_64_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED


Theorem BExp_word_reverse_8_128_eval:
  !e env. bir_eval_exp (BExp_word_reverse_8_128 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (Imm128 (word_reverse_8_128 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_8_128_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_8_128_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED




(*******************)
(* Reverse Word 16 *)
(*******************)

Definition word_reverse_16_32_def:
  word_reverse_16_32 (w:word32) =
    (((((15 >< 0) w):word16) @@ (((31 >< 16) w):word16)) : word32)
End

Definition word_reverse_16_64_def:
  word_reverse_16_64 (w:word64) =
     (((((15 :num) >< (0 :num)) w :word16) @@
       (((((31 :num) >< (16 :num)) w :word16) @@
        (((((47 :num) >< (32 :num)) w :word16) @@
         (((63 :num) >< (48 :num)) w :word16))
           :word32))
          :word48))
        :word64)
End

Definition word_reverse_16_128_def:
  word_reverse_16_128 (w:word128) =
     (((((15 :num) >< (0 :num)) w :word16) @@
       (((((31 :num) >< (16 :num)) w :word16) @@
        (((((47 :num) >< (32 :num)) w :word16) @@
         (((((63 :num) >< (48 :num)) w :word16) @@
          (((((79 :num) >< (64 :num)) w :word16) @@
           (((((95 :num) >< (80 :num)) w :word16) @@
            (((((111 :num) >< (96 :num)) w :word16) @@
             (((127 :num) >< (112 :num)) w :word16))
           :word32))
          :word48))
        :word64))
           :80 word))
          :96 word))
        :112 word)):word128)
End

Theorem word_reverse_16_32_id:
  !w:word32. word_reverse_16_32 (word_reverse_16_32 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED

Theorem word_reverse_16_64_id:
  !w:word64. word_reverse_16_64 (word_reverse_16_64 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED

Theorem word_reverse_16_128_id:
  !w:word128. word_reverse_16_128 (word_reverse_16_128 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED


Definition word_extract_16bit_def:
  word_extract_16bit (w:'a word) (n:num) =
  (w && ((n2w 65535) << n))
End

Theorem word_extract_16bit_index:
  !w:'a word m n. m < dimindex (:'a) ==>
  ((word_extract_16bit w n) ' m =
  ((w ' m) /\ (n <= m) /\ (m < n + 16)))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_lsl_def, word_and_def, word_index, word_extract_16bit_def] >>

MP_TAC (Q.SPECL [`m-n`, `16`] bitTheory.BIT_EXP_SUB1) >>
ASM_SIMP_TAC arith_ss []
QED




Theorem word_reverse_16_32_ALT_DEF:
  !w:word32. word_reverse_16_32 w = (w >>> 16) || (w << 16)
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_32_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_lsr_def, word_lsl_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_16_64_ALT_DEF_aux[local]:
  !w:word64. word_reverse_16_64 w = (w >>> 48) || (word_extract_16bit (w >>> 16) 16) ||
                                  (word_extract_16bit (w << 16) 32) || (w << 48)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_16bit_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_16_64_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_16bit_def, word_lsl_n2w] word_reverse_16_64_ALT_DEF_aux



Theorem word_reverse_16_128_ALT_DEF_aux[local]:
  !w:word128. word_reverse_16_128 w = (w >>> 112) ||
                                      (word_extract_16bit (w >>> 80) 16) ||
                                      (word_extract_16bit (w >>> 48) 32) ||
                                      (word_extract_16bit (w >>> 16) 48) ||
                                      (word_extract_16bit (w <<  16) 64) ||
                                      (word_extract_16bit (w <<  48) 80) ||
                                      (word_extract_16bit (w <<  80) 96) ||
                                      (w << 112)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_16_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_16bit_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Theorem word_reverse_16_128_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_16bit_def, word_lsl_n2w] word_reverse_16_128_ALT_DEF_aux





Definition BExp_word_reverse_16_128_def:
  BExp_word_reverse_16_128 e1 =
      (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 112w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 80w)))
              (BExp_Const (Imm128 0xFFFF0000w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_RightShift e1
                    (BExp_Const (Imm128 48w)))
                 (BExp_Const (Imm128 0xFFFF00000000w)))
              (BExp_BinExp BIExp_Or
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_RightShift e1
                       (BExp_Const (Imm128 16w)))
                    (BExp_Const (Imm128 0xFFFF000000000000w)))
                 (BExp_BinExp BIExp_Or
                    (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_LeftShift e1
                          (BExp_Const (Imm128 16w)))
                       (BExp_Const (Imm128 0xFFFF0000000000000000w)))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 48w)))
                          (BExp_Const (Imm128 0xFFFF00000000000000000000w)))
                       (BExp_BinExp BIExp_Or
                          (BExp_BinExp BIExp_And
                             (BExp_BinExp BIExp_LeftShift e1
                                (BExp_Const (Imm128 80w)))
                             (BExp_Const (Imm128 0xFFFF000000000000000000000000w)))
                          (BExp_BinExp BIExp_LeftShift e1
                             (BExp_Const (Imm128 112w))))))))))
End

Definition BExp_word_reverse_16_64_def:
  BExp_word_reverse_16_64 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm64 48w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm64 16w)))
              (BExp_Const (Imm64 0xFFFF0000w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_LeftShift e1
                    (BExp_Const (Imm64 16w)))
                 (BExp_Const (Imm64 0xFFFF00000000w)))
              (BExp_BinExp BIExp_LeftShift e1
                 (BExp_Const (Imm64 48w))))))
End

Definition BExp_word_reverse_16_32_def:
  BExp_word_reverse_16_32 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm32 16w)))
        (BExp_BinExp BIExp_LeftShift e1 (BExp_Const (Imm32 16w))))
End


Theorem BExp_word_reverse_16_32_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_16_32 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_32_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_16_64_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_16_64 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_64_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_16_128_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_16_128 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_128_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_word_reverse_16_32_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_16_32 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit32)) then SOME (BType_Imm Bit32) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_32_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_16_64_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_16_64 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit64)) then SOME (BType_Imm Bit64) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_64_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_16_128_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_16_128 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit128)) then SOME (BType_Imm Bit128) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_128_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED



Theorem BExp_word_reverse_16_32_eval:
  !e env. bir_eval_exp (BExp_word_reverse_16_32 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm32 w)) => SOME (BVal_Imm (Imm32 (word_reverse_16_32 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_32_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_16_32_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED


Theorem BExp_word_reverse_16_64_eval:
  !e env. bir_eval_exp (BExp_word_reverse_16_64 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm64 w)) => SOME (BVal_Imm (Imm64 (word_reverse_16_64 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_64_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_16_64_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED


Theorem BExp_word_reverse_16_128_eval:
  !e env. bir_eval_exp (BExp_word_reverse_16_128 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (Imm128 (word_reverse_16_128 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_16_128_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_16_128_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED




(*******************)
(* Reverse Word 32 *)
(*******************)

Definition word_reverse_32_64_def:
  word_reverse_32_64 (w:word64) =
    (((((31 >< 0) w):word32) @@ (((63 >< 32) w):word32)) : word64)
End

Definition word_reverse_32_128_def:
  word_reverse_32_128 (w:word128) =
     (((((31 :num) >< (0 :num)) w :word32) @@
       (((((63 :num) >< (32 :num)) w :word32) @@
        (((((95 :num) >< (64 :num)) w :word32) @@
         (((127 :num) >< (96 :num)) w :word32))
           :word64))
          :word96))
        :word128)
End

Theorem word_reverse_32_64_id:
  !w:word64. word_reverse_32_64 (word_reverse_32_64 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_32_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED

Theorem word_reverse_32_128_id:
  !w:word128. word_reverse_32_128 (word_reverse_32_128 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_32_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED


Definition word_extract_32bit_def:
  word_extract_32bit (w:'a word) (n:num) =
  (w && ((n2w 0xFFFFFFFF) << n))
End

Theorem word_extract_32bit_index:
  !w:'a word m n. m < dimindex (:'a) ==>
  ((word_extract_32bit w n) ' m =
  ((w ' m) /\ (n <= m) /\ (m < n + 32)))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_lsl_def, word_and_def, word_index, word_extract_32bit_def] >>

MP_TAC (Q.SPECL [`m-n`, `32`] bitTheory.BIT_EXP_SUB1) >>
ASM_SIMP_TAC arith_ss []
QED



Theorem word_reverse_32_64_ALT_DEF:
  !w:word64. word_reverse_32_64 w = (w >>> 32) || (w << 32)
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_32_64_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_lsr_def, word_lsl_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED

Theorem word_reverse_32_128_ALT_DEF_aux[local]:
  !w:word128. word_reverse_32_128 w = (w >>> 96) ||
                                      (word_extract_32bit (w >>> 32) 32) ||
                                      (word_extract_32bit (w <<  32) 64) ||
                                      (w << 96)
Proof
GEN_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_32_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_and_def, word_extract_32bit_index, word_lsl_def, word_lsr_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED

Theorem word_reverse_32_128_ALT_DEF = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_extract_32bit_def, word_lsl_n2w] word_reverse_32_128_ALT_DEF_aux




Definition BExp_word_reverse_32_128_def:
  BExp_word_reverse_32_128 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 96w)))
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_And
              (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 32w)))
              (BExp_Const (Imm128 0xFFFFFFFF00000000w)))
           (BExp_BinExp BIExp_Or
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_LeftShift e1
                    (BExp_Const (Imm128 32w)))
                 (BExp_Const (Imm128 0xFFFFFFFF0000000000000000w)))
              (BExp_BinExp BIExp_LeftShift e1
                 (BExp_Const (Imm128 96w))))))
End

Definition BExp_word_reverse_32_64_def:
  BExp_word_reverse_32_64 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm64 32w)))
        (BExp_BinExp BIExp_LeftShift e1 (BExp_Const (Imm64 32w))))
End



Theorem BExp_word_reverse_32_64_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_32_64 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_64_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED

Theorem BExp_word_reverse_32_128_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_32_128 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_128_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED

Theorem BExp_word_reverse_32_64_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_32_64 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit64)) then SOME (BType_Imm Bit64) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_64_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED

Theorem BExp_word_reverse_32_128_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_32_128 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit128)) then SOME (BType_Imm Bit128) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_128_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_word_reverse_32_64_eval:
  !e env. bir_eval_exp (BExp_word_reverse_32_64 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm64 w)) => SOME (BVal_Imm (Imm64 (word_reverse_32_64 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_64_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_32_64_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED

Theorem BExp_word_reverse_32_128_eval:
  !e env. bir_eval_exp (BExp_word_reverse_32_128 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (Imm128 (word_reverse_32_128 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_32_128_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_32_128_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED



(*******************)
(* Reverse Word 64 *)
(*******************)

Definition word_reverse_64_128_def:
  word_reverse_64_128 (w:word128) =
    (((((63 >< 0) w):word64) @@ (((127 >< 64) w):word64)) : word128)
End

Theorem word_reverse_64_128_id:
  !w:word128. word_reverse_64_128 (word_reverse_64_128 w) = w
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_64_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index]
QED


Theorem word_reverse_64_128_ALT_DEF:
  !w:word128. word_reverse_64_128 w = (w >>> 64) || (w << 64)
Proof
Cases >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA,
  word_reverse_64_128_def, word_bits_def, word_extract_def, w2w, word_concat_def, word_join_index,
  word_or_def, word_lsr_def, word_lsl_def] >>
SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []
QED


Definition BExp_word_reverse_64_128_def:
  BExp_word_reverse_64_128 e1 =
     (BExp_BinExp BIExp_Or
        (BExp_BinExp BIExp_RightShift e1 (BExp_Const (Imm128 64w)))
        (BExp_BinExp BIExp_LeftShift e1 (BExp_Const (Imm128 64w))))
End



Theorem BExp_word_reverse_64_128_vars_of:
  !e. bir_vars_of_exp (BExp_word_reverse_64_128 e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_64_128_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED

Theorem BExp_word_reverse_64_128_type_of:
  !e. type_of_bir_exp (BExp_word_reverse_64_128 e) =
      (if (type_of_bir_exp e = SOME (BType_Imm Bit128)) then SOME (BType_Imm Bit128) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_64_128_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_word_reverse_64_128_eval:
  !e env. bir_eval_exp (BExp_word_reverse_64_128 e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (Imm128 (word_reverse_64_128 w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_reverse_64_128_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [word_reverse_64_128_ALT_DEF,
    wordsTheory.word_shift_bv]
)
QED



(********************)
(* Reverse Word ALL *)
(********************)

Theorem BExp_word_reverse_REWRS = LIST_CONJ [
  BExp_word_reverse_1_8_def,
  BExp_word_reverse_1_16_def,
  BExp_word_reverse_1_32_def,
  BExp_word_reverse_1_64_def,
  BExp_word_reverse_1_128_def,
  BExp_word_reverse_8_16_def,
  BExp_word_reverse_8_32_def,
  BExp_word_reverse_8_64_def,
  BExp_word_reverse_8_128_def,
  BExp_word_reverse_16_32_def,
  BExp_word_reverse_16_64_def,
  BExp_word_reverse_16_128_def,
  BExp_word_reverse_32_64_def,
  BExp_word_reverse_32_128_def,
  BExp_word_reverse_64_128_def
]


Theorem word_reverse_REWRS = LIST_CONJ [
  word_reverse_8_16_def,
  word_reverse_8_32_def,
  word_reverse_8_64_def,
  word_reverse_8_128_def,
  word_reverse_16_32_def,
  word_reverse_16_64_def,
  word_reverse_16_128_def,
  word_reverse_32_64_def,
  word_reverse_32_128_def,
  word_reverse_64_128_def
]


Theorem BExp_word_reverse_vars_of = LIST_CONJ [
  BExp_word_reverse_1_vars_of,
  BExp_word_reverse_8_16_vars_of,
  BExp_word_reverse_8_32_vars_of,
  BExp_word_reverse_8_64_vars_of,
  BExp_word_reverse_8_128_vars_of,
  BExp_word_reverse_16_32_vars_of,
  BExp_word_reverse_16_64_vars_of,
  BExp_word_reverse_16_128_vars_of,
  BExp_word_reverse_32_64_vars_of,
  BExp_word_reverse_32_128_vars_of,
  BExp_word_reverse_64_128_vars_of
]


Theorem BExp_word_reverse_type_of = LIST_CONJ [
  BExp_word_reverse_1_type_of,
  BExp_word_reverse_8_16_type_of,
  BExp_word_reverse_8_32_type_of,
  BExp_word_reverse_8_64_type_of,
  BExp_word_reverse_8_128_type_of,
  BExp_word_reverse_16_32_type_of,
  BExp_word_reverse_16_64_type_of,
  BExp_word_reverse_16_128_type_of,
  BExp_word_reverse_32_64_type_of,
  BExp_word_reverse_32_128_type_of,
  BExp_word_reverse_64_128_type_of
]



Theorem BExp_word_reverse_eval = LIST_CONJ [
  BExp_word_reverse_1_eval,
  BExp_word_reverse_8_16_eval,
  BExp_word_reverse_8_32_eval,
  BExp_word_reverse_8_64_eval,
  BExp_word_reverse_8_128_eval,
  BExp_word_reverse_16_32_eval,
  BExp_word_reverse_16_64_eval,
  BExp_word_reverse_16_128_eval,
  BExp_word_reverse_32_64_eval,
  BExp_word_reverse_32_128_eval,
  BExp_word_reverse_64_128_eval
]




(************)
(* word_msb *)
(************)

Definition BExp_MSB_def:
  BExp_MSB sz e =
   BExp_BinPred BIExp_SignedLessThan e (BExp_Const (n2bs 0 sz))
End

Theorem BExp_MSB_vars_of:
  !sz e. bir_vars_of_exp (BExp_MSB sz e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, pred_setTheory.UNION_EMPTY]
QED

Theorem BExp_MSB_type_of:
  !sz e. type_of_bir_exp (BExp_MSB sz e) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_MSB_eval:
  !sz e env. bir_eval_exp (BExp_MSB sz e) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | (Bit128, SOME (BVal_Imm (Imm128 w))) => SOME (BVal_Imm (bool2b (word_msb w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_MSB_def, wordsTheory.word_msb_neg] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
)
QED




(************)
(* word_lsb *)
(************)

Theorem bool2b_word_lsb[local]:
  !w. bool2w (word_lsb w) = w2w w
Proof
SIMP_TAC std_ss [bir_immTheory.bool2w_def, word_lsb_def] >>
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
Cases >> SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [] >>
FULL_SIMP_TAC (arith_ss++wordsLib.WORD_ss ++
  boolSimps.LIFT_COND_ss) [
  fcpTheory.FCP_BETA, w2w]
QED

Definition BExp_LSB_def:
  BExp_LSB e = BExp_Cast BIExp_LowCast e Bit1
End

Theorem BExp_LSB_vars_of:
  !e. bir_vars_of_exp (BExp_LSB e) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def]
QED

Theorem BExp_LSB_type_of:
  !e. type_of_bir_exp (BExp_LSB e) =
      (if (?sz. type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS, BType_Bool_def]
)
QED


Theorem BExp_LSB_eval:
  !e env. bir_eval_exp (BExp_LSB e) env =
     case (bir_eval_exp e env) of
       | SOME (BVal_Imm (Imm1   w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | SOME (BVal_Imm (Imm8   w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | SOME (BVal_Imm (Imm16  w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | SOME (BVal_Imm (Imm32  w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | SOME (BVal_Imm (Imm64  w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | SOME (BVal_Imm (Imm128 w)) => SOME (BVal_Imm (bool2b (word_lsb w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_LSB_def, bir_immTheory.bool2b_def, bool2b_word_lsb] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [w2w_id]
)
QED



(*********************)
(* Word-Bit-Constant *)
(*********************)

Theorem word_bit_ALT_DEF[local]:
  !w n. (word_bit n w = ((w && n2w (2**n)) <> 0w))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
`0 < dimindex (:'a)` by METIS_TAC[DIMINDEX_GT_0] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss++boolSimps.EQUIV_EXTRACT_ss) [
  word_bit_def, word_0, word_and_def, fcpTheory.FCP_BETA, word_index,
  bitTheory.BIT_TWO_POW] >>
DECIDE_TAC
QED


Definition BExp_word_bit_def:
  BExp_word_bit sz e n =
   BExp_BinPred BIExp_NotEqual
   (BExp_BinExp BIExp_And e (BExp_Const (n2bs (2**n) sz))) (BExp_Const (n2bs 0 sz))
End

Theorem BExp_word_bit_vars_of:
  !sz e n. bir_vars_of_exp (BExp_word_bit sz e n) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, pred_setTheory.UNION_EMPTY]
QED

Theorem BExp_word_bit_type_of:
  !sz e n. type_of_bir_exp (BExp_word_bit sz e n) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_word_bit_eval:
  !sz e n env. bir_eval_exp (BExp_word_bit sz e n) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | (Bit128, SOME (BVal_Imm (Imm128 w))) => SOME (BVal_Imm (bool2b (word_bit n w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_def, word_bit_ALT_DEF] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
)
QED




(****************)
(* Word-Bit Exp *)
(****************)

Definition BExp_word_bit_exp_def:
  BExp_word_bit_exp sz e ne =
   BExp_BinPred BIExp_NotEqual
   (BExp_BinExp BIExp_And e (BExp_BinExp BIExp_LeftShift (BExp_Const (n2bs 1 sz)) ne))
      (BExp_Const (n2bs 0 sz))
End

Theorem BExp_word_bit_exp_vars_of:
  !sz e en. bir_vars_of_exp (BExp_word_bit_exp sz e en) = bir_vars_of_exp e UNION bir_vars_of_exp en
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, pred_setTheory.UNION_EMPTY]
QED


Theorem BExp_word_bit_exp_type_of:
  !sz e en. type_of_bir_exp (BExp_word_bit_exp sz e en) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) /\
          (type_of_bir_exp en = SOME (BType_Imm sz)) then SOME BType_Bool else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_word_bit_exp_eval:
  !sz e en env. bir_eval_exp (BExp_word_bit_exp sz e en) env =
     case (sz, bir_eval_exp e env, bir_eval_exp en env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w)), SOME (BVal_Imm (Imm1   wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w)), SOME (BVal_Imm (Imm8   wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w)), SOME (BVal_Imm (Imm16  wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w)), SOME (BVal_Imm (Imm32  wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w)), SOME (BVal_Imm (Imm64  wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | (Bit128, SOME (BVal_Imm (Imm128 w)), SOME (BVal_Imm (Imm128 wn))) =>
            SOME (BVal_Imm (bool2b (word_bit (w2n wn) w)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_word_bit_exp_def, word_bit_ALT_DEF] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  SIMP_TAC std_ss [GSYM wordsTheory.word_1_lsl, GSYM wordsTheory.word_lsl_bv_def]
)
QED



(****************)
(* rotate right *)
(****************)

Theorem word_ror_OR_SHIFT:
  !n w1:'a word w2.
   (dimindex (:'a) = 2**n) ==>

   ((w1 #>>~ w2) = (

   ((w1 >>>~ (w2 && n2w ((2 ** n) - 1))) ||
   (w1 <<~ (n2w (2**n) - (w2 && n2w ((2 ** n) - 1)))))))
Proof
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REPEAT STRIP_TAC >>
Cases_on `w2` >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_ror_bv_def, word_lsl_bv_def,
  word_lsr_def, w2n_n2w, holba_auxiliaryTheory.word_sub_n2w,
  WORD_AND_EXP_SUB1] >>
`n' MOD 2 ** n <= 2 ** n` by METIS_TAC[
  bitTheory.MOD_2EXP_LT, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
`2 ** n < dimword (:'a)` by METIS_TAC[dimindex_lt_dimword] >>
`(2 ** n - n' MOD 2 ** n) MOD dimword (:'a) =
 (2 ** n - n' MOD 2 ** n)` by (

   MATCH_MP_TAC arithmeticTheory.LESS_MOD >> DECIDE_TAC
) >>

ASM_SIMP_TAC arith_ss [Once (GSYM arithmeticTheory.MOD_PLUS)] >>

ASM_SIMP_TAC arith_ss [word_ror_def, GSYM wordsTheory.word_shift_bv, n2w_11,
  fcpTheory.FCP_BETA] >>
`(i + n') MOD 2 ** n = (i + (n' MOD 2 ** n)) MOD 2 ** n` by (
  SIMP_TAC arith_ss [bitTheory.MOD_PLUS_RIGHT]
) >>
Cases_on `n' MOD 2 ** n = 0` >> (
  ASM_SIMP_TAC arith_ss []
) >>
ASM_SIMP_TAC arith_ss [fcpTheory.FCP_BETA, word_lsl_def, word_lsr_def,
  word_or_def] >>
Cases_on `i + n' MOD 2 ** n < 2 ** n` >> (
  ASM_SIMP_TAC arith_ss []
) >>
ASM_SIMP_TAC arith_ss [holba_auxiliaryTheory.MOD_ADD_EQ_SUB]
QED







Definition BExp_ror_exp_def:
  BExp_ror_exp sz e1 e2 =
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_RightShift e1
              (BExp_BinExp BIExp_And e2 (BExp_Const (n2bs (size_of_bir_immtype sz - 1) sz))))
           (BExp_BinExp BIExp_LeftShift e1
              (BExp_BinExp BIExp_Minus (BExp_Const (n2bs (size_of_bir_immtype sz) sz))
                 (BExp_BinExp BIExp_And e2 (BExp_Const (n2bs (size_of_bir_immtype sz - 1) sz))))))
End


Theorem BExp_ror_exp_vars_of:
  !sz e1 e2. bir_vars_of_exp (BExp_ror_exp sz e1 e2) = bir_vars_of_exp e1 UNION bir_vars_of_exp e2
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_ror_exp_def, pred_setTheory.UNION_EMPTY] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [pred_setTheory.EXTENSION, pred_setTheory.IN_UNION]
QED


Theorem BExp_ror_exp_type_of:
  !sz e1 e2. type_of_bir_exp (BExp_ror_exp sz e1 e2) =
      (if (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
          (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME (BType_Imm sz) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ror_exp_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_ror_exp_eval:
  !sz e1 e2 env. bir_eval_exp (BExp_ror_exp sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w1)), SOME (BVal_Imm (Imm1   w2))) =>
            SOME (BVal_Imm (Imm1 (w1 #>>~ w2)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w1)), SOME (BVal_Imm (Imm8   w2))) =>
            SOME (BVal_Imm (Imm8 (w1 #>>~ w2)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w1)), SOME (BVal_Imm (Imm16  w2))) =>
            SOME (BVal_Imm (Imm16 (w1 #>>~ w2)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w1)), SOME (BVal_Imm (Imm32  w2))) =>
            SOME (BVal_Imm (Imm32 (w1 #>>~ w2)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w1)), SOME (BVal_Imm (Imm64  w2))) =>
            SOME (BVal_Imm (Imm64 (w1 #>>~ w2)))
       | (Bit128, SOME (BVal_Imm (Imm128 w1)), SOME (BVal_Imm (Imm128 w2))) =>
            SOME (BVal_Imm (Imm128 (w1 #>>~ w2)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
MP_TAC (SPEC ``0:num`` (INST_TYPE [``:'a`` |-> ``:1``] word_ror_OR_SHIFT)) >>
MP_TAC (SPEC ``3:num`` (INST_TYPE [``:'a`` |-> ``:8``] word_ror_OR_SHIFT)) >>
MP_TAC (SPEC ``4:num`` (INST_TYPE [``:'a`` |-> ``:16``] word_ror_OR_SHIFT)) >>
MP_TAC (SPEC ``5:num`` (INST_TYPE [``:'a`` |-> ``:32``] word_ror_OR_SHIFT)) >>
MP_TAC (SPEC ``6:num`` (INST_TYPE [``:'a`` |-> ``:64``] word_ror_OR_SHIFT)) >>
MP_TAC (SPEC ``7:num`` (INST_TYPE [``:'a`` |-> ``:128``] word_ror_OR_SHIFT)) >>

SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [BExp_ror_exp_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [WORD_AND_CLAUSES]
)
QED



Theorem word_ror_bv_OR_SHIFT:
  !n w:'a word n. n <= dimindex (:'a) ==> (
   (w #>> n) =
   ((w >>> n) || (w << (dimindex (:'a) - n))))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
Cases_on `w` >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_or_def, fcpTheory.FCP_BETA, word_ror_def,
  word_lsl_def, word_lsr_def] >>
REPEAT STRIP_TAC >>
Cases_on `i + n < dimindex (:'a)` >> ASM_SIMP_TAC arith_ss [] >>
Cases_on `n = dimindex (:'a)` >> (
  ASM_SIMP_TAC arith_ss [holba_auxiliaryTheory.MOD_ADD_EQ_SUB,
    arithmeticTheory.ADD_MODULUS]
)
QED



Definition BExp_ror_def:
  BExp_ror sz e n =
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_RightShift e
              (BExp_Const (n2bs n sz)))
           (BExp_BinExp BIExp_LeftShift e
              (BExp_Const (n2bs (size_of_bir_immtype sz - n) sz))))
End


Theorem BExp_ror_vars_of:
  !sz e n. bir_vars_of_exp (BExp_ror sz e n) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_ror_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_ror_type_of:
  !sz e n. type_of_bir_exp (BExp_ror sz e n) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME (BType_Imm sz) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_ror_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_ror_eval:
  !sz e n env.
    n <= size_of_bir_immtype sz ==> (
    bir_eval_exp (BExp_ror sz e n) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,    SOME (BVal_Imm (Imm1   w))) =>
            SOME (BVal_Imm (Imm1 (w #>> n)))
       | (Bit8,    SOME (BVal_Imm (Imm8   w))) =>
            SOME (BVal_Imm (Imm8 (w #>> n)))
       | (Bit16,   SOME (BVal_Imm (Imm16  w))) =>
            SOME (BVal_Imm (Imm16 (w #>> n)))
       | (Bit32,   SOME (BVal_Imm (Imm32  w))) =>
            SOME (BVal_Imm (Imm32 (w #>> n)))
       | (Bit64,   SOME (BVal_Imm (Imm64  w))) =>
            SOME (BVal_Imm (Imm64 (w #>> n)))
       | (Bit128,  SOME (BVal_Imm (Imm128 w))) =>
            SOME (BVal_Imm (Imm128 (w #>> n)))
       | _ => NONE)
Proof
REPEAT STRIP_TAC >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:1``] word_ror_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:8``] word_ror_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:16``] word_ror_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:32``] word_ror_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:64``] word_ror_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:128``] word_ror_bv_OR_SHIFT)) >>

SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [BExp_ror_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [word_lsr_bv_def,
    word_lsl_bv_def, w2n_n2w]
)
QED



(***************)
(* rotate left *)
(***************)

Theorem word_rol_OR_SHIFT:
  !n w1:'a word w2.
   (dimindex (:'a) = 2**n) ==>

   ((w1 #<<~ w2) = (

   ((w1 <<~ (w2 && n2w ((2 ** n) - 1))) ||
   (w1 >>>~ (n2w (2**n) - (w2 && n2w ((2 ** n) - 1)))))))
Proof
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
REPEAT STRIP_TAC >>
Cases_on `w2` >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_rol_bv_def, word_lsl_bv_def,
  word_lsr_def, w2n_n2w, holba_auxiliaryTheory.word_sub_n2w,
  WORD_AND_EXP_SUB1] >>
`n' MOD 2 ** n <= 2 ** n` by METIS_TAC[
  bitTheory.MOD_2EXP_LT, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
`2 ** n < dimword (:'a)` by METIS_TAC[dimindex_lt_dimword] >>
`(2 ** n - n' MOD 2 ** n) MOD dimword (:'a) =
 (2 ** n - n' MOD 2 ** n)` by (

   MATCH_MP_TAC arithmeticTheory.LESS_MOD >> DECIDE_TAC
) >>

ASM_SIMP_TAC arith_ss [word_rol_def, GSYM wordsTheory.word_shift_bv, n2w_11,
  fcpTheory.FCP_BETA, word_ror_def] >>
`(i + n') MOD 2 ** n = (i + (n' MOD 2 ** n)) MOD 2 ** n` by (
  SIMP_TAC arith_ss [bitTheory.MOD_PLUS_RIGHT]
) >>
ASM_SIMP_TAC arith_ss [fcpTheory.FCP_BETA, word_lsl_def, word_lsr_def,
  word_or_def] >>
Cases_on `n' MOD 2 ** n = 0` >> (
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MODULUS]
) >>
Cases_on `n' MOD 2 ** n <= i` >> (
  ASM_SIMP_TAC arith_ss [] >>
  `i + 2 ** n - n' MOD 2 ** n =
   2 ** n + (i - n' MOD 2 ** n)` by DECIDE_TAC >>
  ASM_SIMP_TAC std_ss [arithmeticTheory.ADD_MODULUS] >>
  ASM_SIMP_TAC arith_ss []
) >>
ASM_SIMP_TAC arith_ss [holba_auxiliaryTheory.MOD_ADD_EQ_SUB]
QED





Definition BExp_rol_exp_def:
  BExp_rol_exp sz e1 e2 =
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_LeftShift e1
              (BExp_BinExp BIExp_And e2 (BExp_Const (n2bs (size_of_bir_immtype sz - 1) sz))))
           (BExp_BinExp BIExp_RightShift e1
              (BExp_BinExp BIExp_Minus (BExp_Const (n2bs (size_of_bir_immtype sz) sz))
                 (BExp_BinExp BIExp_And e2 (BExp_Const (n2bs (size_of_bir_immtype sz - 1) sz))))))
End


Theorem BExp_rol_exp_vars_of:
  !sz e1 e2. bir_vars_of_exp (BExp_rol_exp sz e1 e2) = bir_vars_of_exp e1 UNION bir_vars_of_exp e2
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_rol_exp_def, pred_setTheory.UNION_EMPTY] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [pred_setTheory.EXTENSION, pred_setTheory.IN_UNION]
QED


Theorem BExp_rol_exp_type_of:
  !sz e1 e2. type_of_bir_exp (BExp_rol_exp sz e1 e2) =
      (if (type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
          (type_of_bir_exp e2 = SOME (BType_Imm sz)) then SOME (BType_Imm sz) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_rol_exp_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_rol_exp_eval:
  !sz e1 e2 env. bir_eval_exp (BExp_rol_exp sz e1 e2) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w1)), SOME (BVal_Imm (Imm1   w2))) =>
            SOME (BVal_Imm (Imm1 (w1 #<<~ w2)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w1)), SOME (BVal_Imm (Imm8   w2))) =>
            SOME (BVal_Imm (Imm8 (w1 #<<~ w2)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w1)), SOME (BVal_Imm (Imm16  w2))) =>
            SOME (BVal_Imm (Imm16 (w1 #<<~ w2)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w1)), SOME (BVal_Imm (Imm32  w2))) =>
            SOME (BVal_Imm (Imm32 (w1 #<<~ w2)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w1)), SOME (BVal_Imm (Imm64  w2))) =>
            SOME (BVal_Imm (Imm64 (w1 #<<~ w2)))
       | (Bit128, SOME (BVal_Imm (Imm128 w1)), SOME (BVal_Imm (Imm128 w2))) =>
            SOME (BVal_Imm (Imm128 (w1 #<<~ w2)))
       | _ => NONE
Proof
REPEAT GEN_TAC >>
MP_TAC (SPEC ``0:num`` (INST_TYPE [``:'a`` |-> ``:1``] word_rol_OR_SHIFT)) >>
MP_TAC (SPEC ``3:num`` (INST_TYPE [``:'a`` |-> ``:8``] word_rol_OR_SHIFT)) >>
MP_TAC (SPEC ``4:num`` (INST_TYPE [``:'a`` |-> ``:16``] word_rol_OR_SHIFT)) >>
MP_TAC (SPEC ``5:num`` (INST_TYPE [``:'a`` |-> ``:32``] word_rol_OR_SHIFT)) >>
MP_TAC (SPEC ``6:num`` (INST_TYPE [``:'a`` |-> ``:64``] word_rol_OR_SHIFT)) >>
MP_TAC (SPEC ``7:num`` (INST_TYPE [``:'a`` |-> ``:128``] word_rol_OR_SHIFT)) >>

SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [BExp_rol_exp_def] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [WORD_AND_CLAUSES]
)
QED



Theorem word_rol_bv_OR_SHIFT:
  !n w:'a word n. n <= dimindex (:'a) ==> (
   (w #<< n) =
   ((w << n) || (w >>> (dimindex (:'a) - n))))
Proof
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
Cases_on `w` >>
ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_or_def, fcpTheory.FCP_BETA, word_rol_def,
  word_lsl_def, word_lsr_def, word_ror_def] >>
REPEAT STRIP_TAC >>
Cases_on `n <= i` >- (
  ASM_SIMP_TAC arith_ss [] >>
  `i + dimindex (:'a) - n = dimindex (:'a) + (i - n)` by DECIDE_TAC >>
  ASM_SIMP_TAC std_ss [arithmeticTheory.ADD_MODULUS, DIMINDEX_GT_0] >>
  ASM_SIMP_TAC arith_ss []
) >>
ASM_SIMP_TAC arith_ss [] >>
Cases_on `n = dimindex (:'a)` >> (
  ASM_SIMP_TAC arith_ss [holba_auxiliaryTheory.MOD_ADD_EQ_SUB,
    arithmeticTheory.ADD_MODULUS]
)
QED



Definition BExp_rol_def:
  BExp_rol sz e n =
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_LeftShift e
              (BExp_Const (n2bs n sz)))
           (BExp_BinExp BIExp_RightShift e
              (BExp_Const (n2bs (size_of_bir_immtype sz - n) sz))))
End


Theorem BExp_rol_vars_of:
  !sz e n. bir_vars_of_exp (BExp_rol sz e n) = bir_vars_of_exp e
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_rol_def, pred_setTheory.UNION_EMPTY,
  pred_setTheory.UNION_IDEMPOT]
QED


Theorem BExp_rol_type_of:
  !sz e n. type_of_bir_exp (BExp_rol sz e n) =
      (if (type_of_bir_exp e = SOME (BType_Imm sz)) then SOME (BType_Imm sz) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_rol_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_rol_eval:
  !sz e n env.
    n <= size_of_bir_immtype sz ==> (
    bir_eval_exp (BExp_rol sz e n) env =
     case (sz, bir_eval_exp e env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w))) =>
            SOME (BVal_Imm (Imm1   (w #<< n)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w))) =>
            SOME (BVal_Imm (Imm8   (w #<< n)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w))) =>
            SOME (BVal_Imm (Imm16  (w #<< n)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w))) =>
            SOME (BVal_Imm (Imm32  (w #<< n)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w))) =>
            SOME (BVal_Imm (Imm64  (w #<< n)))
       | (Bit128, SOME (BVal_Imm (Imm128 w))) =>
            SOME (BVal_Imm (Imm128 (w #<< n)))
       | _ => NONE)
Proof
REPEAT STRIP_TAC >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:1``] word_rol_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:8``] word_rol_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:16``] word_rol_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:32``] word_rol_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:64``] word_rol_bv_OR_SHIFT)) >>
MP_TAC (GSYM (INST_TYPE [``:'a`` |-> ``:128``] word_rol_bv_OR_SHIFT)) >>

SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [BExp_rol_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [word_lsr_bv_def,
    word_lsl_bv_def, w2n_n2w]
)
QED





(***********)
(* extract *)
(***********)

(* Extract is the underlying operation used to implement ROR on ARM8. However,
   it is also available as a separate assembler instruction and therefore
   modelled explicitly here. *)

Definition word_shift_extract_def:
  word_shift_extract (w1:'a word) (w2:'a word) n =
  ((w2 >>> n) || (w1 << (dimindex (:'a) - n)))
End


Theorem word_shift_extract_ID:
  !n w:'a word. word_shift_extract w w n =
  if (n <= dimindex (:'a)) then (w #>> n) else w
Proof
REPEAT GEN_TAC >>
SIMP_TAC std_ss [word_ror_bv_OR_SHIFT, word_shift_extract_def] >>
Cases_on `dimindex (:'a) < n` >> ASM_SIMP_TAC arith_ss [] >>
`dimindex (:'a) - n = 0` by DECIDE_TAC >>
ASM_SIMP_TAC arith_ss [SHIFT_ZERO, LSR_LIMIT, WORD_OR_CLAUSES]
QED


Theorem word_shift_extract_0:
  !w1:'a word w2. word_shift_extract w1 w2 0 = w2
Proof
SIMP_TAC std_ss [word_shift_extract_def, SHIFT_ZERO, LSL_LIMIT,
  WORD_OR_CLAUSES]
QED

Theorem word_shift_extract_LIMIT:
  !w1:'a word w2 n. dimindex (:'a) <= n ==> (word_shift_extract w1 w2 n = w1)
Proof
REPEAT STRIP_TAC >>
`dimindex (:'a) - n = 0` by DECIDE_TAC >>
ASM_SIMP_TAC std_ss [word_shift_extract_def, SHIFT_ZERO, LSR_LIMIT,
  WORD_OR_CLAUSES]
QED


Definition BExp_extr_def:
  BExp_extr sz e1 e2 n =
        (BExp_BinExp BIExp_Or
           (BExp_BinExp BIExp_RightShift e2
              (BExp_Const (n2bs n sz)))
           (BExp_BinExp BIExp_LeftShift e1
              (BExp_Const (n2bs (size_of_bir_immtype sz - n) sz))))
End

Theorem BExp_extr_ID:
  !sz e n. BExp_extr sz e e n = BExp_ror sz e n
Proof
SIMP_TAC std_ss [BExp_extr_def, BExp_ror_def]
QED


Theorem BExp_extr_vars_of:
  !sz e1 e2 n. bir_vars_of_exp (BExp_extr sz e1 e2 n) = bir_vars_of_exp e1 UNION bir_vars_of_exp e2
Proof
SIMP_TAC (std_ss++holBACore_ss) [BExp_extr_def, pred_setTheory.UNION_EMPTY, pred_setTheory.UNION_COMM]
QED


Theorem BExp_extr_type_of:
  !sz e1 e2 n. type_of_bir_exp (BExp_extr sz e1 e2 n) =
      (if ((type_of_bir_exp e1 = SOME (BType_Imm sz)) /\
          (type_of_bir_exp e2 = SOME (BType_Imm sz))) then SOME (BType_Imm sz) else NONE)
Proof
REPEAT GEN_TAC >>
SIMP_TAC (std_ss++holBACore_ss) [BExp_extr_def, type_of_bir_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_type_checker_DEFS]
)
QED


Theorem BExp_extr_eval:
  !sz e1 e2 n env.
    n <= size_of_bir_immtype sz ==> (
    bir_eval_exp (BExp_extr sz e1 e2 n) env =
     case (sz, bir_eval_exp e1 env, bir_eval_exp e2 env) of
       | (Bit1,   SOME (BVal_Imm (Imm1   w1)), SOME (BVal_Imm (Imm1   w2))) =>
            SOME (BVal_Imm (Imm1   (word_shift_extract w1 w2 n)))
       | (Bit8,   SOME (BVal_Imm (Imm8   w1)), SOME (BVal_Imm (Imm8   w2))) =>
            SOME (BVal_Imm (Imm8   (word_shift_extract w1 w2 n)))
       | (Bit16,  SOME (BVal_Imm (Imm16  w1)), SOME (BVal_Imm (Imm16  w2))) =>
            SOME (BVal_Imm (Imm16  (word_shift_extract w1 w2 n)))
       | (Bit32,  SOME (BVal_Imm (Imm32  w1)), SOME (BVal_Imm (Imm32  w2))) =>
            SOME (BVal_Imm (Imm32  (word_shift_extract w1 w2 n)))
       | (Bit64,  SOME (BVal_Imm (Imm64  w1)), SOME (BVal_Imm (Imm64  w2))) =>
            SOME (BVal_Imm (Imm64  (word_shift_extract w1 w2 n)))
       | (Bit128, SOME (BVal_Imm (Imm128 w1)), SOME (BVal_Imm (Imm128 w2))) =>
            SOME (BVal_Imm (Imm128 (word_shift_extract w1 w2 n)))
       | _ => NONE)
Proof
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss++holBACore_ss++wordsLib.SIZES_ss) [BExp_extr_def,
  pairTheory.pair_case_thm] >>
REPEAT CASE_TAC >> (
  FULL_SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [word_lsr_bv_def,
    word_lsl_bv_def, w2n_n2w, word_shift_extract_def]
)
QED

Definition BExp_IntervalPred_def:
  BExp_IntervalPred e (e_l, e_h) =
    BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual e_l e)
      (BExp_BinPred BIExp_LessOrEqual e e_h)
End

Theorem bir_vars_of_exp_BExp_IntervalPred_thm:
  !e e_l e_h.
    bir_vars_of_exp (BExp_IntervalPred e (e_l, e_h)) =
      (bir_vars_of_exp e UNION
       bir_vars_of_exp e_l UNION
       bir_vars_of_exp e_h)
Proof
  fs [BExp_IntervalPred_def, bir_vars_of_exp_def] >>
  metis_tac [pred_setTheory.UNION_COMM, pred_setTheory.UNION_ASSOC, pred_setTheory.UNION_IDEMPOT]
QED

Theorem bir_eval_exp_BExp_IntervalPred_thm:
  !e e_l e_h env.
    bir_eval_exp (BExp_IntervalPred e (e_l, e_h)) env = (
      bir_eval_bin_exp BIExp_And
        (bir_eval_bin_pred BIExp_LessOrEqual
          (bir_eval_exp e_l env)
          (bir_eval_exp e env))
        (bir_eval_bin_pred BIExp_LessOrEqual
          (bir_eval_exp e env)
          (bir_eval_exp e_h env)))
Proof
  fs [BExp_IntervalPred_def, bir_eval_exp_def]
QED

Theorem type_of_bir_exp_BExp_IntervalPred_thm:
  !e e_l e_h.
    type_of_bir_exp (BExp_IntervalPred e (e_l, e_h)) =
      (case (type_of_bir_exp e, type_of_bir_exp e_l, type_of_bir_exp e_h) of
        (SOME (BType_Imm ty), SOME (BType_Imm lty), SOME (BType_Imm hty)) =>
          (if ((ty = lty) /\ (ty = hty)) then SOME (BType_Imm Bit1) else NONE)
        | _, _ => NONE)
Proof
  fs [BExp_IntervalPred_def, type_of_bir_exp_def] >>
  Cases_on ‘type_of_bir_exp e’ >> Cases_on ‘type_of_bir_exp e_l’ >> Cases_on ‘type_of_bir_exp e_h’ >> (
    EVAL_TAC
  ) >- (
    CASE_TAC
  ) >- (
    CASE_TAC
  ) >- (
    Cases_on ‘x’ >> Cases_on ‘x'’ >> EVAL_TAC >> CASE_TAC
  ) >>

  Cases_on ‘x’ >> Cases_on ‘x'’ >> Cases_on ‘x''’ >> FULL_SIMP_TAC std_ss [bir_type_t_11] >> EVAL_TAC >> CASE_TAC >> (
    FULL_SIMP_TAC std_ss []) >>
  CASE_TAC >> FULL_SIMP_TAC std_ss []
QED

Theorem bir_exp_subst1_BExp_IntervalPred_thm:
  !v ve e e_l e_h.
    bir_exp_subst1 v ve (BExp_IntervalPred e (e_l, e_h)) =
    BExp_IntervalPred (bir_exp_subst1 v ve e) (bir_exp_subst1 v ve e_l, bir_exp_subst1 v ve e_h)
Proof
  fs [BExp_IntervalPred_def, bir_exp_subst1_REWRS]
QED


val _ = export_theory();
