structure bir_extra_expsSyntax :> bir_extra_expsSyntax =
struct

  open HolKernel Parse boolLib bossLib
  open Abbrev

  local

  open bir_extra_expsTheory

  val ERR = mk_HOL_ERR "bir_extra_expsSyntax"
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_extra_exps"

  fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
     (fn tm1 => fn e => fn tm2 =>
         if Term.same_const tm1 tm2 then () else raise e)
     (fn tm => fn () => tm) s in (tm, is_f) end;

  val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;

  in

  val (BExp_Align_tm, mk_BExp_Align, dest_BExp_Align, is_BExp_Align)         = syntax_fns3 "BExp_Align"
  val (BExp_Aligned_tm, mk_BExp_Aligned, dest_BExp_Aligned, is_BExp_Aligned) = syntax_fns3 "BExp_Aligned"

  val (BExp_word_reverse_1_8_tm, mk_BExp_word_reverse_1_8, dest_BExp_word_reverse_1_8, is_BExp_word_reverse_1_8)             = syntax_fns1 "BExp_word_reverse_1_8"
  val (BExp_word_reverse_1_16_tm, mk_BExp_word_reverse_1_16, dest_BExp_word_reverse_1_16, is_BExp_word_reverse_1_16)         = syntax_fns1 "BExp_word_reverse_1_16"
  val (BExp_word_reverse_1_32_tm, mk_BExp_word_reverse_1_32, dest_BExp_word_reverse_1_32, is_BExp_word_reverse_1_32)         = syntax_fns1 "BExp_word_reverse_1_32"
  val (BExp_word_reverse_1_64_tm, mk_BExp_word_reverse_1_64, dest_BExp_word_reverse_1_64, is_BExp_word_reverse_1_64)         = syntax_fns1 "BExp_word_reverse_1_64"
  val (BExp_word_reverse_1_128_tm, mk_BExp_word_reverse_1_128, dest_BExp_word_reverse_1_128, is_BExp_word_reverse_1_128)     = syntax_fns1 "BExp_word_reverse_1_128"
  val (BExp_word_reverse_8_16_tm, mk_BExp_word_reverse_8_16, dest_BExp_word_reverse_8_16, is_BExp_word_reverse_8_16)         = syntax_fns1 "BExp_word_reverse_8_16"
  val (BExp_word_reverse_8_32_tm, mk_BExp_word_reverse_8_32, dest_BExp_word_reverse_8_32, is_BExp_word_reverse_8_32)         = syntax_fns1 "BExp_word_reverse_8_32"
  val (BExp_word_reverse_8_64_tm, mk_BExp_word_reverse_8_64, dest_BExp_word_reverse_8_64, is_BExp_word_reverse_8_64)         = syntax_fns1 "BExp_word_reverse_8_64"
  val (BExp_word_reverse_8_128_tm, mk_BExp_word_reverse_8_128, dest_BExp_word_reverse_8_128, is_BExp_word_reverse_8_128)     = syntax_fns1 "BExp_word_reverse_8_128"
  val (BExp_word_reverse_16_32_tm, mk_BExp_word_reverse_16_32, dest_BExp_word_reverse_16_32, is_BExp_word_reverse_16_32)     = syntax_fns1 "BExp_word_reverse_16_32"
  val (BExp_word_reverse_16_64_tm, mk_BExp_word_reverse_16_64, dest_BExp_word_reverse_16_64, is_BExp_word_reverse_16_64)     = syntax_fns1 "BExp_word_reverse_16_64"
  val (BExp_word_reverse_16_128_tm, mk_BExp_word_reverse_16_128, dest_BExp_word_reverse_16_128, is_BExp_word_reverse_16_128) = syntax_fns1 "BExp_word_reverse_16_128"
  val (BExp_word_reverse_32_64_tm, mk_BExp_word_reverse_32_64, dest_BExp_word_reverse_32_64, is_BExp_word_reverse_32_64)     = syntax_fns1 "BExp_word_reverse_32_64"
  val (BExp_word_reverse_32_128_tm, mk_BExp_word_reverse_32_128, dest_BExp_word_reverse_32_128, is_BExp_word_reverse_32_128) = syntax_fns1 "BExp_word_reverse_32_128"
  val (BExp_word_reverse_64_128_tm, mk_BExp_word_reverse_64_128, dest_BExp_word_reverse_64_128, is_BExp_word_reverse_64_128) = syntax_fns1 "BExp_word_reverse_64_128"

  val (BExp_MSB_tm, mk_BExp_MSB, dest_BExp_MSB, is_BExp_MSB) = syntax_fns2 "BExp_MSB"
  val (BExp_LSB_tm, mk_BExp_LSB, dest_BExp_LSB, is_BExp_LSB) = syntax_fns1 "BExp_LSB"

  val (BExp_word_bit_tm, mk_BExp_word_bit, dest_BExp_word_bit, is_BExp_word_bit)                 = syntax_fns3 "BExp_word_bit"
  val (BExp_word_bit_exp_tm, mk_BExp_word_bit_exp, dest_BExp_word_bit_exp, is_BExp_word_bit_exp) = syntax_fns3 "BExp_word_bit_exp"

  val (BExp_ror_tm, mk_BExp_ror, dest_BExp_ror, is_BExp_ror)                 = syntax_fns3 "BExp_ror"
  val (BExp_ror_exp_tm, mk_BExp_ror_exp, dest_BExp_ror_exp, is_BExp_ror_exp) = syntax_fns3 "BExp_ror_exp"
  val (BExp_rol_tm, mk_BExp_rol, dest_BExp_rol, is_BExp_rol)                 = syntax_fns3 "BExp_rol"
  val (BExp_rol_exp_tm, mk_BExp_rol_exp, dest_BExp_rol_exp, is_BExp_rol_exp) = syntax_fns3 "BExp_rol_exp"

  val (BExp_extr_tm, mk_BExp_extr, dest_BExp_extr, is_BExp_extr) = syntax_fns4 "BExp_extr"
    
  val (BExp_IntervalPred_tm,  mk_BExp_IntervalPred, dest_BExp_IntervalPred, is_BExp_IntervalPred)  = syntax_fns2 "BExp_IntervalPred";

  end (* local *)

end (* bir_extra_expsSyntax *)
