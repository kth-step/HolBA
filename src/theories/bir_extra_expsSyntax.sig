signature bir_extra_expsSyntax =
sig

   include Abbrev

   val BExp_Align_tm                    : term
   val BExp_Aligned_tm                  : term
   val BExp_word_reverse_1_8_tm         : term
   val BExp_word_reverse_1_16_tm        : term
   val BExp_word_reverse_1_32_tm        : term
   val BExp_word_reverse_1_64_tm        : term
   val BExp_word_reverse_1_128_tm       : term
   val BExp_word_reverse_8_16_tm        : term
   val BExp_word_reverse_8_32_tm        : term
   val BExp_word_reverse_8_64_tm        : term
   val BExp_word_reverse_8_128_tm       : term
   val BExp_word_reverse_16_32_tm       : term
   val BExp_word_reverse_16_64_tm       : term
   val BExp_word_reverse_16_128_tm      : term
   val BExp_word_reverse_32_64_tm       : term
   val BExp_word_reverse_32_128_tm      : term
   val BExp_word_reverse_64_128_tm      : term
   val BExp_MSB_tm                      : term
   val BExp_LSB_tm                      : term
   val BExp_word_bit_tm                 : term
   val BExp_word_bit_exp_tm             : term
   val BExp_ror_exp_tm                  : term
   val BExp_ror_tm                      : term
   val BExp_rol_exp_tm                  : term
   val BExp_rol_tm                      : term
   val BExp_extr_tm                     : term

   val is_BExp_Align                    : term -> bool
   val is_BExp_Aligned                  : term -> bool
   val is_BExp_word_reverse_1_8         : term -> bool
   val is_BExp_word_reverse_1_16        : term -> bool
   val is_BExp_word_reverse_1_32        : term -> bool
   val is_BExp_word_reverse_1_64        : term -> bool
   val is_BExp_word_reverse_1_128       : term -> bool
   val is_BExp_word_reverse_8_16        : term -> bool
   val is_BExp_word_reverse_8_32        : term -> bool
   val is_BExp_word_reverse_8_64        : term -> bool
   val is_BExp_word_reverse_8_128       : term -> bool
   val is_BExp_word_reverse_16_32       : term -> bool
   val is_BExp_word_reverse_16_64       : term -> bool
   val is_BExp_word_reverse_16_128      : term -> bool
   val is_BExp_word_reverse_32_64       : term -> bool
   val is_BExp_word_reverse_32_128      : term -> bool
   val is_BExp_word_reverse_64_128      : term -> bool
   val is_BExp_MSB                      : term -> bool
   val is_BExp_LSB                      : term -> bool
   val is_BExp_word_bit                 : term -> bool
   val is_BExp_word_bit_exp             : term -> bool
   val is_BExp_ror_exp                  : term -> bool
   val is_BExp_ror                      : term -> bool
   val is_BExp_rol_exp                  : term -> bool
   val is_BExp_rol                      : term -> bool
   val is_BExp_extr                     : term -> bool

   val mk_BExp_Align                    : (term * term) -> term
   val mk_BExp_Aligned                  : (term * term) -> term
   val mk_BExp_word_reverse_1_8         : term -> term
   val mk_BExp_word_reverse_1_16        : term -> term
   val mk_BExp_word_reverse_1_32        : term -> term
   val mk_BExp_word_reverse_1_64        : term -> term
   val mk_BExp_word_reverse_1_128       : term -> term
   val mk_BExp_word_reverse_8_16        : term -> term
   val mk_BExp_word_reverse_8_32        : term -> term
   val mk_BExp_word_reverse_8_64        : term -> term
   val mk_BExp_word_reverse_8_128       : term -> term
   val mk_BExp_word_reverse_16_32       : term -> term
   val mk_BExp_word_reverse_16_64       : term -> term
   val mk_BExp_word_reverse_16_128      : term -> term
   val mk_BExp_word_reverse_32_64       : term -> term
   val mk_BExp_word_reverse_32_128      : term -> term
   val mk_BExp_word_reverse_64_128      : term -> term
   val mk_BExp_MSB                      : (term * term) -> term
   val mk_BExp_LSB                      : (term * term) -> term
   val mk_BExp_word_bit                 : (term * term * term) -> term
   val mk_BExp_word_bit_exp             : (term * term * term) -> term
   val mk_BExp_ror_exp                  : (term * term * term) -> term
   val mk_BExp_ror                      : (term * term * term) -> term
   val mk_BExp_rol_exp                  : (term * term * term) -> term
   val mk_BExp_rol                      : (term * term * term) -> term
   val mk_BExp_extr                     : (term * term * term * term) -> term

   val dest_BExp_Align                  : term -> (term * term)
   val dest_BExp_Aligned                : term -> (term * term)
   val dest_BExp_word_reverse_1_8       : term -> term
   val dest_BExp_word_reverse_1_16      : term -> term
   val dest_BExp_word_reverse_1_32      : term -> term
   val dest_BExp_word_reverse_1_64      : term -> term
   val dest_BExp_word_reverse_1_128     : term -> term
   val dest_BExp_word_reverse_8_16      : term -> term
   val dest_BExp_word_reverse_8_32      : term -> term
   val dest_BExp_word_reverse_8_64      : term -> term
   val dest_BExp_word_reverse_8_128     : term -> term
   val dest_BExp_word_reverse_16_32     : term -> term
   val dest_BExp_word_reverse_16_64     : term -> term
   val dest_BExp_word_reverse_16_128    : term -> term
   val dest_BExp_word_reverse_32_64     : term -> term
   val dest_BExp_word_reverse_32_128    : term -> term
   val dest_BExp_word_reverse_64_128    : term -> term
   val dest_BExp_MSB                    : term -> (term * term)
   val dest_BExp_LSB                    : term -> (term * term)
   val dest_BExp_word_bit               : term -> (term * term * term)
   val dest_BExp_word_bit_exp           : term -> (term * term * term)
   val dest_BExp_ror_exp                : term -> (term * term * term)
   val dest_BExp_ror                    : term -> (term * term * term)
   val dest_BExp_rol_exp                : term -> (term * term * term)
   val dest_BExp_rol                    : term -> (term * term * term)
   val dest_BExp_extr                   : term -> (term * term * term * term)

end
