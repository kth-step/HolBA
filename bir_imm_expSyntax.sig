signature bir_imm_expSyntax =
sig
   include Abbrev


   (*******************)
   (* bir_unary_exp_t *)
   (*******************)

   val bir_unary_exp_t_ty  : hol_type

   val BIExp_Not_tm        : term
   val BIExp_ChangeSign_tm : term

   val is_BIExp_Not        : term -> bool
   val is_BIExp_ChangeSign : term -> bool

   val bir_unary_exp_tm    : term;
   val mk_bir_unary_exp    : term * term -> term;
   val dest_bir_unary_exp  : term -> term * term;
   val is_bir_unary_exp    : term -> bool;

   (*****************)
   (* bir_bin_exp_t *)
   (*****************)

   val bir_bin_exp_t_ty          : hol_type

   val BIExp_And_tm              : term
   val BIExp_Div_tm              : term
   val BIExp_LeftShift_tm        : term
   val BIExp_Minus_tm            : term
   val BIExp_Mod_tm              : term
   val BIExp_Mult_tm             : term
   val BIExp_Or_tm               : term
   val BIExp_Plus_tm             : term
   val BIExp_RightShift_tm       : term
   val BIExp_SignedDiv_tm        : term
   val BIExp_SignedMod_tm        : term
   val BIExp_SignedRightShift_tm : term
   val BIExp_Xor_tm              : term

   val is_BIExp_And              : term -> bool
   val is_BIExp_Div              : term -> bool
   val is_BIExp_LeftShift        : term -> bool
   val is_BIExp_Minus            : term -> bool
   val is_BIExp_Mod              : term -> bool
   val is_BIExp_Mult             : term -> bool
   val is_BIExp_Or               : term -> bool
   val is_BIExp_Plus             : term -> bool
   val is_BIExp_RightShift       : term -> bool
   val is_BIExp_SignedDiv        : term -> bool
   val is_BIExp_SignedMod        : term -> bool
   val is_BIExp_SignedRightShift : term -> bool
   val is_BIExp_Xor              : term -> bool

   val bir_bin_exp_tm            : term;
   val mk_bir_bin_exp            : term * term * term -> term;
   val dest_bir_bin_exp          : term -> term * term * term;
   val is_bir_bin_exp            : term -> bool;


   (******************)
   (* bir_bin_pred_t *)
   (******************)

   val bir_bin_pred_t_ty          : hol_type

   val BIExp_Equal_tm             : term
   val BIExp_LessOrEqual_tm       : term
   val BIExp_LessThan_tm          : term
   val BIExp_NotEqual_tm          : term
   val BIExp_SignedLessOrEqual_tm : term
   val BIExp_SignedLessThan_tm    : term

   val is_BIExp_Equal             : term -> bool
   val is_BIExp_LessOrEqual       : term -> bool
   val is_BIExp_LessThan          : term -> bool
   val is_BIExp_NotEqual          : term -> bool
   val is_BIExp_SignedLessOrEqual : term -> bool
   val is_BIExp_SignedLessThan    : term -> bool

   val bir_bin_pred_tm            : term;
   val mk_bir_bin_pred            : term * term * term -> term;
   val dest_bir_bin_pred          : term -> term * term * term;
   val is_bir_bin_pred            : term -> bool;


   (******************)
   (* bir_cast_t     *)
   (******************)

   val bir_cast_t_ty         : hol_type

   val BIExp_HighCast_tm     : term
   val BIExp_LowCast_tm      : term
   val BIExp_SignedCast_tm   : term
   val BIExp_UnsignedCast_tm : term

   val is_BIExp_HighCast     : term -> bool
   val is_BIExp_LowCast      : term -> bool
   val is_BIExp_SignedCast   : term -> bool
   val is_BIExp_UnsignedCast : term -> bool

   val bir_gencast_tm        : term;
   val mk_bir_gencast        : term * term * term -> term;
   val dest_bir_gencast      : term -> term * term * term;
   val is_bir_gencast        : term -> bool;

end
