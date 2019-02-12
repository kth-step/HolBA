signature bir_expSyntax =
sig
   include Abbrev

   (*************)
   (* bir_exp_t *)
   (*************)

   (* The type itself *)
   val bir_exp_t_ty : hol_type

   val BExp_BinExp_tm       : term;
   val BExp_BinPred_tm      : term;
   val BExp_MemEq_tm        : term;
   val BExp_Cast_tm         : term;
   val BExp_Const_tm        : term;
   val BExp_Den_tm          : term;
   val BExp_IfThenElse_tm   : term;
   val BExp_Load_tm         : term;
   val BExp_Store_tm        : term;
   val BExp_UnaryExp_tm     : term;

   val dest_BExp_BinExp     : term -> term * term * term;
   val dest_BExp_BinPred    : term -> term * term * term;
   val dest_BExp_MemEq      : term -> term * term;
   val dest_BExp_Cast       : term -> term * term * term;
   val dest_BExp_Const      : term -> term;
   val dest_BExp_Den        : term -> term;
   val dest_BExp_IfThenElse : term -> term * term * term;
   val dest_BExp_Load       : term -> term * term * term * term;
   val dest_BExp_Store      : term -> term * term * term * term;
   val dest_BExp_UnaryExp   : term -> term * term;

   val is_BExp_BinExp       : term -> bool;
   val is_BExp_BinPred      : term -> bool;
   val is_BExp_MemEq        : term -> bool;
   val is_BExp_Cast         : term -> bool;
   val is_BExp_Const        : term -> bool;
   val is_BExp_Den          : term -> bool;
   val is_BExp_IfThenElse   : term -> bool;
   val is_BExp_Load         : term -> bool;
   val is_BExp_Store        : term -> bool;
   val is_BExp_UnaryExp     : term -> bool;

   val mk_BExp_BinExp       : term * term * term -> term;
   val mk_BExp_BinPred      : term * term * term -> term;
   val mk_BExp_MemEq        : term * term -> term;
   val mk_BExp_Cast         : term * term * term -> term;
   val mk_BExp_Const        : term -> term;
   val mk_BExp_Den          : term -> term;
   val mk_BExp_IfThenElse   : term * term * term -> term;
   val mk_BExp_Load         : term * term * term * term -> term;
   val mk_BExp_Store        : term * term * term * term -> term;
   val mk_BExp_UnaryExp     : term * term -> term;

   val bir_eval_exp_tm      : term;
   val mk_bir_eval_exp      : term * term -> term;
   val dest_bir_eval_exp    : term -> term * term;
   val is_bir_eval_exp      : term -> bool;

end
