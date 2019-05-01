signature bir_exp_substitutionsSyntax =
sig
   include Abbrev

   val bir_exp_subst1_tm   : term
   val dest_bir_exp_subst1 : term -> term * term * term
   val is_bir_exp_subst1   : term -> bool
   val mk_bir_exp_subst1   : term * term * term -> term

end
