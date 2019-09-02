signature bir_typing_expSyntax =
sig
   include Abbrev

   val type_of_bir_exp_tm   : term
   val dest_type_of_bir_exp : term -> term
   val is_type_of_bir_exp   : term -> bool
   val mk_type_of_bir_exp   : term -> term

   val bir_vars_of_exp_tm   : term
   val dest_bir_vars_of_exp : term -> term
   val is_bir_vars_of_exp   : term -> bool
   val mk_bir_vars_of_exp   : term -> term

   val bir_exp_is_well_typed_tm   : term
   val dest_bir_exp_is_well_typed : term -> term
   val is_bir_exp_is_well_typed   : term -> bool
   val mk_bir_exp_is_well_typed   : term -> term

end
