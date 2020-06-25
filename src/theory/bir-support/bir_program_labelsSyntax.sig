signature bir_program_labelsSyntax =
sig
   include Abbrev

   (***************)
   (* bir_label_t *)
   (***************)

   val BL_Address_HC_tm   : term
   val dest_BL_Address_HC : term -> term * term
   val is_BL_Address_HC   : term -> bool
   val mk_BL_Address_HC   : term * term -> term

end
