signature bir_typing_progSyntax =
sig
   include Abbrev

   val bir_vars_of_program_tm   : term
   val dest_bir_vars_of_program : term -> term
   val is_bir_vars_of_program   : term -> bool
   val mk_bir_vars_of_program   : term -> term

end
