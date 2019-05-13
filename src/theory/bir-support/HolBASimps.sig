signature HolBASimps =
sig
   include Abbrev

   (* Rewrite rules to determine statements of a program *)
   val stmts_of_prog_ss : simpLib.ssfrag;

   (* Rewrite rules to determine variables of a program *)
   val vars_of_prog_ss : simpLib.ssfrag;

end
