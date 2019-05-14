signature HolBASimps =
sig
   include Abbrev

   (* Rewrite rules to determine statements of a program *)
   val STMTS_OF_PROG_ss : simpLib.ssfrag;

   (* Rewrite rules to determine variables of a program *)
   val VARS_OF_PROG_ss : simpLib.ssfrag;

end
