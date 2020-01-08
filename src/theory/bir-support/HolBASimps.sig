signature HolBASimps =
sig
   include Abbrev

   (* List of definitions and vars_of theorems for use
    * when determining variables of BIR expressions *)
   val common_exp_defs : thm list;

   (* Rewrite rules to determine statements of a program *)
   val STMTS_OF_PROG_ss : simpLib.ssfrag;

   (* Rewrite rules to determine variables of a program *)
   val VARS_OF_PROG_ss : simpLib.ssfrag;

end
