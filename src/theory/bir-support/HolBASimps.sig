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

  (* Simplification set fragment for deciding booleanity
   * of expression *)
  val bir_is_bool_ss : simpLib.ssfrag

  (* Simplification set for use with bir_env_read *)
  val bir_type_val_opt_ss : simpLib.ssfrag
end
