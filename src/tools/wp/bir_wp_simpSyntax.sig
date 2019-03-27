signature bir_wp_simpSyntax =
sig
   include Abbrev

  val bir_exp_imp_tm: term
  val mk_bir_exp_imp: term * term -> term
  val dest_bir_exp_imp: term -> term * term
  val is_bir_exp_imp: term -> bool

  val bir_exp_and_tm: term
  val mk_bir_exp_and: term * term -> term
  val dest_bir_exp_and: term -> term * term
  val is_bir_exp_and: term -> bool

  val bir_exp_varsubst_tm: term
  val mk_bir_exp_varsubst: term * term -> term
  val dest_bir_exp_varsubst: term -> term * term
  val is_bir_exp_varsubst: term -> bool

  val bir_exp_varsubst1_tm: term
  val mk_bir_exp_varsubst1: term * term * term -> term
  val dest_bir_exp_varsubst1: term -> term * term * term
  val is_bir_exp_varsubst1: term -> bool

end
