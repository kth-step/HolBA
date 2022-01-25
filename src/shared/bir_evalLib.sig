signature bir_evalLib =
sig
  include Abbrev;
  val bir_eval_exec : term -> term -> term list * term

end
