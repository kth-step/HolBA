signature bir_evalLib =
sig
  include Abbrev;
  val bir_eval_exec_n : term -> term -> int -> term list * term
  val bir_eval_exec : term -> term -> term list * term
  val bir_eval_mem_exec : term -> term -> term list * term
end
