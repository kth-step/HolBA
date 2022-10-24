signature evalwrapLib =
sig

  include Abbrev
  val eval_ctxt_gen : term list -> term list -> thm -> term -> thm
  val qeval_ctxt : term frag list list -> term frag list -> thm
  val eval_ctxt_unify : term list -> term list -> term -> term -> thm

end
