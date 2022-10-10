signature evalwrapLib =
sig

  include Abbrev
  val eval_ctxt_gen : term list -> term list -> term list -> term -> thm
  val qeval_ctxt : term frag list list -> term frag list -> thm

end
