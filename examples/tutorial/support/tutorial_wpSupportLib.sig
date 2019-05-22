signature tutorial_wpSupportLib =
sig
   include Abbrev

  val bir_obtain_ht : term -> term -> term -> term -> string -> term list -> thm * thm list

  val prove_imp_w_smt : term -> term -> thm

end
