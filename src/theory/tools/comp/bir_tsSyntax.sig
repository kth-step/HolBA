signature bir_tsSyntax =
sig
    include Abbrev

    (************)
    (* bir_cont *)
    (*************)
    val bir_cont_tm    : term
    val mk_bir_cont    : (term * term * term * term * term * term * term) -> term
    val dest_bir_cont  : term -> (term * term * term * term * term * term * term)
    val is_bir_cont    : term -> bool

end
