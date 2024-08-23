signature smtArraySyntax =
sig
    include Abbrev

    val store_tm         : term
    val select_tm        : term
    val const_array_tm   : term

    val mk_store         : (term * term * term) -> term
    val mk_select        : (term * term) -> term
    val mk_const_array   : (hol_type * term) -> term

    val dest_store       : term -> (term * term * term)
    val dest_select      : term -> (term * term)
    (* val dest_const_array : term -> (hol_type * term) *)

    val is_store         : term -> bool
    val is_select        : term -> bool
    val is_const_array   : term -> bool

end
