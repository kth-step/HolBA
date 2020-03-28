signature bir_wm_instSyntax =
sig
    include Abbrev

    (*****************************)
    (* bir_map_triple *)
    (*****************************)
    val bir_map_triple_tm    : term
    val mk_bir_map_triple    : (term * term * term * term * term * term) -> term
    val dest_bir_map_triple  : term -> (term * term * term * term * term * term)
    val is_bir_map_triple    : term -> bool

end
