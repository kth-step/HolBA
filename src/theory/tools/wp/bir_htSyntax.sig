signature bir_htSyntax =
sig
    include Abbrev

    (*****************************)
    (* bir_exec_to_labels_triple *)
    (*****************************)
    val bir_exec_to_labels_triple_tm    : term
    val mk_bir_exec_to_labels_triple    : (term * term * term * term * term) -> term
    val dest_bir_exec_to_labels_triple  : term -> (term * term * term * term * term)
    val is_bir_exec_to_labels_triple    : term -> bool

end
