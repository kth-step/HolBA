signature bir_wm_instSyntax =
sig
    include Abbrev

    (*****************)
    (* bir_simp_jgmt *)
    (*****************)
    val bir_simp_jgmt_tm    : term
    val mk_bir_simp_jgmt    : (term * term * term * term * term * term * term) -> term
    val dest_bir_simp_jgmt  : term -> (term * term * term * term * term * term * term)
    val is_bir_simp_jgmt    : term -> bool

end
