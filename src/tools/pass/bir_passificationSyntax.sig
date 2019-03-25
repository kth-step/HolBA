signature bir_passificationSyntax =
sig
   include Abbrev

val BExp_Aligned_tm : term
val dest_BExp_Aligned : term -> term * term * term
val is_BExp_Aligned : term -> bool
val mk_BExp_Aligned : term * term * term -> term

val BExp_unchanged_mem_interval_distinct_tm : term
val dest_BExp_unchanged_mem_interval_distinct :
   term -> term * term * term * term * term
val is_BExp_unchanged_mem_interval_distinct : term -> bool
val mk_BExp_unchanged_mem_interval_distinct :
   term * term * term * term * term -> term

end
