signature bir_multicoreSyntax =
sig
   include Abbrev


   val core_tm      : term;
   val mk_core      : term * term * term -> term;
   val dest_core    : term -> term * term * term;
   val is_core      : term -> bool;

   val mem_tm      : term;
   val mk_mem      : term -> term;
   val dest_mem    : term -> term;
   val is_mem      : term -> bool;

end
