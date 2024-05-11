signature bir_symbLib =
sig

  include Abbrev;

  val mem_addrs_aligned_prog_disj_tm : string -> term;

  val pre_vals_reg_tm : string -> string -> term;

  val pre_vals_mem_reg_tm : string -> string -> term;

  val pre_vals_tm : string -> string -> string -> term;

  val bir_symb_analysis : term -> term -> term list -> term -> term -> thm;

end
