signature bir_symbLib =
sig

  include Abbrev;

  val mem_addrs_prog_disj_bir_tm : string -> term;

  val mem_addrs_aligned_prog_disj_bir_tm : string -> term;

  val mem_addrs_aligned_prog_disj_riscv_tm : string -> term;

  val pre_vals_reg_bir_tm : string -> string -> term;

  val pre_vals_mem_reg_bir_tm : string -> string -> string -> term;

  val pre_vals_bir_tm : string -> string -> string -> string -> term;

  val bir_symb_analysis : term -> term -> term list -> term -> term -> thm;

  val bir_symb_analysis_thm : thm -> thm -> thm list -> thm -> thm -> thm * thm;

  val bir_symb_transfer : term -> term -> term -> term ->
    thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm;

end
