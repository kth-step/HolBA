signature bir_htLib =
sig
  include Abbrev

  val bir_stmtb_is_not_assume_pp : term -> thm
  val bir_stmtsB_has_no_assumes_pp : term -> thm
  val bir_block_has_no_assumes_pp : term -> thm
  val bir_prog_has_no_assumes_pp : term -> thm

end
