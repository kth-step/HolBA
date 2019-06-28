signature bir_program_no_assumeSyntax =
sig
    include Abbrev

    val bir_prog_has_no_assumes_tm      : term
    val mk_bir_prog_has_no_assumes      : term -> term
    val dest_bir_prog_has_no_assumes    : term -> term
    val is_bir_prog_has_no_assumes      : term -> bool

    val bir_block_has_no_assumes_tm     : term
    val mk_bir_block_has_no_assumes     : term -> term
    val dest_bir_block_has_no_assumes   : term -> term
    val is_bir_block_has_no_assumes     : term -> bool

    val bir_stmtsB_has_no_assumes_tm    : term
    val mk_bir_stmtsB_has_no_assumes    : term -> term
    val dest_bir_stmtsB_has_no_assumes  : term -> term
    val is_bir_stmtsB_has_no_assumes    : term -> bool

    val bir_stmtB_is_not_assume_tm      : term
    val mk_bir_stmtB_is_not_assume      : term -> term
    val dest_bir_stmtB_is_not_assume    : term -> term
    val is_bir_stmtB_is_not_assume      : term -> bool

end
