signature bir_cv_programLib =
sig
  include Abbrev;

  val bir_label_exp_conv : conv;
  val bir_stmt_basic_conv : conv;
  val bir_stmt_end_conv : conv;
  val bir_block_conv : conv;
  val bir_program_conv : conv;
  val bir_state_conv : conv;



end
