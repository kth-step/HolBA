signature bir_programSyntax =
sig
  include Abbrev;

  val le_label_tm : term;
  val le_exp_tm : term;
  val stmt_assign_tm : term;
  val stmt_jmp_tm : term;
  val stmt_cjmp_tm : term;
  val program_tm : term;


  val mk_le_label : term -> term;
  val mk_le_exp : term -> term;
  val mk_stmt_assign : (term * term) -> term;
  val mk_stmt_jmp : term -> term;
  val mk_stmt_cjmp : (term * term * term) -> term;
  val mk_block : (term * term * term) -> term;
  val mk_program : term -> term;
  val mk_programcounter : (term * term) -> term;
  val mk_state : (term * term * term) -> term;

  val dest_le_label : term -> term;
  val dest_le_exp : term -> term;
  val dest_stmt_assign : term -> (term * term);
  val dest_stmt_jmp : term -> term;
  val dest_stmt_cjmp : term -> (term * term * term);
  val dest_block : term -> (term * term * term);
  val dest_program : term -> term;
  val dest_programcounter : term -> (term * term);
  val dest_state : term -> (term * term * term);

  val is_le_label : term -> bool;
  val is_le_exp : term -> bool;
  val is_stmt_assign : term -> bool;
  val is_stmt_jmp : term -> bool;
  val is_stmt_cjmp : term -> bool;
  val is_block : term -> bool;
  val is_program : term -> bool;
  val is_programcounter : term -> bool;
  val is_state : term -> bool;


end
