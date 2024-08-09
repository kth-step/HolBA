signature bir_cv_programSyntax =
sig
  include Abbrev ;

  val cv_le_label_tm : term ;
  val cv_le_exp_tm : term ;
  val cv_stmt_assign_tm : term ;
  val cv_stmt_jmp_tm : term ;
  val cv_stmt_cjmp_tm : term ;
  val cv_program_tm : term ;


  val mk_cv_le_label : term -> term ;
  val mk_cv_le_exp : term -> term ;
  val mk_cv_stmt_assign : (term * term) -> term ;
  val mk_cv_stmt_jmp : term -> term ;
  val mk_cv_stmt_cjmp : (term * term * term) -> term ;
  val mk_cv_block : (term * term * term) -> term ;
  val mk_cv_program : term -> term ;
  val mk_cv_state : (term * term * term) -> term ;

  val dest_cv_le_label : term -> term ;
  val dest_cv_le_exp : term -> term ;
  val dest_cv_stmt_assign : term -> (term * term) ;
  val dest_cv_stmt_jmp : term -> term ;
  val dest_cv_stmt_cjmp : term -> (term * term * term) ;
  val dest_cv_block : term -> (term * term * term) ;
  val dest_cv_program : term -> term ;
  val dest_cv_state : term -> (term * term * term) ;

  val is_cv_le_label : term -> bool ;
  val is_cv_le_exp : term -> bool ;
  val is_cv_stmt_assign : term -> bool ;
  val is_cv_stmt_jmp : term -> bool ;
  val is_cv_stmt_cjmp : term -> bool ;
  val is_cv_block : term -> bool ;
  val is_cv_program : term -> bool ;
  val is_cv_state : term -> bool ;


end
