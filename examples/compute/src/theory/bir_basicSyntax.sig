signature bir_basicSyntax = 
sig
  include Abbrev ;

  val val_imm_tm : term ;
  val val_mem_tm : term ;
  val exp_const_tm : term ;
  val exp_mem_const_tm : term ;
  val exp_den_tm : term ;
  val exp_bin_exp_tm : term ;
  val exp_unary_exp_tm : term ;
  val exp_bin_pred_tm : term ;
  val exp_if_then_else_tm : term ;
  val exp_load_tm : term ;
  val exp_store_tm : term ;

  val is_val_imm : term -> bool ;
  val is_val_mem : term -> bool ;
  val is_exp_const : term -> bool ;
  val is_exp_mem_const : term -> bool ;
  val is_exp_den : term -> bool ;
  val is_exp_bin_exp : term -> bool ;
  val is_exp_unary_exp : term -> bool ;
  val is_exp_bin_pred : term -> bool ;
  val is_exp_if_then_else : term -> bool ;
  val is_exp_load : term -> bool ;
  val is_exp_store : term -> bool ;

  val dest_val_imm : term -> term ;
  val dest_val_mem : term -> (term * term * term) ;
  val dest_exp_const : term -> term;
  val dest_exp_mem_const : term -> (term * term * term) ;
  val dest_exp_den : term -> term ;
  val dest_exp_bin_exp : term -> (term * term * term) ;
  val dest_exp_unary_exp : term -> (term * term) ;
  val dest_exp_bin_pred : term -> (term * term * term) ;
  val dest_exp_if_then_else : term -> (term * term * term) ;
  val dest_exp_load : term -> (term * term * term * term) ;
  val dest_exp_store : term -> (term * term * term * term) ;



end
