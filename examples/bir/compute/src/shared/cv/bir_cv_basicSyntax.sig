signature bir_cv_basicSyntax = 
sig
  include Abbrev;

  val cv_val_imm_tm : term;
  val cv_val_mem_tm : term;
  val cv_exp_const_tm : term;
  val cv_exp_mem_const_tm : term;
  val cv_exp_den_tm : term;
  val cv_exp_bin_exp_tm : term;
  val cv_exp_unary_exp_tm : term;
  val cv_exp_bin_pred_tm : term;
  val cv_exp_if_then_else_tm : term;
  val cv_exp_load_tm : term;
  val cv_exp_store_tm : term;

  val mk_cv_val_imm : term -> term;
  val mk_cv_val_mem : (term * term * term) -> term;
  val mk_cv_exp_const : term -> term;
  val mk_cv_exp_mem_const : (term * term * term) -> term;
  val mk_cv_exp_den : term -> term;
  val mk_cv_exp_bin_exp : (term * term * term) -> term;
  val mk_cv_exp_unary_exp : (term * term) -> term;
  val mk_cv_exp_bin_pred : (term * term * term) -> term;
  val mk_cv_exp_if_then_else : (term * term * term) -> term;
  val mk_cv_exp_load : (term * term * term * term) -> term;
  val mk_cv_exp_store : (term * term * term * term) -> term;

  val is_cv_val_imm : term -> bool;
  val is_cv_val_mem : term -> bool;
  val is_cv_exp_const : term -> bool;
  val is_cv_exp_mem_const : term -> bool;
  val is_cv_exp_den : term -> bool;
  val is_cv_exp_bin_exp : term -> bool;
  val is_cv_exp_unary_exp : term -> bool;
  val is_cv_exp_bin_pred : term -> bool;
  val is_cv_exp_if_then_else : term -> bool;
  val is_cv_exp_load : term -> bool;
  val is_cv_exp_store : term -> bool;

  val dest_cv_val_imm : term -> term;
  val dest_cv_val_mem : term -> (term * term * term);
  val dest_cv_exp_const : term -> term;
  val dest_cv_exp_mem_const : term -> (term * term * term);
  val dest_cv_exp_den : term -> term;
  val dest_cv_exp_bin_exp : term -> (term * term * term);
  val dest_cv_exp_unary_exp : term -> (term * term);
  val dest_cv_exp_bin_pred : term -> (term * term * term);
  val dest_cv_exp_if_then_else : term -> (term * term * term);
  val dest_cv_exp_load : term -> (term * term * term * term);
  val dest_cv_exp_store : term -> (term * term * term * term);



end
