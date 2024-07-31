signature bir_basicSyntax = 
sig
  include Abbrev ;

  val val_imm_tm : term ;
  val val_mem_tm : term ;

  val is_val_imm : term -> bool ;
  val is_val_mem : term -> bool ;

  val dest_val_imm : term -> term ;
  val dest_val_mem : term -> (term * term * term) ;



end
