signature bir_computeLib = 
sig
  include Abbrev ;

  val compute_exp_EVAL : term -> term -> thm ;
  val compute_exp_cv : thm -> term -> thm ;
  val translate_exp_cv : thm -> unit ;

  val compute_step_EVAL : term -> term -> thm ;
  val translate_program_cv : thm -> thm ;
  val compute_step_cv :  thm -> term -> thm ;

end
