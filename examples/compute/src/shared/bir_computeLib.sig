signature bir_computeLib = 
sig
  include Abbrev ;

  val compute_exp_EVAL : term -> term -> thm
  val compute_exp_cv : thm -> term -> thm


end
