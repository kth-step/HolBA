signature bir_computeLib = 
sig
  include Abbrev;

  val compute_exp_EVAL : term -> term -> thm;
  val compute_exp_cv : thm -> term -> thm;
  val translate_exp_cv : thm -> unit;

  (* These functions usually aren’t necessary outside of the library *)
  val deep_embed_label_exp : string -> term -> thm option;
  val deep_embed_basic_stmt : string -> term -> thm;
  val deep_embed_end_stmt : string -> term -> thm;
  val deep_embed_block : string -> term -> thm;
  val deep_embed_state : string -> term -> thm;
  val deep_embed_program : string -> term -> thm;

  val compute_step_EVAL : term -> term -> thm;
  val translate_program_cv : thm -> thm;
  val compute_step_cv :  thm -> term -> thm;

end
