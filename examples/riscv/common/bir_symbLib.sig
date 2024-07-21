signature bir_symbLib =
sig

  include Abbrev;

  val gen_prog_vars_birenvtyl_defthms : string -> thm -> unit;

(*
  val bir_symb_analysis : term -> term -> term list -> term -> term -> thm;
*)

  val bir_symb_analysis_thm : thm -> thm -> thm list -> thm -> thm -> thm * thm;

  val bir_symb_transfer : term -> term -> term -> term ->
    thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm;

end
