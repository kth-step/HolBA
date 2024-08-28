signature bir_symbLib =
sig

  include Abbrev;

  val bir_symb_analysis : term -> term -> term list -> term -> term -> thm;

  val bir_symb_analysis_thm : thm -> thm -> thm list -> thm -> thm -> thm * thm;

  val bir_symb_transfer : term -> term -> term -> term ->
    thm -> thm -> thm -> thm -> thm ->
    thm -> thm -> thm -> thm;

end
