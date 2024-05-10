signature bir_symbLib =
sig

  include Abbrev;

  val bir_symb_analysis : term -> term -> term list -> term -> term -> thm;

end
