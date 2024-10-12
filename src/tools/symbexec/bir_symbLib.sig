signature bir_symbLib =
sig

  include Abbrev;

  val birs_simp_select : (term -> thm) ref;

  val bir_symb_analysis_init_gen : term option -> term -> term -> thm -> term * thm * thm;

  val bir_symb_analysis : term -> term list -> term -> thm;

  val bir_symb_analysis_thm : thm -> thm -> thm list -> thm -> thm -> thm * thm;

  val bir_symb_analysis_thm_gen : term option -> thm -> thm -> thm list -> thm -> thm -> thm * thm;

  val bir_symb_transfer :
    term -> term ->
    term -> term ->
    thm -> thm ->
    thm -> thm -> thm ->
    thm -> thm -> thm ->
    thm;

  val bir_symb_transfer_thm :
    thm -> thm -> thm ->
    thm -> thm ->
    thm -> thm ->
    thm -> thm -> thm ->
    thm;

  val bir_symb_transfer_two :
    term -> term -> term ->
    term -> term -> term ->
    thm -> thm ->
    thm -> thm -> thm -> thm ->
    thm -> thm -> thm ->
    thm;

  val bir_symb_transfer_two_thm :
    thm ->
    thm -> thm -> thm ->
    thm -> thm -> thm ->
    thm -> thm ->
    thm -> thm -> thm ->
    thm;

end
