signature bir_symbLib =
sig

  include Abbrev;

  val bir_symb_analysis_thm : thm -> thm -> thm list -> thm -> thm -> thm;

  val bir_symb_transfer :
    term -> term ->
    term -> term ->
    thm -> thm ->
    thm -> thm -> thm ->
    thm -> thm ->
    thm;

  val bir_symb_transfer_thm :
    thm -> thm -> thm ->
    thm -> thm ->
    thm -> thm ->
    thm -> thm ->
    thm;

  val bir_symb_transfer_two :
    term -> term -> term ->
    term -> term -> term ->
    thm -> thm ->
    thm -> thm -> thm -> thm ->
    thm -> thm ->
    thm;

  val bir_symb_transfer_two_thm :
    thm ->
    thm -> thm -> thm ->
    thm -> thm -> thm ->
    thm -> thm ->
    thm -> thm ->
    thm;

end
