signature bir_auxiliaryLib =
sig
  include Abbrev
  type simpset = simpLib.simpset

  val QSPECL_ASSUM : term -> Q.tmquote list -> tactic
  val QSPECL_X_ASSUM : term -> Q.tmquote list -> tactic
  val FULLSIMP_BY_THM : simpset -> thm -> tactic

end
