signature bir_auxiliaryLib =
sig
  include Abbrev
  type simpset = simpLib.simpset

  val QSPECL_ASSUM : term -> Q.tmquote list -> tactic
  val QSPECL_X_ASSUM : term -> Q.tmquote list -> tactic
  val FULLSIMP_BY_THM : simpset -> thm -> tactic

  val HO_MATCH_MPL : thm -> thm list -> thm

  val ins_sort_tm : term list -> term list

  val list_split_pred : ''a -> ''a list -> ''a list * ''a list
end
