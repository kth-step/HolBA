signature tutorial_smtSupportLib =
sig
  include Abbrev

  val prove_exp_is_taut: term -> thm

  (* TODO: Move bimp to bslSyntax *)
  val bimp: term * term -> term

end
