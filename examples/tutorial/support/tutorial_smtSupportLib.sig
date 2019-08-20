signature tutorial_smtSupportLib =
sig
  include Abbrev

  val Z3_prove_or_print_model: term -> thm

  val prove_exp_is_taut: term -> thm

  (* TODO: Move bimp to bslSyntax *)
  val bimp: term * term -> term

end
