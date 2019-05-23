signature tutorial_smtSupportLib =
sig
   include Abbrev

   val prove_bir_eval_exp_with_SMT_then_cheat_TAC: tactic

   val prove_exp_is_taut: term -> thm

   val bimp: term * term -> term

   val save_exp_is_taut_imp : string * term * term -> thm

end
