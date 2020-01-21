signature tutorial_wpSupportLib =
sig
   include Abbrev

  val eot : term -> term
  val get_wp_from_ht : thm -> term

  val bir_obtain_ht : term -> term -> term -> term -> string -> term list -> thm * thm list

  val ending_lam_disj_to_sml_list : term -> term list
  val ending_set_to_sml_list : term -> term list
  val postcond_exp_from_label : term -> term -> term

  val prove_imp_w_smt : term -> term -> thm

end
