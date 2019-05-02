signature easy_noproof_wpLib =
sig
  include Abbrev

  val bir_label_to_wps_id_suffix: term -> string
  val compute_wps_tm: string -> thm -> (term list * term) -> term
  val bir_wp_simp: string -> thm -> term -> term -> term -> term

  val compute_p_imp_wp_tm: string -> thm -> (term * term) -> (term list * term) -> term
end
