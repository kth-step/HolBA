signature tutorial_compositionLib =
sig
  include Abbrev

  val get_contract_prog: thm -> term;
  val get_contract_l: thm -> term;
  val get_contract_ls: thm -> term;
  val get_contract_pre: thm -> term;
  val get_contract_post: thm -> term;

  val get_bir_map_triple_prog: thm -> term
  val get_bir_map_triple_invariant: thm -> term
  val get_bir_map_triple_start_label: thm -> term
  val get_bir_map_triple_wlist: thm -> term
  val get_bir_map_triple_blist: thm -> term
  val get_bir_map_triple_pre: thm -> term
  val get_bir_map_triple_post: thm -> term

  val vars_ss: simpset;

  val bir_map_triple_from_bir_triple: thm -> thm;

  val bir_remove_labels_from_ending_set : thm -> term -> thm;

  val bir_compose_loop: thm -> thm -> term -> term -> term -> thm list -> thm;

  val bir_compose_seq: thm -> thm -> thm list -> thm;
  val bir_compose_nonmap_seq: thm -> thm -> thm list -> thm;
  val bir_compose_nonmap1_seq: thm -> thm -> thm list -> thm;

end
