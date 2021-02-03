signature bir_symb_execLib = sig

  include Abbrev;

  type 'a symb_tree_t;

  val symb_is_BST_Running  : term -> bool

  val symb_is_BST_Halted   : term -> bool

  val symb_is_BST_AssertionViolated : term -> bool

  (* maxdepth (-1 is unlimited), precond, program, pred decider *)
  val symb_exec_program    : int -> term -> term -> (term -> bool) -> (term -> term) option -> term symb_tree_t

  val dest_bir_symb_obs    : term -> term * term * term * term
  val dest_bir_symb_state  : term -> term * term * term * term * term

  val bir_exp_hvar_to_bvar : term -> term

  val symb_exec_leaflist   : 'a symb_tree_t -> 'a list

  val bir_exp_rewrite      : (term -> term) -> term -> term

end
