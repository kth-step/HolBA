signature bir_predLib =
sig

  include Abbrev;

  val mem_area_disj_reg_bir_tm : string * int -> string * int -> term;

  val mem_addrs_stack_disj_reg_bir_tm : string -> string -> term;

  val mem_params_standard : term * term;
(*
  val mem_addrs_prog_disj_bir_tm : term * term -> string -> term;
*)
  val mem_addrs_aligned_prog_disj_bir_tm : term * term -> string -> term;

  val mem_addrs_aligned_prog_disj_riscv_tm : term * term -> string -> term;

  val pre_vals_reg_bir_tm : string -> string -> term;

  val pre_vals_mem_reg_bir_tm : string -> string -> string -> term;

  val pre_vals_bir_tm : string -> string -> string -> string -> term;

end
