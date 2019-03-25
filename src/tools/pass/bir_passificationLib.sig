signature bir_passificationLib =
sig
  include Abbrev

  val bir_prog_pass_ssa : term -> term
  val bir_prog_rff : string -> term
  val bir_prog_wtf : term -> string -> unit

end
