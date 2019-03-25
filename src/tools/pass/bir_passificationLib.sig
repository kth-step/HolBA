signature bir_passificationLib =
sig
  include Abbrev

  val passify_prog_ssa : term -> term
  val bir_prog_rff : string -> term
  val bir_prog_wtf : term -> string -> unit

end
