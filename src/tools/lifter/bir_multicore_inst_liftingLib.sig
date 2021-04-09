signature bir_multicore_inst_liftingLib = sig

  include Abbrev

  val riscv_multicore_test_hex : Arbnum.num -> Arbnum.num -> Arbnum.num -> string -> thm option * bir_inst_liftingLibTypes.bir_inst_liftingExn_data option * string

end
