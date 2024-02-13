signature bir_lifter_interfaceLib =
sig

  datatype da_isa =
    da_arm8
  | da_riscv

  val lift_da_and_store : string -> string -> da_isa -> Arbnum.num * Arbnum.num -> unit;

end
