signature bir_gccLib = sig

  (*
     takes a list of assembly instructions
     it produces a disassembly file for the lifter
     and returns its path in the temporary directory.
   *)
  val bir_gcc_assembe_disassemble : string -> string
  val bir_gcc_disassemble : string -> string
  val bir_gcc_remove_data_section : string -> string

end
