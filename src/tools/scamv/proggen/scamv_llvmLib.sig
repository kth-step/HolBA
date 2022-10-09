signature scamv_llvmLib = sig

  val llvm_prefix : unit -> string
  val llvm_initial_phase : string -> string option -> ((string * string * string) * string) list option

end
