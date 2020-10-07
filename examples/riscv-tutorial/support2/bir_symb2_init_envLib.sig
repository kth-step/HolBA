signature bir_symb2_init_envLib = sig

(*
  val add_memory_to_env               : term -> term
  val add_registers_to_env_1          : string list -> term -> term
  val add_registers_to_env_64         : string list -> term -> term
  val add_registers_to_env_8          : string list -> term -> term
  val add_symbolic_register_to_env_1  : string -> term -> term
  val add_symbolic_register_to_env_64 : string -> term -> term
  val add_symbolic_register_to_env_8  : string -> term -> term
  val generate_symbolic_register_1    : string -> term
  val generate_symbolic_register_64   : string -> term
  val generate_symbolic_register_8    : string -> term
*)
  val init_env                        : unit -> term

end
