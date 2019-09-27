signature bir_prog_gen_randLib = sig

  (* provide length of program to generate *)
  (* generates a mix of instructions with only forward jumps within this sequence *)
  val bir_prog_gen_arm8_rand : int -> string list

  val bir_prog_gen_arm8_rand_simple : int -> string list

end
