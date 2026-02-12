signature init_automatonLib =
sig

  type bir_block = term * term list * term;

  val init_blocks: bir_block list
  val init_program: term

end (* init_automatonLib *)
