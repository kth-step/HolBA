signature tx_automatonLib =
sig

  type bir_block = term * term list * term;

  val tx_blocks: bir_block list
  val tx_program: term

end (* tx_automatonLib *)
