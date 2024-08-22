signature ex_mem_incrLib =
sig

  include Abbrev;

  val generate_bigger_inc : term -> int -> term;
  val benchmark : unit -> unit;

end
