signature holba_eq_utilLib =
sig
  val assoc_with : ('b * 'b -> bool) -> 'b -> ('b * 'a) list -> 'a;

  val rev_assoc_with : ('a * 'a -> bool) -> 'a -> ('b * 'a) list -> 'b;

  val mem_with : ('a * 'a -> bool) -> 'a -> 'a list -> bool;
end
