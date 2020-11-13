signature scamv_enumLib =
sig
  type 'a enumeration;

  val next : 'a enumeration -> 'a
  val peek : 'a enumeration -> 'a
  val nth : int -> 'a enumeration -> 'a
  val take : int -> 'a enumeration -> 'a list
  val takeWhile : ('a -> bool) -> 'a enumeration -> 'a list
  val skipWhile : ('a -> bool) -> 'a enumeration -> 'a

  val constant : 'a -> 'a enumeration
  val unfold : ('b -> 'a) -> ('b -> 'b) -> 'b -> 'a enumeration
  val roundrobin_list : 'a list -> 'a enumeration
  val range_from_to : int -> int -> int enumeration

  val map : ('a -> 'b) -> 'a enumeration -> 'b enumeration
  val iterate : ('a -> 'a) -> 'a -> 'a enumeration
  val zipWith : ('a -> 'b -> 'c) -> 'a enumeration -> 'b enumeration -> 'c enumeration
  val cartesian : 'a enumeration -> 'b enumeration -> ('a * 'b) enumeration
  val prefix : 'a list -> 'a enumeration -> 'a enumeration
  val interleave : 'a enumeration -> 'a enumeration -> 'a enumeration

end
