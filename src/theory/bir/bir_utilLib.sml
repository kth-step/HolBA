structure bir_utilLib =
struct

open HolKernel Parse;

val ERR = mk_HOL_ERR "bir_utilLib"

(* val assoc_with : ('b * 'b -> bool) -> 'b -> ('b * 'a) list -> 'a *)
fun assoc_with eq x [] = raise ERR "assoc_with" "not found"
  | assoc_with eq x ((b,a)::xs) =
    if eq (x,b)
    then a
    else assoc_with eq x xs;

(* val rev_assoc_with : ('a * 'a -> bool) -> 'a -> ('b * 'a) list -> 'b *)
fun rev_assoc_with eq x [] = raise ERR "rev_assoc_with" "not found"
  | rev_assoc_with eq x ((b,a)::xs) =
    if eq (x,a)
    then b
    else rev_assoc_with eq x xs;

end
