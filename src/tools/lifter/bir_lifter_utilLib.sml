structure bir_lifter_utilLib =
struct

local
  open HolKernel Parse;

  val ERR = mk_HOL_ERR "bir_lifter_utilLib"

in

fun mem_with eq a []      = false
  | mem_with eq a (x::xs) =
    if eq (a,x)
    then true
    else mem_with eq a xs;

end

end (* struct *)
