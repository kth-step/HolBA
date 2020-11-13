structure bir_utilLib =
struct

local
  open HolKernel Parse;
  open bslSyntax;

  
  (* error handling *)
  val libname  = "bir_utilLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

fun bir_free_vars exp =
    let 
	    fun nub_with eq [] = []
	      | nub_with eq (x::xs) = x::(nub_with eq (List.filter (fn y => not (eq (y, x))) xs))

	    val fvs =
	        if is_comb exp then
		        let val (con,args) = strip_comb exp
		        in
		          if identical con ``BExp_MemConst``
		          then [``"MEM"``]
		          else if identical con ``BExp_Den``
		          then
		            let val v = case strip_comb (hd args) of
				                        (_,v::_) => v
				                      | _ => raise ERR "bir_free_vars" "not expected"
		            in
			            [v]
		            end
		          else
		            List.concat (map bir_free_vars args)
		        end
	        else []
    in
	    nub_with (fn (x,y) => identical x y) fvs
    end;
end

end
