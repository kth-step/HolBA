structure bir_exp_helperLib =
struct
local

  open pred_setTheory;

  val conv_to_varset = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss)
                                 ([INSERT_UNION_EQ,UNION_EMPTY]@HolBASimps.common_exp_defs);

in

(*
val exp = ``
BExp_UnaryExp BIExp_Not
          (BExp_BinExp BIExp_Or
             (BExp_UnaryExp BIExp_Not
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "PSR_N" BType_Bool))
                   (BExp_Den (BVar "PSR_V" BType_Bool))))
             (BExp_Den (BVar "PSR_Z" BType_Bool)))
``
*)

fun simpleholset_to_list t =
  if pred_setSyntax.is_empty t then [] else
  if not (pred_setSyntax.is_insert t) then
    raise ERR "simpleholset_to_list" ("cannot handle syntax: " ^ (term_to_string t))
  else
    let val (x, rset) = pred_setSyntax.dest_insert t in
      x::(simpleholset_to_list rset)
    end;

fun get_birexp_vars exp =
  let
    val exp_vars = (snd o dest_eq o concl o conv_to_varset) ``(bir_vars_of_exp ^exp)``;
    val vars = (simpleholset_to_list) exp_vars;
  in
    vars
  end;

end (* local *)

end (* struct *)
