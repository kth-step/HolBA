signature bir_rel_synthLib =
sig
    type exp;
    type cobs = exp * exp;
    val mkRel : (exp * (cobs list) option) list -> exp;
    val mkRel_conds : (exp * (cobs list) option) list -> exp list * exp;
end;
