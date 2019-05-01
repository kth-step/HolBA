signature bir_rel_synthLib =
sig
    type exp;
    type cobs = exp * exp;
    val mkRel : (exp * (cobs list) option) list -> exp;
end;
