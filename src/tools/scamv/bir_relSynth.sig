signature bir_relSynth =
sig
    type exp;
    type cobs = exp * exp;
    val mkRel : (exp * (cobs list) option) list -> exp;
end;
