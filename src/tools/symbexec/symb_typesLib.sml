structure symb_typesLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open symb_interpretTheory;
  open symb_recordTheory;

in

  val symb_list_of_types = [
    (*mk_thy_type {Tyop="symb_concst_t",   Thy="scratch", Args=[Type.alpha, Type.beta, Type.gamma]}*)
    mk_type ("symb_concst_t", [Type.alpha, Type.beta, Type.gamma, Type.delta]),
    mk_type ("symb_symbst_t", [Type.alpha, Type.beta, Type.gamma, Type.delta]),
    mk_type ("symb_interpret_t", [Type.alpha, Type.beta]),
    mk_type ("symb_rec_t", [Type.alpha, Type.beta, Type.gamma, Type.delta, Type.etyvar, Type.ftyvar, ``:'g``])
  ];

  val symb_TYPES_thms = (flatten (map type_rws symb_list_of_types));
  val symb_TYPES_ss = rewrites symb_TYPES_thms;

end; (* local *)

end; (* symb_typesLib *)
