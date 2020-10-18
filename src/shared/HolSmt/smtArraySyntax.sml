structure smtArraySyntax :> smtArraySyntax =
struct

  open HolKernel Parse boolLib;  local open smtArrayTheory in end;

  val ERR = Feedback.mk_HOL_ERR "smtArraySyntax"

  val store_tm = prim_mk_const{Name="store", Thy="smtArray"}
  val select_tm = prim_mk_const{Name="select", Thy="smtArray"};

  fun mk_store (array, index, value) =
    list_mk_comb (
      inst [alpha |-> type_of index,
            beta  |-> type_of value] store_tm,
      [array, index, value]);

  fun mk_select (array, index) =
    let
      val (ty_index, ty_value) = (Type.dom_rng o Term.type_of) array;
    in
      list_mk_comb (
        inst [alpha |-> ty_index,
              beta  |-> ty_value] select_tm,
        [array, index])
    end;

  val dest_store  = dest_triop store_tm  (ERR "dest_store"  "not store");
  val dest_select = dest_binop select_tm (ERR "dest_select" "not select");

  val is_store = can dest_store;
  val is_select = can dest_select;

end (* smtArraySyntax *)

