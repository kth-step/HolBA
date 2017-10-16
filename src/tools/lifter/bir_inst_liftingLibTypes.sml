open HolKernel boolLib liteLib simpLib Parse bossLib;

structure bir_inst_liftingLibTypes :> bir_inst_liftingLibTypes = struct

(* If lifting of an instruction fails, it is returned (hexcode) together with
   some explantion in the from of a bir_inst_liftingExn_data value. *)

datatype bir_inst_liftingExn_data =
   BILED_msg of string
 | BILED_msg_term of string * term
 | BILED_lifting_failed of term
exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;

fun bir_inst_liftingExn_data_to_string (BILED_msg msg) = msg
  | bir_inst_liftingExn_data_to_string (BILED_msg_term (msg, t)) =
      (msg ^ "(``" ^ (term_to_string t) ^ "``)")
  | bir_inst_liftingExn_data_to_string (BILED_lifting_failed t) =
      ("lifting of ``" ^ (term_to_string t) ^ "`` failed");

datatype bir_inst_lifting_mem_entry_type =
    BILME_code of string option
  | BILME_data
  | BILME_unknown

datatype bir_inst_lifting_mem_region =
  BILMR of Arbnum.num * (string * bir_inst_lifting_mem_entry_type) list;

fun mk_bir_inst_lifting_data_region addr data =
  BILMR (addr, List.map (fn hc => (hc, BILME_data)) data)

fun mk_bir_inst_lifting_code_region addr data =
  BILMR (addr, List.map (fn hc => (hc, BILME_code NONE)) data)

fun mk_bir_inst_lifting_region addr data =
  BILMR (addr, List.map (fn hc => (hc, BILME_unknown)) data)

end;
