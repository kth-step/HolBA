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

type bir_inst_error = Arbnum.num * string * string * bir_inst_liftingExn_data option;

fun bir_inst_error_to_string ((pc, hc, hc_desc, ed):bir_inst_error) = let
  val s = "code \"" ^ hc_desc ^ "\" @ 0x" ^ (Arbnum.toHexString pc) ^ "\n";
  val s' = case ed of NONE => s |
             SOME e => s ^ "   " ^ (bir_inst_liftingExn_data_to_string e) ^ "\n"
in (s'^"\n") end;

fun print_bir_inst_error e =
  Parse.print_with_style [PPBackEnd.FG PPBackEnd.OrangeRed] (bir_inst_error_to_string e);

fun print_bir_inst_errors [] = ()
  | print_bir_inst_errors (e::es) =
    (print_bir_inst_error e; print_bir_inst_errors es);


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


fun bir_inst_lifting_mem_region_entry_to_string (hc, BILME_data) = ("\"" ^ hc ^ "\" (* data *)")
  | bir_inst_lifting_mem_region_entry_to_string (hc, BILME_unknown) = "\"" ^ hc ^ "\" (* ??? *)"
  | bir_inst_lifting_mem_region_entry_to_string (hc, BILME_code NONE) = "\"" ^ hc ^ "\" (* code *)"
  | bir_inst_lifting_mem_region_entry_to_string (hc, BILME_code (SOME d)) = "\"" ^ hc ^ "\" (* code " ^ d ^" *)"

fun bir_inst_lifting_mem_region_to_string (BILMR (addr, l)) =
("(0x" ^ Arbnum.toHexString addr ^", [\n   " ^
(String.concatWith ",\n   " (List.map bir_inst_lifting_mem_region_entry_to_string l)) ^
"\n])\n")


fun print_bir_inst_lifting_mem_regions l =
 print (String.concatWith "\n\n" (List.map bir_inst_lifting_mem_region_to_string l))


fun expand_bir_inst_lifting_mem_region_aux hc_s acc addr [] =
    List.rev acc
  | expand_bir_inst_lifting_mem_region_aux hc_s acc addr ((hc:string, et)::el) =
    expand_bir_inst_lifting_mem_region_aux hc_s ((addr, hc, et)::acc)
      (Arbnum.+ (addr, hc_s hc)) el

(* fun hc_s s = Arbnum.fromInt (String.size s div 2) *)

fun expand_bir_inst_lifting_mem_region hc_s (BILMR (addr, l)) =
  expand_bir_inst_lifting_mem_region_aux hc_s [] addr l

fun expand_bir_inst_lifting_mem_regions hc_s rl =
  flatten (List.map (expand_bir_inst_lifting_mem_region hc_s) rl);


fun expanded_bir_inst_lifting_mem_regions_to_string l =
String.concatWith "\n" (List.map
  (fn (addr, hc, ty) => "0x" ^ (Arbnum.toHexString addr) ^": " ^
    (bir_inst_lifting_mem_region_entry_to_string (hc, ty))) l)

fun print_expanded_bir_inst_lifting_mem_regions l = (
  print (expanded_bir_inst_lifting_mem_regions_to_string l);
  print "\n\n"
);


fun check_expanded_bir_inst_lifting_mem_region_aux max [] = SOME max
  | check_expanded_bir_inst_lifting_mem_region_aux max ((addr, _, _)::l) =
    if (Arbnum.< (max, addr)) then check_expanded_bir_inst_lifting_mem_region_aux addr l
       else NONE

fun check_expanded_bir_inst_lifting_mem_regions [] = NONE
  | check_expanded_bir_inst_lifting_mem_regions ((addr, _, _)::l) =
    (case check_expanded_bir_inst_lifting_mem_region_aux addr l of
       SOME max => SOME (addr, max)
     | NONE => NONE)

end;
