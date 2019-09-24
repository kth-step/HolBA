open HolKernel Parse boolLib bossLib;


open bir_scamv_driverLib;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;



(*
 example entropy-paper0:
      b.eq l2
      mul x1, x2, x3
  l2: ldr x2, [x1, #8]

 models:
  (if sharedline(x) then tag(x)),
  (tag(x)),
  (if sharedline(x) then x)
 *)

(*
 example entropy-paper1:
      cmp x2, x3
      b.lo lb
      add x1, x2, x3
  lb: ldr x2, [x1]
 *)

(*
 example ld-ld:
  ldr x3, [x1]
  ldr x4, [x2]
 models:
  (cache line(x)),
  (cache line(x), tag(x))
 input:
  ((0,0), (0,cache size))
 *)


val input_files = [
  ("enpa0", "asm/enpa0.s"),
  ("enpa1", "asm/enpa1.s"),
  ("ldld",  "asm/ldld.s")
];


(*
val _ = Globals.linewidth := 100;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Globals.show_assums := true;
val _ = Globals.show_types := true;
*)


val (prog_name, asm_file) = List.nth (input_files, 2);

(*
val _ = bir_prog_gen_arm8_mock_set [];
val _ = bir_prog_gen_arm8_mock_set_wrap_around true;
*)

(*
val asm_code = "ldr x3, [x1]\nldr x4, [x2]\n";
*)

val _ = scamv_test_mock ();
(*val _ = scamv_test_asmf asm_file;*)


(*
 TODO: move the following somewhere else
  >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
 *)


open gcc_supportLib;



(*
from: lifter/bir_inst_liftingLibTypes.sml

datatype bir_inst_lifting_mem_entry_type =
    BILME_code of string option
  | BILME_data
  | BILME_unknown

datatype bir_inst_lifting_mem_region =
  BILMR of Arbnum.num * (string * bir_inst_lifting_mem_entry_type) list;

*)
fun entry_to_str entry = case entry of
                 BILME_code(c) => "BILME_code("^(PolyML.makestring c)^")"
               | BILME_data    => "BILME_data"
               | BILME_unknown => "BILME_unknown";

fun pretty_entry
  (depth: int)
  (printElem: {})
  (x: bir_inst_lifting_mem_entry_type) =
    PolyML.PrettyString (entry_to_str x);

val _ = PolyML.addPrettyPrinter pretty_entry;
(*
PolyML.print (BILME_code(SOME "hallo"))
(BILME_code(SOME "hallo"))
*)

fun section_to_str section = case section of
      BILMR(a_start, entries) =>
        (* use pretty block and "PolyML.prettyRepresentation (x, depth)" *)
        "BILMR (Arbnum.fromString \"" ^ (Arbnum.toString a_start) ^ "\", " ^ (PolyML.makestring entries) ^ ")";

fun pretty_section
  (depth: int)
  (printElem: {})
  (x: bir_inst_lifting_mem_region) =
    PolyML.PrettyString (section_to_str x);

val _ = PolyML.addPrettyPrinter pretty_section;

(*
BILMR (Arbnum.fromString "3", [("test", BILME_code(SOME "hallo"))])
*)
(* <------------ this should go to lifter/bir_inst_liftingLibTypes.sml *)


