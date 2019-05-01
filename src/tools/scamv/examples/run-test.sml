open HolKernel Parse boolLib bossLib;


open gcc_supportLib;



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


val binaries__list = [
  ("enpa0", "enpa0/asm.da"),
  ("enpa1", "enpa1/asm.da"),
  ("ldld",   "ldld/asm.da")
];






val da_file = "ldld/asm.da";
val (region_map, sections) = read_disassembly_file_regions da_file;

(* --------------------------------------- *)
(* here we have the binary in the lifter input format *)
(* --------------------------------------- *)

open bir_inst_liftingLib;

(* for arm8 *)
val (bmil_bir_lift_prog_gen, disassemble_fun) = (bmil_arm8.bir_lift_prog_gen, arm8AssemblerLib.arm8_disassemble);

(* this was copied -----> *)
fun disassembly_section_to_minmax section =
  case section of
      BILMR(addr_start, entries) =>
        let
          val data_strs = List.map fst entries;
	  (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
          val lengths_st = List.map String.size data_strs;
          val _ = List.map (fn x => ()) lengths_st;
          val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
          val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
        in
          (addr_start, Arbnum.+(addr_start, length))
        end;

fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
  ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
   (if Arbnum.>(max_1, max_2) then max_1 else max_2))
  ) (hd ls) (tl ls);

fun da_sections_minmax sections = minmax_fromlist (List.map disassembly_section_to_minmax sections);
(* <---- this was copied *)

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

val prog_range = da_sections_minmax sections;
val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

val lifted_prog = (snd o dest_comb o concl) thm_prog;

(* --------------------------------------- *)
(* here we have a lifted binary *)
(* --------------------------------------- *)
