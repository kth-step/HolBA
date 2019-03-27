open HolKernel Parse;


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


val prog_range = da_sections_minmax sections;
val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

val lifted_prog = (snd o dest_comb o concl) thm_prog;

(* --------------------------------------- *)
(* here we have a lifted binary *)
(* --------------------------------------- *)
