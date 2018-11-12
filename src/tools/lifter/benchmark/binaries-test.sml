open HolKernel Parse;

open bir_inst_liftingLib;
open gcc_supportLib;

open bir_inst_liftingLibTypes;



val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;



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


val da_file = "binaries/aes-aarch64.da";(*"binaries/bzip2-1.0.6/aarch64-libbz2-emptymain.da";*)
val bmil_bir_lift_prog_gen = bmil_arm8.bir_lift_prog_gen;

val _ = print_with_style [Bold, Underline] "Lifting ??? (aarch64)\n";

val (region_map, sections) = read_disassembly_file_regions da_file;

val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
val prog_range = da_sections_minmax sections;

val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;




(*


(* functions for analyzing region map and section structures (using the code sections only) *)
fun zip_region_lists ([], a) = ((if a <> [] then print "warning: element number mismatch.\n" else ()); [])
  | zip_region_lists (region::rs, section::ss) =
       let
         val (name, addr) = region;
         val (BILMR (addr2, entryList)) = section;
         val _ = if addr <> addr2 then print "warning: address mismatch.\n" else ();
       in
         (addr, name, entryList)::(zip_region_lists (rs, ss))
       end;

fun find_irregularities regionList =
  let
    val regionList = List.map (fn (addr, name, l) => (addr, name, List.map (fn (inst, t) => (inst, case t of BILME_code (SOME _) => BILME_code (NONE) | x => x)) l)) regionList;
    val regionIssues = List.map (fn (addr, name, l) =>
                  (case l of
                      [] => true 
                    | (_, eT)::ls => List.exists (fn (_, x) => (x <> eT)) ls
                  , addr,name
                  )) regionList;
    val _ = List.map (fn (x, addr, name) => if x then print ("warning: region " ^ name ^ " has issues.\n") else ()) regionIssues;
    val issueRegions = List.filter (fn (x, addr, name) => x) regionIssues;
    val regions = List.filter (fn (addr, name, l) => List.exists (fn (x, addr2, name2) => (addr = addr2) andalso x) regionIssues) regionList;
    fun mem_type_to_str mt = case mt of
                               BILME_unknown => "unknown"
                             | BILME_data => "data"
                             | BILME_code (NONE) => "code"
                             | BILME_code (SOME s) => "code(" ^ s ^ ")";
    val _ = List.map (fn (_, _, l) => case l of [] => [] 
					     | (_, eT)::ls => (print ("start:" ^ (mem_type_to_str eT) ^ "\n") ;List.map (fn (_, eT2) => if eT <> eT2 then (print ((mem_type_to_str eT2) ^ "\n")) else ()) ls)) regions;
  in
    ()
  end;


  

(* trying to lift the arm8 and m0 binaries, for the whole address space *)
(* ----------- arm8 *)
val _ = print_with_style [Bold, Underline] "Lifting bzip2-aarch64.da\n";

val (region_map, bzip2_sections) = read_disassembly_file (K true) "bzip2-aarch64.da"

(*
length region_map
length bzip2_sections

val regionList = zip_region_lists (region_map, bzip2_sections);
val _ = find_irregularities regionList;

val (thm_arm8, errors_arm8) = bmil_arm8.bir_lift_prog_gen
  ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFFFFFFFFFF))
  [BILMR (Arbnum.fromInt 0x100, [("B9001263", BILME_code (SOME "teststorestatic: (str w3, [x19,#16])"))])]
*)

val (thm_arm8, errors_arm8) = bmil_arm8.bir_lift_prog_gen
  ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFFFFFFFFFF))
  bzip2_sections

val _ = print "\n\n\n";

(* ----------- m0 *)
val _ = print_with_style [Bold, Underline] "Lifting bzip2-m0-cortex.da\n";
val (region_map, bzip2_sections) = read_disassembly_file (K true) "bzip2-m0-cortex.da"

val (thm_m0, errors_m0) = bmil_m0_LittleEnd_Process.bir_lift_prog_gen
  ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFF))
  bzip2_sections



(* error printing functions *)
fun arm8_asm_of_hex_code code = hd (arm8AssemblerLib.arm8_disassemble [QUOTE code]);
fun m0_asm_of_hex_code code = hd (m0AssemblerLib.m0_disassemble [QUOTE code]);
fun none_asm_of_hex_code code = "no dasm";

fun err_to_str asm_of_hex_code_fun (err_pc, err_inst, err_descr) =
  let
    val err_str = case err_descr of
                 SOME (BILED_msg (str)) => str
               | SOME (BILED_msg_term (str, term)) => str
               | SOME (BILED_lifting_failed (term)) => "some term"
               | NONE => "???"
  in
    (err_inst ^ (" (" ^ (asm_of_hex_code_fun err_inst) ^ ")  @ 0x" ^ (Arbnum.toHexString err_pc)) ^ "  -  " ^ err_str)
  end;

val arm8_err_to_str = err_to_str arm8_asm_of_hex_code;
val m0_err_to_str = err_to_str m0_asm_of_hex_code;
val none_err_to_str = err_to_str none_asm_of_hex_code;



(* print out only the failing instructions *)
val _ = print "\n\n";
val _ = print_with_style [Bold, Underline] "Failing instructions of arm8\n";

val _ = List.foldl (fn (x, ()) => print ((none_err_to_str x) ^ "\n")) () errors_arm8;


val _ = print "\n\n";
val _ = print_with_style [Bold, Underline] "Failing instructions of m0\n";

val _ = List.foldl (fn (x, ()) => print ((none_err_to_str x) ^ "\n")) () errors_m0;


(* once we have full coverage we may export a theory for these binaries *)
(*
val _ = print "\n\n";

val _ = new_theory "bzip2";
val _ = save_thm ("bzip2_arm8_program_THM", thm_arm8);
val _ = save_thm ("bzip2_m0_program_THM", thm_m0);
val _ = export_theory();
*)


*)
