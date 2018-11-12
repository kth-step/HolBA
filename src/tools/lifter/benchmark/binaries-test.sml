open HolKernel Parse;

open bir_inst_liftingLib;
open gcc_supportLib;

open bir_inst_liftingLibTypes;



val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;







(* error printing functions *)
fun err_to_str disassemble_fun ((err_pc, err_inst, err_inst_desc, err_descr):bir_inst_error) =
  let
    fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
    val err_str = case err_descr of
                 SOME (BILED_msg (str)) => str
               | SOME (BILED_msg_term (str, term)) => str
               | SOME (BILED_lifting_failed (term)) => "some term"
               | NONE => "???";
  in
    (err_inst ^ (" (" ^ err_inst ^ "; " ^ err_inst_desc ^ ")  @ 0x" ^ (Arbnum.toHexString err_pc)) ^ "\r\n\t" ^ err_str)
  end;



(* generic lifting call *)
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



fun lift_file da_file bmil_bir_lift_prog_gen disassemble_fun =
  let
    val _ = print_with_style [Bold, Underline] ("Lifting \""^da_file^"\" (???)\n");

    val (region_map, sections) = read_disassembly_file_regions da_file;

    (* predefined program range *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
    (* max for arm8 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFFFFFFFFFF));
    (* max for m0 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFF));
    (* max for prog *)
    val prog_range = da_sections_minmax sections;

    val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

    (* print out only the failing instructions *)
    val _ = if errors <> [] then
      let
        val _ = print "\n\n";
        val _ = print_with_style [Bold, Underline] "There are failing instructions\n";
(*
        val _ = print_with_style [Bold, Underline] "Failing instructions\n";
        val _ = List.foldl (fn (x, ()) => print ((err_to_str disassemble_fun x) ^ "\n")) () errors;
*)
      in
        ()
      end else ();
  in
    thm_prog
  end;

(*
val da_file = "binaries/bzip2-1.0.6/aarch64-libbz2-emptymain.da";
val da_file = "binaries/aes-aarch64.da";
val da_file = "binaries/bignum/aarch64-bignum-emptymain.da";
val bmil_bir_lift_prog_gen = bmil_arm8.bir_lift_prog_gen;
val disassemble_fun = arm8AssemblerLib.arm8_disassemble;
val _ = lift_file da_file bmil_bir_lift_prog_gen disassemble_fun;

val da_file = "binaries/bzip2-1.0.6/m0-libbz2-emptymain.da";
val da_file = "binaries/bignum/m0-bignum-emptymain.da";
val bmil_bir_lift_prog_gen = bmil_m0_LittleEnd_Process.bir_lift_prog_gen;
val disassemble_fun = m0AssemblerLib.m0_disassemble;
val _ = lift_file da_file bmil_bir_lift_prog_gen disassemble_fun;
(*
merging code - 214.769 s
checking for duplicate labels - 18.312 s
merging memory-regions - 7.185 s
Total time : 820.226 s - OK
*)
*)






fun gen_sections disassemble_fun (pc:Arbnum.num) (inst:string) =
  let
    fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
  in
    [BILMR (pc, [(inst, BILME_code (SOME (asm_of_hex_code_fun inst)))])]
  end;

fun lift_inst disassemble_fun (pc:Arbnum.num) (inst:string) =
  let
(*
    val pc = (Arbnum.fromInt 0xCFEE);
    val inst = "4770";
*)
    val sections = gen_sections disassemble_fun pc inst;
    val prog_range = da_sections_minmax sections;
    val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;
  in
    thm_prog
  end;

(*
val disassemble_fun = arm8AssemblerLib.arm8_disassemble;
val thm_prog = lift_inst disassemble_fun (Arbnum.fromInt 0x40C2A4) ("78206A61");

val disassemble_fun = m0AssemblerLib.m0_disassemble;
val thm_prog = lift_inst disassemble_fun (Arbnum.fromInt 0xCFEE) ("4770");
*)




(* export a theory for these binaries *)
(*
val _ = print "\n\n";

val _ = new_theory "bzip2";
val _ = save_thm ("bzip2_arm8_program_THM", thm_arm8);
val _ = save_thm ("bzip2_m0_program_THM", thm_m0);
val _ = export_theory();
*)

