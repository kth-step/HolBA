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
    val err_str = (
             case err_descr of
                 SOME x => bir_inst_liftingExn_data_to_string x
               | NONE => "???"
      ); (*case err_descr of
                 SOME (BILED_msg (str)) => str
               | SOME (BILED_msg_term (str, term)) => str
               | SOME (BILED_lifting_failed (term)) => "some term"
               | NONE => "???"*)
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



fun lift_file bmil_bir_lift_prog_gen disassemble_fun da_file =
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
val _ = lift_file bmil_bir_lift_prog_gen disassemble_fun da_file;

val da_file = "binaries/bzip2-1.0.6/m0-libbz2-emptymain.da";
val da_file = "binaries/bignum/m0-bignum-emptymain.da";
val bmil_bir_lift_prog_gen = bmil_m0_LittleEnd_Process.bir_lift_prog_gen;
val disassemble_fun = m0AssemblerLib.m0_disassemble;
val _ = lift_file bmil_bir_lift_prog_gen disassemble_fun da_file;
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

fun lift_inst bmil_bir_lift_prog_gen disassemble_fun (pc:Arbnum.num) (inst:string) =
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
val bmil_bir_lift_prog_gen = bmil_arm8.bir_lift_prog_gen;
val thm_prog = lift_inst bmil_bir_lift_prog_gen disassemble_fun (Arbnum.fromInt 0x40C2A4) ("78206A61");

val disassemble_fun = m0AssemblerLib.m0_disassemble;
val bmil_bir_lift_prog_gen = bmil_m0_LittleEnd_Process.bir_lift_prog_gen;
val thm_prog = lift_inst bmil_bir_lift_prog_gen disassemble_fun (Arbnum.fromInt 0xCFEE) ("4770");
*)

(*

val tm = ``mem_store_byte (ms.REG 0w + ms.REG 19w + 1w)
  ((15 >< 8) (w2w (ms.REG 1w)))
  (mem_store_byte (ms.REG 0w + ms.REG 19w) ((7 >< 0) (w2w (ms.REG 1w)))
     ms.MEM)``;

REWRITE_CONV [GSYM bir_arm8_extrasTheory.mem_store_half_def, bir_arm8_extrasTheory.mem_store_byte_def] tm

dest_comb ``ms.REG 0w + ms.REG 19w + 1w``

REWRITE_CONV [GSYM bir_arm8_extrasTheory.mem_store_half_def] ``(a + 1w =+ (15 >< 8) w) ((a =+ (7 >< 0) w) mmap)``

REWRITE_CONV [GSYM bir_arm8_extrasTheory.mem_store_half_def] ((snd o dest_eq o concl o (Q.SPECL [`a`, `w`, `mmap`])) bir_arm8_extrasTheory.mem_store_half_def)

val tm = ``(BLV_Imm (Imm8 ((15 >< 8) (w2w (ms.REG 1w)))))``;
val tm = ``((15 >< 8) (w2w (ms.REG 1w)))``;
(*
open bir_lifting_machinesLib_instances;
"bir_inst_liftingLib"
structure MD = struct val mr = bir_lifting_machinesLib_instances.arm8_bmr_rec end;
structure bmil_arm8 = bir_inst_liftingFunctor (MD);
bmil_arm8.exp_lift_fn

exp_lift_fn_raw ``Imm8 5w``;
exp_lift_fn_raw ``(Imm8 ((15 >< 8) (w2w (ms.REG 1w))))``;

fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)
val hex_code = hex_code_of_asm `movk x0, #0x0, lsl #32`;
val hex_code = "72A00035";
val [thm] = (#bmr_step_hex mr) ms_v hex_code;



val disassemble_fun = arm8AssemblerLib.arm8_disassemble;
fun asm_of_hex_code_fun code = hd (disassemble_fun [QUOTE code]);
asm_of_hex_code_fun "F2C00000";
asm_of_hex_code_fun "72A00035";



val hex_code = hex_code_of_asm `strh w1, [x19, x0]`;
val [thm] = (#bmr_step_hex mr) ms_v hex_code;
REWRITE_RULE [GSYM bir_arm8_extrasTheory.mem_store_half_def, bir_arm8_extrasTheory.mem_store_byte_def] thm;


val hex_code = hex_code_of_asm `strh w1, [x19, #8]`;
val thm = (#bmr_step_hex mr) ms_v hex_code;

val hex_code = hex_code_of_asm `ldrh w0, [x1, #8]`;
val thm = (#bmr_step_hex mr) ms_v hex_code;

val vn = ms_v;
arm8_step_hex' vn hex_code

mem_half
``mem_store_half``;
bir_arm8_extrasTheory.mem_store_half_def
bir_arm8_extrasTheory.mem_store_byte_def

dest_comb ``(a + 1w =+ (15 >< 8) w) ((a =+ (7 >< 0) w) mmap)``;

val hex_code = hex_code_of_asm `ldrh w0, [x1, #8]`;
val thm = (#bmr_step_hex mr) ms_v hex_code;

*)

*)




(* export a theory for these binaries *)
(*
val _ = print "\n\n";

val _ = new_theory "bzip2";
val _ = save_thm ("bzip2_arm8_program_THM", thm_arm8);
val _ = save_thm ("bzip2_m0_program_THM", thm_m0);
val _ = export_theory();
*)

