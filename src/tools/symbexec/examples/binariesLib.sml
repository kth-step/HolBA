structure binariesLib =
struct
local

open binariesTheory;
open gcc_supportLib;

open bir_programSyntax;
open bir_immSyntax;
open listSyntax;
open wordsSyntax;

(* ===================================== program behavior ======================================= *)
val (_, mem_wi_prog_tm, mem_tm, prog_tm) = (dest_bir_is_lifted_prog o concl) balrob_program_THM;

val prog_blocks = (fst o dest_list o dest_BirProgram) prog_tm;

fun get_block prog_blocks lbl_tm =
  let
    val blocks = prog_blocks;
    (*
    val block = hd blocks;
    *)
    fun is_block block =
      let
        val (lbl, _, _) = dest_bir_block block;
        val lbl2_tm     = (snd o dest_eq o concl o EVAL) lbl;
      in
        lbl_tm = lbl2_tm
      end;

    fun findFirst f []      = NONE
      | findFirst f (x::xs) = if f x then SOME x else
                                          findFirst f xs;
  in
    findFirst is_block blocks
  end;

fun get_block_byAddr prog_tm addr =
    get_block prog_tm ((mk_BL_Address o mk_Imm32 o mk_word) (addr, Arbnum.fromInt 32));

(* =============================== memory contents (including data) ============================= *)
val da_file     = "binaries/balrob.elf.da.plus";
val symb_filter = fn secname =>
  case secname of
      ".text" => (K true)
    | ".data" => (K true)
    | ".bss"  => (K true)
    | _       => (K false);
val data_filter = fn secname => fn _ => secname = ".data" orelse secname = ".bss";

val da_data = read_disassembly_file symb_filter da_file;
(*
val _ = print_disassembly_data da_data;
*)

fun find_single_SOME []             = NONE
  | find_single_SOME ( NONE   ::xs) = find_single_SOME xs
  | find_single_SOME ((SOME x)::xs) =
      case find_single_SOME xs of
	  NONE   => SOME x
        | SOME _ => raise ERR "find_single_SOME" "location exists multiple times";

fun is_location_in_entry location (e: disassembly_entry) =
  (Arbnumcore.<= (#DAE_addr e, location)) andalso
  (Arbnumcore.< (location, Arbnumcore.+ (#DAE_addr e, Arbnumcore.fromInt ((length (explode (#DAE_hex e))) div 2))));

fun read_byte_from_block location (b: disassembly_block) =
  let
    val entries = List.filter (is_location_in_entry location) b;
    val bytes   = List.map (fn e =>
          let
            val offset  = Arbnumcore.-(location, #DAE_addr e);
            val hex_idx = (Arbnumcore.toInt offset) * 2;
            val cl      = explode (#DAE_hex e);
            val hex     = implode (List.take (List.drop (cl, hex_idx), 2));
          in
            Arbnumcore.toInt (Arbnumcore.fromHexString hex)
          end
        ) entries;
    val bytes_ol = List.map SOME bytes;
  in
    find_single_SOME bytes_ol
  end;

fun read_byte_from_lbl      location (l:disassembly_lbl) =
  find_single_SOME (List.map (read_byte_from_block   location) (#DAL_blocks l));

fun read_byte_from_section  location (s:disassembly_section) =
  find_single_SOME (List.map (read_byte_from_lbl     location) (#DAS_lbls   s));

fun read_byte_from_data     location (d:disassembly_data) =
  find_single_SOME (List.map (read_byte_from_section location) d);


fun find_label_addr_lbl      name (l:disassembly_lbl) =
  let val lbl_name = #DAL_name l in
  if name = lbl_name then
    SOME (#DAL_addr l)
  else
    NONE
  end;

fun find_label_addr_section  name (s:disassembly_section) =
  find_single_SOME (List.map (find_label_addr_lbl     name) (#DAS_lbls   s));

fun find_label_addr_data     name (d:disassembly_data) =
  find_single_SOME (List.map (find_label_addr_section name) d);


(* ===================================== symbolic variables for inputs in global memory? ======================================= *)

in (* local *)

(*
val lbl_tm = ``BL_Address (Imm32 440w)``;
get_block_ lbl_tm

val addr = Arbnumcore.fromInt 440;
get_block_byAddr_ addr
*)

fun get_block_ lbl_tm =
    get_block  prog_blocks lbl_tm;

fun get_block_byAddr_ addr =
    get_block_byAddr  prog_blocks addr;

(*
val location = Arbnum.fromInt 0x01;
val location = Arbnum.fromInt 0x10000002;
val location = Arbnum.fromInt 0x10000040;
val location = Arbnum.fromInt 0x10000;

read_byte_from_init_mem location

val name = "imu_handler";
val name = "kp";
val name = "non_existent_symbol";

find_label_addr_ name
*)

fun read_byte_from_init_mem_ location =
    read_byte_from_data location da_data;

fun find_label_addr_ name =
    find_label_addr_data  name da_data;

end (* local *)
end (* struct *)
