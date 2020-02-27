open HolKernel Parse

open binariesTheory;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;


(* ===================================== program behavior ======================================= *)
val (_, mem_wi_prog_tm, mem_tm, prog_tm) = (dest_bir_is_lifted_prog o concl) balrob_program_THM;


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

fun find_single_SOME []             = NONE
  | find_single_SOME ( NONE   ::xs) = read_byte_find_one xs
  | find_single_SOME ((SOME x)::xs) =
      case read_byte_find_one xs of
	  NONE   => SOME x
        | SOME _ => raise ERR "read_byte_find_one" "location exists multiple times";

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

fun read_byte_from_init_mem location =
  find_single_SOME (List.map (read_byte_from_section location) da_data        );
(*
val _ = print_disassembly_data da_data;

read_byte_from_init_mem (Arbnum.fromInt 0x10000002);
*)


(* ===================================== symbolic variables for inputs in global memory? ======================================= *)

