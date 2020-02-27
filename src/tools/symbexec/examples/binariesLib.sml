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
        | SOME _ => raise ERR "find_single_SOME" "search criterion matched multiple times";

fun find_in_lbl find_in_block_f   item (l:disassembly_lbl) =
  find_single_SOME (List.map (find_in_block_f item) (#DAL_blocks l));

fun find_in_section find_in_lbl_f item (s:disassembly_section) =
  find_single_SOME (List.map (find_in_lbl_f item) (#DAS_lbls   s));

fun find_in_data    find_in_lbl_f item (d:disassembly_data) =
  find_single_SOME (List.map (find_in_section find_in_lbl_f item) d);

fun find_in_data_at_block find_in_block_f item (d:disassembly_data) =
    find_in_data (find_in_lbl find_in_block_f) item d;

fun find_in_data_at_lbl find_in_lbl_f item (d:disassembly_data) =
    find_in_data find_in_lbl_f item d;


fun is_addr_in_entry addr (e: disassembly_entry) =
  (Arbnumcore.<= (#DAE_addr e, addr)) andalso
  (Arbnumcore.< (addr, Arbnumcore.+ (#DAE_addr e, Arbnumcore.fromInt ((length (explode (#DAE_hex e))) div 2))));

fun read_byte_from_block addr (b: disassembly_block) =
  let
    val entries = List.filter (is_addr_in_entry addr) b;
    val bytes   = List.map (fn e =>
          let
            val offset  = Arbnumcore.-(addr, #DAE_addr e);
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


fun find_label_addr_lbl name (l:disassembly_lbl) =
  let val lbl_name = #DAL_name l in
  if name = lbl_name then
    SOME (#DAL_addr l)
  else
    NONE
  end;


fun find_label_by_addr_block addr name (b: disassembly_block) =
  let
    val entries = List.filter (is_addr_in_entry addr) b;
  in
    find_single_SOME (List.map (K (SOME name)) entries)
  end;

fun find_label_by_addr_lbl addr (l:disassembly_lbl) =
  find_single_SOME (List.map (find_label_by_addr_block addr (#DAL_name l)) (#DAL_blocks l));


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

fun mk_lbl_tm addr =
  (mk_BL_Address o mk_Imm32 o mk_word) (addr, Arbnum.fromInt 32);

(*
val addr = Arbnum.fromInt 0x01;
val addr = Arbnum.fromInt 0x10000002;
val addr = Arbnum.fromInt 0x10000040;
val addr = Arbnum.fromInt 0x10000;

read_byte_from_init_mem_ addr

val name = "imu_handler";
val name = "kp";
val name = "non_existent_symbol";

find_label_addr_ name

val addr = Arbnum.fromInt 65;
val addr = Arbnum.fromInt 828;
val addr = Arbnum.fromInt 0x10000002;

find_label_by_addr_ addr
*)

fun read_byte_from_init_mem_ addr =
    find_in_data_at_block read_byte_from_block addr da_data;

fun find_label_addr_ name =
    find_in_data_at_lbl find_label_addr_lbl name da_data;

fun find_label_by_addr_ addr =
    find_in_data_at_lbl find_label_by_addr_lbl addr da_data;

end (* local *)
end (* struct *)
