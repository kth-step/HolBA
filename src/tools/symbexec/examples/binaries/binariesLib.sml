structure binariesLib =
struct
local

open binariesTheory;
open binariesDefsLib;

open gcc_supportLib;

open bir_programSyntax;
open bir_immSyntax;
open bir_exec_typingLib;
open bir_envSyntax;

open listSyntax;
open wordsSyntax;
open stringSyntax;

open Redblackmap;

(* ====================== put in the right place =================================== *)

local
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_immTheory bir_valuesTheory bir_programTheory;


val ERR = mk_HOL_ERR "bir_program_labelsSyntax"
val wrap_exn = Feedback.wrap_exn "bir_program_labelsSyntax"

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_labels"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
in
val (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC)  = syntax_fns2 "BL_Address_HC";
end

(* ================================================================================= *)


(* ===================================== program behavior ======================================= *)
val (_, mem_wi_prog_tm, mem_tm, prog_tm) = (dest_bir_is_lifted_prog o concl) balrob_program_THM;
val prog_bls = (fst o dest_list o dest_BirProgram) prog_tm;

val prog_blocks_dict =
  let
    val lbl_block_pairs =
      List.foldr (fn (bl, l) => (
        let
          val (lbl, _, _) = dest_bir_block bl;
          val lbl_tm      = (snd o dest_eq o concl o EVAL) lbl;
        in
          (lbl_tm, bl)
        end
      )::l) [] prog_bls;

    val _ = print ("found " ^ (Int.toString (length prog_bls))  ^ " blocks in lifted program\n");
  in
    Redblackmap.insertList (Redblackmap.mkDict Term.compare, lbl_block_pairs)
  end;

fun prog_get_block bl_dict lbl_tm =
  SOME (Redblackmap.find (bl_dict, lbl_tm))
  handle NotFound => NONE;

fun prog_get_block_byAddr bl_dict addr =
    prog_get_block bl_dict ((mk_BL_Address o mk_Imm32 o mk_word) (addr, Arbnum.fromInt 32));

val prog_lbl_tms =
  List.map ((snd o dest_eq o concl o EVAL) o (fn (a, _, _) => a) o dest_bir_block) prog_bls;

val prog_vars = gen_vars_of_prog prog_tm;

(* =============================== memory contents (including data) ============================= *)


val da_data_mem = read_disassembly_file symb_filter_mem da_file_mem;
(*
val _ = print_disassembly_data da_data_mem;
*)

fun find_single_SOME []             = NONE
  | find_single_SOME ( NONE   ::xs) = find_single_SOME xs
  | find_single_SOME ((SOME x)::xs) =
      case find_single_SOME xs of
	  NONE   => SOME x
        | SOME _ => raise ERR "find_single_SOME" "search criterion matched multiple times";

fun mem_find_in_lbl mem_find_in_block_f   item (l:disassembly_lbl) =
  find_single_SOME (List.map (mem_find_in_block_f item) (#DAL_blocks l));

fun mem_find_in_section mem_find_in_lbl_f item (s:disassembly_section) =
  find_single_SOME (List.map (mem_find_in_lbl_f item) (#DAS_lbls   s));

fun mem_find_in_data    mem_find_in_lbl_f item (d:disassembly_data) =
  find_single_SOME (List.map (mem_find_in_section mem_find_in_lbl_f item) d);

fun mem_find_in_data_at_block mem_find_in_block_f item (d:disassembly_data) =
    mem_find_in_data (mem_find_in_lbl mem_find_in_block_f) item d;

fun mem_find_in_data_at_lbl mem_find_in_lbl_f item (d:disassembly_data) =
    mem_find_in_data mem_find_in_lbl_f item d;


fun is_addr_in_entry addr (e: disassembly_entry) =
  (Arbnumcore.<= (#DAE_addr e, addr)) andalso
  (Arbnumcore.< (addr, Arbnumcore.+ (#DAE_addr e, Arbnumcore.fromInt ((length (explode (#DAE_hex e))) div 2))));

fun mem_read_byte_from_block addr (b: disassembly_block) =
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


fun mem_find_symbol_addr_lbl name (l:disassembly_lbl) =
  let val lbl_name = #DAL_name l in
  if name = lbl_name then
    SOME (#DAL_addr l)
  else
    NONE
  end;


fun mem_find_symbol_by_addr_block addr name (b: disassembly_block) =
  let
    val entries = List.filter (is_addr_in_entry addr) b;
  in
    find_single_SOME (List.map (K (SOME name)) entries)
  end;

fun mem_find_symbol_by_addr_lbl addr (l:disassembly_lbl) =
  find_single_SOME (List.map (mem_find_symbol_by_addr_block addr (#DAL_name l)) (#DAL_blocks l));


(* ===================================== symbolic variables for inputs in global memory? ======================================= *)

in (* local *)

(*
val lbl_tm = ``BL_Address (Imm32 440w)``;
prog_get_block_ lbl_tm

val addr = Arbnumcore.fromInt 440;
prog_get_block_byAddr_ addr
*)

fun prog_get_block_ lbl_tm =
    prog_get_block  prog_blocks_dict lbl_tm;

fun prog_get_block_byAddr_ addr =
    prog_get_block_byAddr  prog_blocks_dict addr;

fun mk_lbl_tm addr =
  (mk_BL_Address o mk_Imm32 o mk_word) (addr, Arbnum.fromInt 32);

fun dest_lbl_tm lbl_tm =
  (dest_word_literal o dest_Imm32 o dest_BL_Address o snd o dest_eq o concl o EVAL) lbl_tm

val prog_vars = prog_vars;
val prog_var_types = List.map (fn t =>
      let val (bn, bty) = dest_BVar t in
      (fromHOLstring bn, bty) end
  ) prog_vars;

(*
val addr = Arbnum.fromInt 0x01;
val addr = Arbnum.fromInt 0x10000002;
val addr = Arbnum.fromInt 0x10000040;
val addr = Arbnum.fromInt 0x10000;

mem_read_byte_from_init_mem_ addr

val name = "imu_handler";
val name = "kp";
val name = "non_existent_symbol";

mem_find_symbol_addr_ name

val addr = Arbnum.fromInt 65;
val addr = Arbnum.fromInt 828;
val addr = Arbnum.fromInt 0x10000002;

mem_find_symbol_by_addr_ addr
*)

fun mem_read_byte_from_init_mem_ addr =
    mem_find_in_data_at_block mem_read_byte_from_block addr da_data_mem;

fun mem_find_symbol_addr_ name =
    mem_find_in_data_at_lbl mem_find_symbol_addr_lbl name da_data_mem;

fun mem_find_rel_symbol_by_addr_ addr =
    mem_find_in_data_at_lbl mem_find_symbol_by_addr_lbl addr da_data_mem;

fun mem_symbol_to_prog_lbl name =
    (mk_lbl_tm o valOf o mem_find_symbol_addr_) name
    handle Option => raise ERR "mem_symbol_to_prog_lbl" ("cannot find addr for label: " ^ name);


val prog_fun_entry_lbl_tms = List.map mem_symbol_to_prog_lbl symbs_sec_text;
val prog_lbl_tms_ = prog_lbl_tms;

fun prog_lbl_to_mem_rel_symbol lbl_tm =
  (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) lbl_tm
  handle Option => raise ERR "prog_lbl_to_mem_symbol" ("cannot find label: " ^ (term_to_string lbl_tm));


val (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC)  = (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC);

end (* local *)
end (* struct *)
