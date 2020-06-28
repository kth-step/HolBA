structure binariesLib =
struct
local

open binariesTheory;
open binariesDefsLib;

open bir_block_collectionLib;
open gcc_supportLib;

open bir_programSyntax;
open bir_program_labelsSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_exec_typingLib;
open bir_envSyntax;

open listSyntax;
open wordsSyntax;
open stringSyntax;


(* helpers *)
  fun update_dict_gen err_src_str update_fun lbl_tms_in n_dict_in =
      let
	fun update_n_dict (lbl_tm, n_dict) =
	  let
	    val n =
		    case lookup_block_dict n_dict lbl_tm of
		       SOME x => x
		     | NONE => raise ERR ("cfg_update_nodes_gen::" ^ err_src_str)
                                         ("cannot find label " ^ (term_to_string lbl_tm));

	    val n_o = update_fun n;
	    val n_dict' = if isSome n_o then
				Redblackmap.update (n_dict, lbl_tm, K (valOf n_o))
			      else
				n_dict;
	  in
	    n_dict'
	  end;
      in
	List.foldr update_n_dict n_dict_in lbl_tms_in
      end;


(* ===================================== program behavior ======================================= *)
val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
    (DB.fetch "binaries" thm_name);

val bl_dict_0    = gen_block_dict prog_tm;
val prog_lbl_tms = get_block_dict_keys bl_dict_0;

(* TODO: why is this step necessary? what's wrong in the lifter? *)
fun fix_jumps bl =
  let
    val (lbl_tm, bs, bes) = dest_bir_block bl;
  in
    if not (is_BStmt_Jmp bes) then NONE else
    let val ble = dest_BStmt_Jmp bes; in
      if is_BLE_Label ble then NONE else
      let
        val ble_exp_tm = dest_BLE_Exp ble;
        val ble_exp_eval_tm = (snd o dest_eq o concl o EVAL) (``bir_eval_exp ^ble_exp_tm (BEnv (K NONE))``);
      in
        if is_none ble_exp_eval_tm then NONE else
        let
          val imm = ((dest_BVal_Imm o dest_some) ble_exp_eval_tm);
          val bes' = (mk_BStmt_Jmp o mk_BLE_Label o mk_BL_Address) imm;
        in
          SOME (mk_bir_block (lbl_tm, bs, bes'))
        end
      end
    end
  end;


val bl_dict    = update_dict_gen "fix_jumps" (fix_jumps) prog_lbl_tms bl_dict_0;

(* this is redundant *)
fun prog_get_block bl_dict lbl_tm = lookup_block_dict bl_dict lbl_tm;
fun prog_get_block_byAddr bl_dict addr = lookup_block_dict_byAddr32 bl_dict addr;
(* --- *)


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
    prog_get_block  bl_dict lbl_tm;

fun prog_get_block_byAddr_ addr =
    prog_get_block_byAddr  bl_dict addr;

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


val prog_fun_entry_lbl_tms = List.foldr (fn (symb, l) =>
      (mem_symbol_to_prog_lbl symb)::l handle HOL_ERR _ => l
) [] symbs_sec_text;
val bl_dict_ = bl_dict;
val prog_lbl_tms_ = prog_lbl_tms;

fun prog_lbl_to_mem_rel_symbol lbl_tm =
  (valOf o mem_find_rel_symbol_by_addr_ o dest_lbl_tm) lbl_tm
  handle Option => raise ERR "prog_lbl_to_mem_symbol" ("cannot find label: " ^ (term_to_string lbl_tm));


end (* local *)
end (* struct *)
