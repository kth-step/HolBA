structure binariesLib =
struct
local

open binariesTheory;
open binariesDefsLib;

open bir_block_collectionLib;

open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_inst_liftingHelpersLib;

open bir_exec_typingLib;

open listSyntax;
open wordsSyntax;
open stringSyntax;


(* ad hoc helpers *)
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


(* ===================================== program behavior ======================================= *)
val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
    (DB.fetch "binaries" thm_name);

val bl_dict_0    = gen_block_dict prog_tm;
val prog_lbl_tms = get_block_dict_keys bl_dict_0;

(* TODO: why is this step necessary? what's wrong in the lifter? *)
val bl_dict    = update_dict_gen "fix_jumps" (fix_jumps) prog_lbl_tms bl_dict_0;


val prog_vars = gen_vars_of_prog prog_tm;

(* =============================== memory contents (including data) ============================= *)

local
  open gcc_supportLib;
in
  val da_data_mem = read_disassembly_file symb_filter_mem da_file_mem;
end
(*
val _ = print_disassembly_data da_data_mem;
*)

open bir_gcc_dataLib;

(* ===================================== symbolic variables for inputs in global memory? ======================================= *)

in (* local *)

(*
val lbl_tm = ``BL_Address (Imm32 440w)``;
val addr = Arbnumcore.fromInt 440;
*)

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
