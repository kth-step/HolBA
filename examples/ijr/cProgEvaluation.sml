open HolKernel Parse boolLib bossLib;

open bir_lifter_interfaceLib;
open bir_execLib bir_bool_expTheory;

open resolveFullyLib;
open generationLib;
open timersLib;

val lift_start = timer_start ()
val _ = lift_da_and_store "composition"
                          "composition.da"
                          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
val _ = print ("Lifting time: " ^ timer_stop_str lift_start ^ "\n")


fun eval tm = (snd o dest_eq o concl o EVAL) tm

val blocks = (fst o dest_list o dest_BirProgram o eval) “bir_composition_prog”

val endings = List.map (fn block_tm => eval “ ^block_tm.bb_last_statement”) blocks
val add_one_ret = el 6 blocks
val add_two_ret = el 12 blocks
val call_add_one = el 20 blocks
val call_add_two = el 22 blocks
val comp_ret = el 24 blocks
val add_two_three = el 35 blocks

fun addr_to_int addr = (dest_word_literal o snd o gen_dest_Imm o dest_BL_Address) addr

val add_one_entry_address = (#1 o dest_bir_block o el 1) blocks
val add_one_ret_address = (#1 o dest_bir_block o el 6) blocks
val add_two_entry_address = (#1 o dest_bir_block o el 7) blocks
val add_two_ret_address = (#1 o dest_bir_block o el 12) blocks

val call_add_one_address = (#1 o dest_bir_block o el 20) blocks
val call_add_one_next_address = (#1 o dest_bir_block o el 21) blocks
val call_add_two_address = (#1 o dest_bir_block o el 22) blocks
val call_add_two_next_address = (#1 o dest_bir_block o el 23) blocks

val comp_entry_address = (#1 o dest_bir_block o el 13) blocks
val comp_ret_address = (#1 o dest_bir_block o el 24) blocks
val call_comp_next_adress = (#1 o dest_bir_block o el 34) blocks


(*Transform program*)
val add_two_ret_args = [(add_two_ret_address, [0x400050], ["0x400014w-1"])]
val add_one_ret_args = [(add_one_ret_address, [0x400058], ["0x40002Cw-1"])]
val call_add_two_args = [(call_add_two_address, [0x400000], ["0x40004Cw-1"])]
val call_add_one_args = [(call_add_one_address, [0x400018], ["0x400054w-1"])]
val comp_ret_args = [(comp_ret_address, [0x400084], ["0x40005Cw-1"])]

val composition_args = gen_args (add_two_ret_args @
                                 add_one_ret_args @
                                 call_add_two_args @
                                 call_add_one_args @
                                 comp_ret_args )

val transfer_start = timer_start ()
val (cprog'_def, cprog'_thm) = 
  resolve_indirect_jumps("resolved_composition_prog", “bir_composition_prog”, composition_args)
val _ = print ("Resolve time: " ^ timer_stop_str transfer_start ^ "\n")

val blocks' = (fst o dest_list o dest_BirProgram o eval o lhs o concl) cprog'_def
val endings' = List.map (fn block_tm => eval “ ^block_tm.bb_last_statement”) blocks'

(*Obtain WP contract*)
val get_sp = bden (bvar "SP_EL0" “(BType_Imm Bit64)”)
val pre_def = Define ‘pre = ^(beq(get_sp, bconst64 0xE0000000))’
val post_def = Define ‘post = bir_exp_true’
val prefix = "example3"
val pre_tm = (lhs o concl) pre_def
val entry_label_tm = “BL_Address (Imm64 0x400070w)”
val ending_labels_tm = “{BL_Address (Imm64 0x400084w)}”
val post_tm = “\l. if (l = BL_Address (Imm64 0x400084w))
                   then post
                   else bir_exp_false”
val defs = [cprog'_def, post_def, bir_exp_false_def, bir_exp_true_def]

val ccontract = prove_and_transfer_contract(cprog'_thm,
                                            prefix, pre_tm, entry_label_tm,
                                            ending_labels_tm, post_tm, defs)
