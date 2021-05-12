open HolKernel Parse boolLib bossLib;

open bslSyntax listSyntax wordsSyntax;
open bir_execLib bir_bool_expTheory;
open bir_lifter_interfaceLib;

open resolveFullyLib generationLib;

val _ = new_theory "examples";


val _ = bir_ppLib.install_bir_pretty_printers();

val block1 = (blabel_addr64 0,
              [bassign (bvarimm64 "y", bconst64 4)],
              (bjmp o belabel_expr o bden o bvarimm64) "y")

val block2: term * term list * term  = (blabel_addr64 4,
                                        [],
                                        (bhalt o bconst64) 0)


(*Program definition*)
val prog_def = bdefprog_list "prog" [block1, block2]
val prog_tm = (lhs o concl) prog_def

(*resolve_fail and resolve tests*)
val resolve_fail_prog'_thm = EVAL “resolve_fail ^prog_tm (BL_Address (Imm64 0w)) (Imm64 4w)”
val resolve_fail_prog'_tm = (dest_some o rhs o concl) resolve_fail_prog'_thm

val resolve_prog'_thm = EVAL “resolve ^prog_tm (BL_Address (Imm64 0w)) (Imm64 10w) "0w-1"”
val resolve_prog'_tm = (dest_some o rhs o concl) resolve_prog'_thm


(*resolve_fully test*)
val arg1 = “BL_Address (Imm64 0w)”
val arg2 = “[(Imm64 10w, "0w-1"); (Imm64 4w, "0w-2")]”
val arg3 = “Imm64 4w”
val resolve_fully_prog'_thm = EVAL “resolve_fully ^prog_tm ^arg1 ^arg2 ^arg3”
val resolve_fully_prog'_tm = (dest_some o rhs o concl) resolve_fully_prog'_thm


(*resolve_fully_n one indirect jump test many steps*)
val resolve_fully_n_args = “[(^arg1, ^arg2, ^arg3)]”
val resolve_fully_n_prog'_thm = EVAL “resolve_fully_n ^prog_tm ^resolve_fully_n_args”
val resolve_fully_n_prog'_tm = (dest_some o rhs o concl) resolve_fully_n_prog'_thm


(*resolve_fully_n many indirect jumps many steps test*)
val block1' = (blabel_addr64 8,
               [bassign (bvarimm64 "z", bconst64 4)],
               (bjmp o belabel_expr o bden o bvarimm64) "z")
val prog2_def = bdefprog_list "prog2" [block1, block2, block1']
val prog2_tm = (rhs o concl) prog2_def

val prog2_args = “[(^arg1, ^arg2, ^arg3);
             (BL_Address (Imm64 8w), [(Imm64 10w, "8w-1"); (Imm64 4w, "8w-2")], ^arg3)]”
val prog2'_thm = EVAL “resolve_fully_n ^prog2_tm ^prog2_args”
val prog2'_tm = (dest_some o rhs o concl) prog2'_thm


(*resolve_indirect_jumps and transfer_contract test*)
(*Transform program*)
val small_args = “[(BL_Address (Imm64 0w), [(Imm64 4w, "0w-2")], ^arg3)]”
val (small_prog'_tm, small_prog'_def, small_prog'_thm) = 
  resolve_indirect_jumps("resolved_small_prog", prog_tm, small_args)

(*Obtain WP contract*)
val pre_def = Define ‘pre = bir_exp_true’
val post_def = Define ‘post = ^(beq((bden o bvarimm64) "y", bconst64 4))’
val prefix = "example1_"
val pre_tm = (lhs o concl) pre_def
val entry_label_tm = “BL_Address (Imm64 0w)”
val ending_labels_tm = “{BL_Address (Imm64 4w)}”
val post_tm = “\l. if (l = BL_Address (Imm64 4w))
                   then post
                   else bir_exp_false”
val defs = [small_prog'_def, post_def, bir_exp_false_def]

val small_contract = prove_and_transfer_contract(prog_tm, small_prog'_tm, small_prog'_thm,
                                                 prefix, pre_tm, entry_label_tm,
                                                 ending_labels_tm, post_tm, defs)


(*Larger resolve_indirect_jumps and transfer_contract test*)
val middle_blocks_n = 10;
val exit_addr = 10 * middle_blocks_n
val large_prog_def = gen_program("prog", middle_blocks_n)
val large_prog_tm = (lhs o concl) large_prog_def

val large_prog_args = gen_args_program(middle_blocks_n, 1)
val (large_prog'_tm, large_prog'_def, large_prog'_thm) = 
  resolve_indirect_jumps("resolved_large_prog", large_prog_tm, large_prog_args)

val pre_def = Define ‘pre = ^(blt((bden o bvarimm64) "x", (bconst64 middle_blocks_n)))’
val post_def = Define ‘post = ^(beq((bden o bvarimm64) "y", bconst64 exit_addr))’
val prefix = "example2_"
val pre_tm = (lhs o concl) pre_def
val entry_label_tm = “BL_Label "entry1"”
val ending_labels_tm = “{^(blabel_addr64 exit_addr)}”
val post_tm = “\l. if (l = ^(blabel_addr64 exit_addr))
                   then post
                   else bir_exp_false”
val defs = [large_prog'_def, post_def, bir_exp_false_def, bir_exp_true_def]

val large_contract = prove_and_transfer_contract(large_prog_tm, large_prog'_tm, large_prog'_thm,
                                                 prefix, pre_tm, entry_label_tm,
                                                 ending_labels_tm, post_tm, defs)
(*c test*)
val _ = lift_da_and_store "composition"
                          "composition.da"
                          ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));

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
val add_two_ret_args = [(add_two_ret_address, [0x400050], ["0x400014w-1"], 0x400084)]
val add_one_ret_args = [(add_one_ret_address, [0x400058], ["0x40002Cw-1"], 0x400084)]
val call_add_two_args = [(call_add_two_address, [0x400000], ["0x40004Cw-1"], 0x400084)]
val call_add_one_args = [(call_add_one_address, [0x400018], ["0x400054w-1"], 0x400084)]
val comp_ret_args = [(comp_ret_address, [0x400084], ["0x40005Cw-1"], 0x400084)]

val composition_args = gen_args (add_two_ret_args @
                                 add_one_ret_args @
                                 call_add_two_args @
                                 call_add_one_args @
                                 comp_ret_args )
val (cprog'_tm, cprog'_def, cprog'_thm) = 
  resolve_indirect_jumps("resolved_composition_prog", “bir_composition_prog”, composition_args)

val blocks' = (fst o dest_list o dest_BirProgram o eval) cprog'_tm
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

val ccontract = prove_and_transfer_contract(“bir_composition_prog”, cprog'_tm, cprog'_thm,
                                            prefix, pre_tm, entry_label_tm,
                                            ending_labels_tm, post_tm, defs)


val _ = export_theory();

