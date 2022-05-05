open HolKernel Parse boolLib bossLib;

open bslSyntax listSyntax wordsSyntax;
open bir_execLib bir_bool_expTheory;

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
val resolve_fail_prog'_thm = EVAL “resolve_fail ^prog_tm (BL_Address (Imm64 0w))”
val resolve_fail_prog'_tm = (dest_some o rhs o concl) resolve_fail_prog'_thm

val resolve_prog'_thm = EVAL “resolve ^prog_tm (BL_Address (Imm64 0w)) (Imm64 10w) "0w-1"”
val resolve_prog'_tm = (dest_some o rhs o concl) resolve_prog'_thm


(*resolve_fully test*)
val arg1 = “BL_Address (Imm64 0w)”
val arg2 = “[(Imm64 10w, "0w-1"); (Imm64 4w, "0w-2")]”
val resolve_fully_prog'_thm = EVAL “resolve_fully ^prog_tm ^arg1 ^arg2”
val resolve_fully_prog'_tm = (dest_some o rhs o concl) resolve_fully_prog'_thm


(*resolve_fully_n one indirect jump test many steps*)
val resolve_fully_n_args = “[(^arg1, ^arg2)]”
val resolve_fully_n_prog'_thm = EVAL “resolve_fully_n ^prog_tm ^resolve_fully_n_args”
val resolve_fully_n_prog'_tm = (dest_some o rhs o concl) resolve_fully_n_prog'_thm


(*resolve_fully_n many indirect jumps many steps test*)
val block1' = (blabel_addr64 8,
               [bassign (bvarimm64 "z", bconst64 4)],
               (bjmp o belabel_expr o bden o bvarimm64) "z")
val prog2_def = bdefprog_list "prog2" [block1, block2, block1']
val prog2_tm = (rhs o concl) prog2_def

val prog2_args = “[(^arg1, ^arg2);
                   (BL_Address (Imm64 8w), [(Imm64 10w, "8w-1"); (Imm64 4w, "8w-2")])]”
val prog2'_thm = EVAL “resolve_fully_n ^prog2_tm ^prog2_args”
val prog2'_tm = (dest_some o rhs o concl) prog2'_thm


(*resolve_indirect_jumps and transfer_contract test*)
(*Transform program*)
val small_args = “[(BL_Address (Imm64 0w), [(Imm64 4w, "0w-2")])]”
val (small_prog'_def, small_prog'_thm) = 
  resolve_indirect_jumps("resolved_small_prog", prog_tm, small_args)

(*Obtain WP contract*)
val pre_def = Define ‘pre = bir_exp_true’
val post_def = Define ‘post = ^(beq((bden o bvarimm64) "y", bconst64 4))’
val prefix = "example1"
val pre_tm = (lhs o concl) pre_def
val entry_label_tm = “BL_Address (Imm64 0w)”

val ending_labels_tm = “{BL_Address (Imm64 4w)}”
val post_tm = “\l. if (l = BL_Address (Imm64 4w))
                   then post
                   else bir_exp_false”
val defs = [small_prog'_def, post_def, bir_exp_false_def]

val small_contract = prove_and_transfer_contract(small_prog'_thm,
                                                 prefix, pre_tm, entry_label_tm,
                                                 ending_labels_tm, post_tm, defs)


(*Larger resolve_indirect_jumps and transfer_contract test*)
val middle_blocks_n = 10;
val exit_addr = 10 * middle_blocks_n
val large_prog_def = gen_program("prog", middle_blocks_n)
val large_prog_tm = (lhs o concl) large_prog_def

val large_prog_args = gen_args_program(middle_blocks_n, 1)
val (large_prog'_def, large_prog'_thm) = 
  resolve_indirect_jumps("resolved_large_prog", large_prog_tm, large_prog_args)


val pre_def = Define ‘pre = ^(blt((bden o bvarimm64) "x", (bconst64 middle_blocks_n)))’
val post_def = Define ‘post = ^(beq((bden o bvarimm64) "y", bconst64 exit_addr))’
val prefix = "example2"
val pre_tm = (lhs o concl) pre_def
val entry_label_tm = “BL_Label "entry1"”
val ending_labels_tm = “{^(blabel_addr64 exit_addr)}”
val post_tm = “\l. if (l = ^(blabel_addr64 exit_addr))
                   then post
                   else bir_exp_false”
val defs = [large_prog'_def, post_def, bir_exp_false_def, bir_exp_true_def]

val large_contract = prove_and_transfer_contract(large_prog'_thm,
                                                 prefix, pre_tm, entry_label_tm,
                                                 ending_labels_tm, post_tm, defs)


val _ = export_theory();

