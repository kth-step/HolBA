open HolKernel Parse;

open bir_inst_liftingTheory;
open bir_program_valid_stateTheory;

open bir_exec_envLib;
open bir_execLib;

open aesBinaryTheory;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

val _ = log_setfile "aes-test.log";

val _ = print "loading...\n";

val name = "lifted_aes_enc_part";

(* load lifter theorem *)
val liftertheorem = aes_arm8_program_THM;
val prog_l = ((dest_BirProgram o snd o dest_comb o concl) liftertheorem);

(* fix program to have a BIR halt instead of an armv8 ret at the end *)
val prog_l =
  let
    val (blocks,ty) = dest_list prog_l;
    val obs_ty = (hd o snd o dest_type) ty;
    val (lbl,a,_) = bir_programSyntax.dest_bir_block (List.last blocks);
    val new_last_block =  bir_programSyntax.mk_bir_block
              (lbl, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
               ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);

    val blocks' = (List.take (blocks, (List.length blocks) - 1))@[new_last_block];
  in
    mk_list (blocks',ty)
  end;

(* define a constant for the program, obtain validprog theorem *)
val prog_l_def = Define [QUOTE (name ^ "_prog_l = "), ANTIQUOTE prog_l];
val prog_const = (mk_BirProgram o fst o dest_eq o concl) prog_l_def;
val prog = prog_const;

val liftertheorem = REWRITE_RULE [GSYM prog_l_def] liftertheorem;

(* (* this is not valid anymore since we replaced the last block *)
val validprog_thm = prove(``
  bir_is_valid_program ^prog_const
``,
  REWRITE_TAC [bir_is_valid_program_def] >>
  STRIP_TAC >- (
    ASM_REWRITE_TAC [REWRITE_RULE [bir_is_lifted_prog_def] liftertheorem]
  ) >>
  SIMP_TAC list_ss [bir_program_is_empty_def, prog_l_def]
);
*)


val prog = (mk_BirProgram) prog_l;
val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog``;
val vars = gen_vars_of_prog prog;
val var_eq_thms = gen_var_eq_thms vars;

val num_aes_rounds = 14;
val num_aes_rounts_wtm = wordsSyntax.mk_wordii (num_aes_rounds, 64);

val env_init = bir_exec_env_initd_env vars;
(* SP *)
val env_1 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "SP_EL0" (BType_Imm Bit64)) (BVal_Imm (Imm64 0x8000000w)) ^env_init``;

(* *rk *)
val env_2 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R0" (BType_Imm Bit64)) (BVal_Imm (Imm64 0xA000000w)) ^env_1``;

(* r *)
val env_3 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R1" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(num_aes_rounts_wtm))) ^env_2``;

(* *inBlock *)
val env_4 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R2" (BType_Imm Bit64)) (BVal_Imm (Imm64 0xB000000w)) ^env_3``;

(* *outBlock *)
val env_5 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R3" (BType_Imm Bit64)) (BVal_Imm (Imm64 0xC000000w)) ^env_4``;

val env = env_5;
val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;



val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = SOME state;

(* set the number of steps *)
val n_max = 400 * 15 * 5;
(* 400 * 15 is an overapproximation of the number of blocks that would need to be executed *)
(* 5 per block should be enough and this should not take longer than 10h, let's see *)

val _ = print "ok\n"



(* run the execution *)
val _ = bir_exec_prog_print name prog_const n_max validprog_o welltypedprog_o state_o;


