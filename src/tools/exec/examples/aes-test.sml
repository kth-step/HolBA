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

(* define a constant for the program, obtain validprog theorem *)
val prog_l_def = Define [QUOTE (name ^ "_prog_l = "), ANTIQUOTE prog_l];
val prog_const = (mk_BirProgram o fst o dest_eq o concl) prog_l_def;
val prog = prog_const;

val liftertheorem = REWRITE_RULE [GSYM prog_l_def] liftertheorem;

val validprog_thm = prove(``
  bir_is_valid_program ^prog_const
``,
  REWRITE_TAC [bir_is_valid_program_def] >>
  STRIP_TAC >- (
    ASM_REWRITE_TAC [REWRITE_RULE [bir_is_lifted_prog_def] liftertheorem]
  ) >>
  SIMP_TAC list_ss [bir_program_is_empty_def, prog_l_def]
);


val prog = (mk_BirProgram) prog_l;
val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog``;
val vars = gen_vars_of_prog prog;
val var_eq_thms = gen_var_eq_thms vars;

val env_init = bir_exec_env_initd_env vars;
val env = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
          ``bir_env_write (BVar "SP_EL0" (BType_Imm Bit64)) (BVal_Imm (Imm64 0x8000000w)) ^env_init``;

val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;



val validprog_o = SOME validprog_thm;
val welltypedprog_o = NONE;
val state_o = SOME state;

(* set the number of steps *)
val n_max = 400 * 15; (* these are not enough steps, this is just an overapproximation of the blocks that have to be executed *)

val _ = print "ok\n"



(* run the execution *)
val _ = bir_exec_prog_print name prog_const n_max validprog_o welltypedprog_o state_o;


