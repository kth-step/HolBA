open HolKernel Parse;

open bir_prog_add_regTheory;

open bir_exec_envLib;
open bir_execLib;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;


val _ = log_setfile "exec.log";


val _ = print "loading...\n";

val name = "add_reg";
val prog_l = (dest_BirProgram o rhs o concl) bir_add_reg_prog_def;

(* set the maximum number of steps to execute *)
val n_max = 100;

(* folowing the calling convention:
    - input (x) is in R0
    - input (y) is in R1
    - output (ly) is in R0 *)
val prog_par_x = 3;
val prog_par_y = 7;
val prog_sp = 0x8000000;

(* translate the inputs to word terms *)
val prog_par_x_wtm = wordsSyntax.mk_wordii (prog_par_x, 64);
val prog_par_y_wtm = wordsSyntax.mk_wordii (prog_par_y, 64);
val prog_sp_wtm = wordsSyntax.mk_wordii (prog_sp, 64);


(* patch the end of the program: has to have a BIR halt instead of an arm8 ret *)
(* convention: last statement has to be the "exit" *)
val _ = print "patching in a \"halt\" statement...";
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

(* define a constant for the program *)
val prog_l_def = Define [QUOTE (name ^ "_prog_l = "), ANTIQUOTE prog_l];
val prog_const = (mk_BirProgram o fst o dest_eq o concl) prog_l_def;

(* obtain initial state for prog_l *)
val prog = (mk_BirProgram) prog_l;

val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog``;

val vars = gen_vars_of_prog prog;
val var_eq_thms = gen_var_eq_thms vars;

val env_init = bir_exec_env_initd_env vars;
(* SP *)
val env_1 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "SP_EL0" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_sp_wtm))) ^env_init``;

(* x *)
val env_2 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R0" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_par_x_wtm))) ^env_1``;

(* y *)
val env_3 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "R1" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_par_y_wtm))) ^env_2``;

val env = env_3;
val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;


val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = SOME state;

val _ = print "ok\n" (* loading complete *)

(* print program labels *)
val _ = print "\n";
val _ = print "label list:\n";
val _ = print "<------------------------------------------------->\n";
val labels = (
               fst o dest_list o snd o dest_eq o concl o
               (computeLib.RESTR_EVAL_CONV [``BL_Address_HC``])
             )``bir_labels_of_program ^prog_const``;
val _ = List.foldl (fn (t,_) => print_term t) () labels;
val _ = print "<------------------------------------------------->\n";
val _ = print "\n";


(* run the execution *)
val thm = bir_exec_prog_print name prog_const n_max validprog_o welltypedprog_o state_o;


