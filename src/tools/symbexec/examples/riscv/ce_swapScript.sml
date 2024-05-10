open HolKernel Parse;

open bin_rv_swapTheory;

open bir_exec_envLib;
open bir_execLib;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;


val _ = log_setfile "exec.log";

val _ = new_theory "ce_swap";

val _ = print "loading...\n";

val name = "swap";
val bprog = List.nth((snd o strip_comb o concl) bin_rv_swap_thm, 3);
val prog_l = (dest_BirProgram) bprog;

(* set the maximum number of steps to execute *)
val n_max = 100;

(*  - input (a) is in memory at x10
    - input (b) is in memory at x11
    - output in memory and registers *)
val prog_par_a = 3;
val prog_par_b = 4;
val prog_x10 = 128;
val prog_x11 = 256;


(* translate the inputs to word terms *)
val prog_x10_wtm = wordsSyntax.mk_wordii (prog_x10, 64);
val prog_x11_wtm = wordsSyntax.mk_wordii (prog_x11, 64);

(* translate the inputs to num terms *)
val prog_par_a_ntm = (numSyntax.mk_numeral o Arbnum.fromInt) prog_par_a;
val prog_par_b_ntm = (numSyntax.mk_numeral o Arbnum.fromInt) prog_par_b;
val prog_x10_ntm = (numSyntax.mk_numeral o Arbnum.fromInt) prog_x10;
val prog_x11_ntm = (numSyntax.mk_numeral o Arbnum.fromInt) prog_x11;


(* patch the end of the program: has to have a BIR halt instead of an riscv ret *)
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
(* MEM8-ab *)
val env_1 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "MEM8" (BType_Mem Bit64 Bit8)) (BVal_Mem Bit64 Bit8 (FUPDATE (FUPDATE FEMPTY (^prog_x10_ntm, ^prog_par_a_ntm)) (^prog_x11_ntm, ^prog_par_b_ntm))) ^env_init``;

(*env_init;*)
(*(dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "SP_EL0" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_sp_wtm))) ^env_init``;
*)

(* x10 *)
val env_2 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "x10" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_x10_wtm))) ^env_1``;

(* x11 *)
val env_3 = (dest_some o snd o dest_eq o concl o (bir_exec_env_write_conv var_eq_thms))
            ``bir_env_write (BVar "x11" (BType_Imm Bit64)) (BVal_Imm (Imm64 ^(prog_x11_wtm))) ^env_2``;

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
(*
val thm = bir_exec_prog_print name prog_const n_max validprog_o welltypedprog_o state_o;
Theorem bin_rv_swap_conreteexec_thm = thm

*)


val _ = export_theory();

