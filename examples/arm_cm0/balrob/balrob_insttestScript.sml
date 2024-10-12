open HolKernel Parse boolLib bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_immSyntax;

open bir_predLib;

open bir_symbLib;

open birs_mergeLib;
open birs_instantiationLib;
open birs_composeLib;

open balrobLib;
open balrob_ends_mergeTheory;

val _ = new_theory "balrob_insttest";

(* instantiation test *)
(* commonBalrobScriptLib.sml *)
val countw_space_req = 63;

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)
val insttest_init_addr = ``0x100012d6w : word32``;
val insttest_end_addrs = [``0x100013b4w : word32``];

(* -------------- *)
(* precondition   *)
(* -------------- *)
val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
fun mk_countw_const v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
fun mk_countw_plus tm v = bslSyntax.bplus (tm, mk_countw_const v);

val insttest_pre = (* TODO: need SP here too *)
  ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_const (0x10000000 - countw_space_req))``;

(* --------------------------- *)
(* Symbolic execution          *)
(* --------------------------- *)
val init_addr = insttest_init_addr;
val end_addrs = insttest_end_addrs;
val precond = insttest_pre;
val birenvtyl_def = balrob_birenvtyl_def;

val bprog_tm = (fst o dest_eq o concl) bir_balrob_prog_def;
fun mk_bir_lbl x = ``bir_block_pc (BL_Address ^(gen_mk_Imm x))``;
val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl;
val init_lbl = bir_lbl_from_addr init_addr;
val end_lbls = List.map bir_lbl_from_addr end_addrs;

val (birs_state_init, birs_env_thm, bsysprecond_thm) =
  bir_symb_analysis_init_gen (SOME pcond_gen_symb) init_lbl precond birenvtyl_def;
val symb_exec_thm =
  bir_symb_analysis bprog_tm end_lbls birs_state_init;

Theorem balrob_insttest_symb_exec_thm = symb_exec_thm

(* ------------------------------ *)

(*
val _ = print_thm balrob_clzsi2_symb_merged_thm;
val _ = raise Fail "";
*)

(* now try to instantiate *)
val _ = print "prepare generic SEQ thm\n";
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
val A_thm = balrob_insttest_symb_exec_thm;
val B_thm = balrob_clzsi2_symb_merged_thm;
(*
val _ = print_thm A_thm;
val _ = print_thm B_thm;
*)
val _ = print "start instantiation\n";
val cont_thm = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm pcond_gen_symb A_thm B_thm;

Theorem balrob_insttest_symb_inst_thm = cont_thm

(* now continue execution after that *)

val _ = export_theory ();


