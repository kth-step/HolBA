open HolKernel Parse boolLib bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_immSyntax;

open bir_predLib;

open bir_symbLib;

open balrobLib;

val _ = new_theory "balrob_ends";

(* __clzsi2 *)

(* commonBalrobScriptLib.sml *)
val countw_space_req = 21;

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)
val clzsi2_init_addr = ``0x100013b4w : word32``;
val clzsi2_end_addrs = [``0x100013dcw : word32``];

(* -------------- *)
(* precondition   *)
(* -------------- *)
val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
fun mk_countw_const v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
fun mk_countw_plus tm v = bslSyntax.bplus (tm, mk_countw_const v);

val clzsi2_pre = (* TODO: need SP here too *)
  ``BExp_BinPred BIExp_LessOrEqual
       ^(bir_countw_bvar_tm)
       ^(mk_countw_const (0x10000000 - countw_space_req))``;


(* --------------------------- *)
(* Symbolic execution          *)
(* --------------------------- *)
val bprog_tm = (fst o dest_eq o concl) bir_balrob_prog_def;
fun mk_bir_lbl x = ``bir_block_pc (BL_Address ^(gen_mk_Imm x))``;
val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl;
val init_lbl = bir_lbl_from_addr clzsi2_init_addr;
val end_lbls = List.map bir_lbl_from_addr clzsi2_end_addrs;

val (birs_state_init, birs_env_thm, bsysprecond_thm) =
  bir_symb_analysis_init_gen (SOME pcond_gen_symb) init_lbl clzsi2_pre balrob_birenvtyl_def;
val symb_exec_thm =
  bir_symb_analysis bprog_tm end_lbls birs_state_init;

(* TODO: should merge Pi states here *)
val symb_exec_merged_thm = symb_exec_thm;

Theorem balrob_clzsi2_symb_exec_thm = symb_exec_merged_thm

(* only need the following two theorems for property transfer,
    then also need to instantiate pcond_gen_symb with the hol free variable constant conditions *)
Theorem balrob_clzsi2_bsysprecond_thm = bsysprecond_thm
Theorem balrob_clzsi2_birs_env_thm = birs_env_thm

val _ = export_theory ();
