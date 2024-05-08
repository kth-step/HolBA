open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aesTheory;

val _ = new_theory "aes_symb_exec";

(* ---------------------------- *)
(* Program variable definitions *)
(* ---------------------------- *)

Definition aes_prog_vars_def:
  aes_prog_vars = [
    BVar "MEM8" (BType_Mem Bit64 Bit8);
    BVar "x31" (BType_Imm Bit64);
    BVar "x30" (BType_Imm Bit64);
    BVar "x29" (BType_Imm Bit64);
    BVar "x28" (BType_Imm Bit64);
    BVar "x18" (BType_Imm Bit64);
    BVar "x17" (BType_Imm Bit64);
    BVar "x16" (BType_Imm Bit64);
    BVar "x15" (BType_Imm Bit64);
    BVar "x14" (BType_Imm Bit64);
    BVar "x13" (BType_Imm Bit64);
    BVar "x12" (BType_Imm Bit64);
    BVar "x11" (BType_Imm Bit64);
    BVar "x10" (BType_Imm Bit64);
    BVar "x9" (BType_Imm Bit64);
    BVar "x8" (BType_Imm Bit64);
    BVar "x7" (BType_Imm Bit64);
    BVar "x6" (BType_Imm Bit64);
    BVar "x5" (BType_Imm Bit64);
    BVar "x2" (BType_Imm Bit64);
    BVar "x1" (BType_Imm Bit64)
  ]
End

Definition aes_birenvtyl_def:
  aes_birenvtyl = MAP BVarToPair aes_prog_vars
End

Theorem aes_prog_vars_thm:
  set aes_prog_vars = bir_vars_of_program (bir_aes_prog : 'observation_type bir_program_t)
Proof
  SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_aes_prog_def, aes_prog_vars_def] >>
  EVAL_TAC
QED

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_tm = (snd o dest_eq o concl) bir_aes_prog_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x000w))``;

val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x400w))``];

val bprog_envtyl = (fst o dest_eq o concl) aes_birenvtyl_def;

(* FIXME: need lots of memory address alignment here *)
val birs_pcond = ``bir_exp_true``;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

(*
val result = bir_symb_analysis bprog_tm
 birs_state_init_lbl birs_stop_lbls
 bprog_envtyl birs_pcond;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);

Theorem aes_symb_analysis_thm = result
*)

val _ = export_theory ();
