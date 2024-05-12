open HolKernel boolLib Parse bossLib;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_riscv_extrasTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open tutorial_smtSupportLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;
open bir_symbLib;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open birs_stepLib;

open swapTheory;

open swap_symb_execTheory;

open distribute_generic_stuffTheory;

val _ = new_theory "swap_prop";

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_dword (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_dword (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_swap_pre_def:
 riscv_swap_pre x y xv yv (m : riscv_state) =
  (m.c_gpr m.procID 10w = x /\
   riscv_mem_load_dword m.MEM8 x = xv /\
   m.c_gpr m.procID 11w = y /\
   riscv_mem_load_dword m.MEM8 y = yv)
End

Definition riscv_swap_post_def:
 riscv_swap_post x y xv yv (m : riscv_state) =
  (riscv_mem_load_dword m.MEM8 x = yv /\
   riscv_mem_load_dword m.MEM8 y = xv)
End

val bir_swap_pre_tm = bslSyntax.bandl [
 mem_addrs_aligned_prog_disj_tm "x10",
 mem_addrs_aligned_prog_disj_tm "x11",
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))``,
 ``BExp_BinPred
      BIExp_Equal
      (BExp_Load
       (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
       (BExp_Den (BVar "x10" (BType_Imm Bit64)))
       BEnd_LittleEndian Bit64)
      (BExp_Const (Imm64 xv))``,
 ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x11" (BType_Imm Bit64)))
     (BExp_Const (Imm64 y))``,
 ``BExp_BinPred
    BIExp_Equal
     (BExp_Load
      (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
      (BExp_Den (BVar "x11" (BType_Imm Bit64)))
      BEnd_LittleEndian Bit64)
     (BExp_Const (Imm64 yv))`` 
];

Definition bir_swap_pre_def:
  bir_swap_pre x y xv yv : bir_exp_t =
   ^bir_swap_pre_tm
End

Definition bir_swap_post_def:
 bir_swap_post x y xv yv : bir_exp_t = 
  BExp_BinExp BIExp_And
   (BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 x))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 yv)))
   (BExp_BinPred
    BIExp_Equal
    (BExp_Load
     (BExp_Den (BVar "MEM8" (BType_Mem Bit64 Bit8)))
     (BExp_Const (Imm64 y))
     BEnd_LittleEndian Bit64)
    (BExp_Const (Imm64 xv)))
End

val bir_swap_pre = ``bir_swap_pre``;
val bir_swap_post = ``bir_swap_post``;

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem swap_riscv_pre_imp_bir_pre_thm[local]:
 bir_pre_riscv_to_bir
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
  (bir_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
Proof
 cheat
QED

Theorem swap_riscv_post_imp_bir_post_thm[local]:
 !ls. bir_post_bir_to_riscv
   (riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
   (\l. (bir_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref))
   ls
Proof
 rw [bir_post_bir_to_riscv_def,riscv_swap_post_def,bir_swap_post_def,riscv_mem_load_dword_def] >>
 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def] >>
 cheat
QED

(* ------------------------------- *)
(* BIR symbolic execution analysis *)
(* ------------------------------- *)

val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) swap_symb_analysis_thm;

Definition swap_analysis_L_def:
 swap_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0x00w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x14w))``;

Theorem swap_analysis_L_NOTIN_thm[local]:
  (^birs_state_end_lbl) NOTIN swap_analysis_L
Proof
  EVAL_TAC
QED

(* ........................... *)
(* ........................... *)
(* ........................... *)

val birs_state_init_pre = ``birs_state_init_pre_GEN ^birs_state_init_lbl swap_birenvtyl
 (mk_bsysprecond (bir_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref) swap_birenvtyl)``;

val swap_bsysprecond_thm = (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
 ``mk_bsysprecond (bir_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref) swap_birenvtyl``;

(*
Theorem birs_state_init_pre_EQ_thm:
  ^((snd o dest_comb) sys_i) = ^birs_state_init_pre
Proof
  REWRITE_TAC [birs_state_init_pre_GEN_def, mk_bsysprecond_def, swap_bsysprecond_thm] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_eval_exp``] THENC birs_stepLib.birs_eval_exp_CONV)
QED

val swap_analysis_thm =
  REWRITE_RULE [birs_state_init_pre_EQ_thm, GSYM bir_swap_prog_def] swap_symb_analysis_thm;
*)

Theorem bir_cont_swap:
 bir_cont bir_swap_prog bir_exp_true (BL_Address (Imm64 0x00w))
  {BL_Address (Imm64 0x14w)} {}
  (bir_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
  (\l. if l = BL_Address (Imm64 0x14w)
       then (bir_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
       else bir_exp_false)
Proof
 cheat
QED

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

(* For debugging:
val bir_ct = bir_cont_swap;
val prog_bin = ``bir_swap_progbin``;
val riscv_pre = ``riscv_swap_pre``;
val riscv_post = ``riscv_swap_post``;
val bir_prog_def = bir_swap_prog_def;
val bir_pre_defs = [bir_swap_pre_def]
val bir_pre1_def = bir_swap_pre_def;
val riscv_pre_imp_bir_pre_thm = swap_riscv_pre_imp_bir_pre_thm;
val bir_post_defs = [bir_swap_post_def];
val riscv_post_imp_bir_post_thm = swap_riscv_post_imp_bir_post_thm;
val bir_is_lifted_prog_thm = bir_swap_riscv_lift_THM;
*)

val riscv_cont_swap_thm =
 get_riscv_contract_sing
  bir_cont_swap
  ``bir_swap_progbin``
  ``riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref``
  ``riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref``
  bir_swap_prog_def
  [bir_swap_pre_def]
  bir_swap_pre_def swap_riscv_pre_imp_bir_pre_thm
  [bir_swap_post_def] swap_riscv_post_imp_bir_post_thm
  bir_swap_riscv_lift_THM;

Theorem riscv_cont_swap:
 riscv_cont bir_swap_progbin 0w {0x14w}
  (riscv_swap_pre pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
  (riscv_swap_post pre_x10 pre_x11 pre_x10_mem_deref pre_x11_mem_deref)
Proof
 ACCEPT_TAC riscv_cont_swap_thm
QED

val _ = export_theory ();
