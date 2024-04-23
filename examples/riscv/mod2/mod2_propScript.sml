open HolKernel boolLib Parse bossLib;

open numTheory arithmeticTheory int_bitwiseTheory;
open pairTheory combinTheory wordsTheory;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open tutorial_smtSupportLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open mod2Theory;

val _ = new_theory "mod2_prop";

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_mod2_pre_def:
 riscv_mod2_pre x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w x)
End

Definition riscv_mod2_post_def:
 riscv_mod2_post x (m : riscv_state) =
  (m.c_gpr m.procID 10w = n2w (x MOD 2))
End

(* ------------ *)
(* BIR contract *)
(* ------------ *)

Definition bir_mod2_pre_def:
  bir_mod2_pre x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w x)))
End

Definition bir_mod2_post_def:
 bir_mod2_post x : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w (x MOD 2))))
End

(* ----------------------------------- *)
(* Connecting RISC-V and BIR contracts *)
(* ----------------------------------- *)

Theorem mod2_riscv_pre_imp_bir_pre_thm[local]:
 bir_pre_riscv_to_bir (riscv_mod2_pre input) (bir_mod2_pre input)
Proof
 cheat
QED

Theorem mod2_riscv_post_imp_bir_post_thm[local]:
 !ls. bir_post_bir_to_riscv (riscv_mod2_post pre_x10) (\l. bir_mod2_post pre_x10) ls
Proof
 cheat
QED

val _ = export_theory ();
