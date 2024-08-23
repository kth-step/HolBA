open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

val _ = new_theory "chacha_spec";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* ivsetup *)

Definition chacha_ivsetup_init_addr_def:
 chacha_ivsetup_init_addr : word64 = 0x106bcw
End

Definition chacha_ivsetup_end_addr_def:
 chacha_ivsetup_end_addr : word64 = 0x10778w
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

Definition bspec_chacha_ivsetup_pre_def:
 bspec_chacha_ivsetup_pre (pre_x15:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))
End

val _ = export_theory ();
