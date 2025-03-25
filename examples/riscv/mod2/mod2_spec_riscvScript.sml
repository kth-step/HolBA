open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_exp_tautologiesTheory;

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

val _ = new_theory "mod2_spec_riscv";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition mod2_init_addr_def:
 mod2_init_addr : word64 = 0x10488w
End

Definition mod2_end_addr_def:
 mod2_end_addr : word64 = 0x1048cw
End

(* --------------- *)
(* RISC-V contract *)
(* --------------- *)

Definition riscv_mod2_pre_def:
 riscv_mod2_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_mod2_post_def:
 riscv_mod2_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w ((w2n pre_x10) MOD 2))
End

val _ = export_theory ();
