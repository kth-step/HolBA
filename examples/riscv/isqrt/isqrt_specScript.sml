open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open tutorial_smtSupportLib;
open birs_smtLib;

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

open bir_env_oldTheory;
open bir_program_varsTheory;

open distribute_generic_stuffTheory;

open logrootTheory arithmeticTheory pairTheory combinTheory;

open isqrtTheory;

val _ = new_theory "isqrt_spec";

(* ------ *)
(* Theory *)
(* ------ *)

Definition nSQRT_def:
 nSQRT (x:num) = ROOT 2 x
End

val arith_ss = srw_ss() ++ numSimps.old_ARITH_ss;

Theorem nSQRT_thm:
!(x:num) (p:num). nSQRT x =
      let 
        q = p * p
      in
      if (q <= x /\ x < q + 2 * p + 1) then p else nSQRT x
Proof
 RW_TAC (arith_ss ++ boolSimps.LET_ss) [nSQRT_def] >>
 MATCH_MP_TAC ROOT_UNIQUE >>
 RW_TAC bool_ss [ADD1,EXP_ADD,EXP_1,DECIDE ``2 = SUC 1``,
     LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
 fs []
QED

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x00w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x04w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x00w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x04w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x08w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x10w
End

(* branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x14w
End

Definition isqrt_end_addr_3_def:
 isqrt_end_addr_3 : word64 = 0x18w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* general contract *)

Definition riscv_isqrt_pre_def:
 riscv_isqrt_pre (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_isqrt_post_def:
 riscv_isqrt_post (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w (nSQRT (w2n x)))
End

(* before loop contract *)

Definition riscv_isqrt_pre_1_def:
 riscv_isqrt_pre_1 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_isqrt_post_1_def:
 riscv_isqrt_post_1 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = x /\ m.c_gpr m.procID 15w = 0w)
End

(* loop body contract *)

Definition riscv_isqrt_pre_2_def:
 riscv_isqrt_pre_2 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_isqrt_post_2_def:
 riscv_isqrt_post_2 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = x /\ m.c_gpr m.procID 15w = 0w)
End

(* branch contract *)

Definition riscv_isqrt_pre_3_def:
 riscv_isqrt_pre_3 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = x)
End

Definition riscv_isqrt_post_3_def:
 riscv_isqrt_post_3 (x:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w (nSQRT (w2n x)))
End

(* --------------- *)
(* HL BIR contract *)
(* --------------- *)

Definition bir_isqrt_pre_def:
 bir_isqrt_pre (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 x))
End

Definition bir_isqrt_post_def:
 bir_isqrt_post (x:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 (n2w (nSQRT (w2n x)))))
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* -------------------------------------- *)
(* Connecting RISC-V and HL BIR contracts *)
(* -------------------------------------- *)

Theorem isqrt_riscv_pre_imp_bir_pre_thm[local]:
 bir_pre_riscv_to_bir (riscv_isqrt_pre pre_x10) (bir_isqrt_pre pre_x10)
Proof
 cheat
QED

Theorem isqrt_riscv_post_imp_bir_post_thm[local]:
 !ls. bir_post_bir_to_riscv (riscv_isqrt_post pre_x10) (\l. bir_isqrt_post pre_x10) ls
Proof
 cheat
QED

val _ = export_theory ();
