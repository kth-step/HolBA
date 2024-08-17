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

open tutorial_smtSupportLib;
open birs_smtLib;

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

open logrootTheory arithmeticTheory pairTheory combinTheory;

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
 isqrt_init_addr : word64 = 0x10488w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x104a0w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x10488w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x10490w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x10490w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x1049cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x1049cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x10490w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x104a0w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* general contract *)

Definition riscv_isqrt_pre_def:
 riscv_isqrt_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_isqrt_post_def:
 riscv_isqrt_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = n2w (nSQRT (w2n pre_x10)))
End

(* before loop contract *)

Definition riscv_isqrt_pre_1_def:
 riscv_isqrt_pre_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

Definition riscv_isqrt_post_1_def:
 riscv_isqrt_post_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x10 /\
   m.c_gpr m.procID 15w = 0w)
End

(* loop body contract *)

Definition riscv_isqrt_pre_2_def:
 riscv_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 15w = pre_x15)
End

Definition riscv_isqrt_post_2_def:
 riscv_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x15 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = (pre_x15 + 1w) * (pre_x15 + 1w) /\
   m.c_gpr m.procID 15w = pre_x15 + 1w)
End

(* loop branch contract *)

Definition riscv_isqrt_pre_3_def:
 riscv_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14)
End

Definition riscv_isqrt_post_3_loop_def:
 riscv_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x14 <= pre_x13)
End

Definition riscv_isqrt_post_3_ret_def:
 riscv_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   pre_x13 < pre_x14)
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

(* before loop contract *)

Definition bspec_isqrt_pre_1_def:
 bspec_isqrt_pre_1 (pre_x10:word64) : bir_exp_t =
  BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))
End

val bspec_isqrt_post_1_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 0w))``
];

Definition bspec_isqrt_post_1_def:
 bspec_isqrt_post_1 (pre_x10:word64) : bir_exp_t =
  ^bspec_isqrt_post_1_tm
End

(* loop body contract *)

val bspec_isqrt_pre_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))``
];

Definition bspec_isqrt_pre_2_def:
 bspec_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_pre_2_tm
End

val bspec_isqrt_post_2_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
     BIExp_Equal
     (BExp_Den (BVar "x14" (BType_Imm Bit64)))
     (BExp_BinExp
       BIExp_Mult
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w)))
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w))))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_BinExp
      BIExp_Plus (BExp_Const (Imm64 pre_x15)) (BExp_Const (Imm64 1w)))``
];

Definition bspec_isqrt_post_2_def:
 bspec_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) : bir_exp_t =
  ^bspec_isqrt_post_2_tm
End

(* branch contract *)

val bspec_isqrt_pre_3_tm = bslSyntax.bandl [
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
 ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``
];

Definition bspec_isqrt_pre_3_def:
 bspec_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
  ^bspec_isqrt_pre_3_tm
End

val bspec_isqrt_post_3_loop_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``,
  ``BExp_BinPred
     BIExp_LessOrEqual
      (BExp_Const (Imm64 pre_x14))
      (BExp_Const (Imm64 pre_x13))``
];

Definition bspec_isqrt_post_3_loop_def:
 bspec_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_loop_tm
End

val bspec_isqrt_post_3_ret_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x13" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x14" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x14))``,
  ``BExp_BinPred
    BIExp_LessThan
    (BExp_Const (Imm64 pre_x13))
    (BExp_Const (Imm64 pre_x14))``
];

Definition bspec_isqrt_post_3_ret_def:
 bspec_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64) (pre_x14:word64) : bir_exp_t =
  ^bspec_isqrt_post_3_ret_tm
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem isqrt_riscv_pre_1_imp_bspec_pre_1_thm:
 bir_pre_riscv_to_bir
  (riscv_isqrt_pre_1 pre_x10)
  (bspec_isqrt_pre_1 pre_x10)
Proof
 rw [bir_pre_riscv_to_bir_def,riscv_isqrt_pre_1_def,bspec_isqrt_pre_1_def] >-
  (rw [bir_is_bool_exp_REWRS,bir_is_bool_exp_env_REWRS] >>
   FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_typing_expTheory.type_of_bir_exp_def]) >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [riscv_bmr_rel_EVAL,bir_val_TF_bool2b_DEF]
QED

Theorem isqrt_riscv_post_1_imp_bspec_post_1_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_isqrt_post_1 pre_x10)
   (\l. bspec_isqrt_post_1 pre_x10)
   ls
Proof
 cheat
QED

val _ = export_theory ();
