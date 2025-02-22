open HolKernel boolLib Parse bossLib;
open pairTheory pred_setTheory markerTheory wordsTheory wordsLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_extra_expsTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;
open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open chachaTheory;

val _ = new_theory "chacha20_spec_riscv";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

(* keysetup *)

Definition chacha20_keysetup_init_addr_def:
 chacha20_keysetup_init_addr : word64 = 0x10488w
End

Definition chacha20_keysetup_end_addr_def:
 chacha20_keysetup_end_addr : word64 = (*0x106a8w*) 0x1053cw
End

(* ivsetup *)

Definition chacha20_ivsetup_init_addr_def:
 chacha20_ivsetup_init_addr : word64 = 0x106bcw
End

Definition chacha20_ivsetup_end_addr_def:
 chacha20_ivsetup_end_addr : word64 = 0x10778w
End

(* first line *)

Definition chacha20_line_init_addr_def:
  chacha20_line_init_addr : word64 = 0x108a0w
End

Definition chacha20_line_end_addr_def:
 chacha20_line_end_addr : word64 = 0x108b4w
End

(* second line *)

Definition chacha20_other_line_init_addr_def:
  chacha20_other_line_init_addr : word64 = 0x108b4w
End

Definition chacha20_other_line_end_addr_def:
 chacha20_other_line_end_addr : word64 = 0x108c8w
End

(* first quarter round *)

Definition chacha20_quarter_round_init_addr_def:
  chacha20_quarter_round_init_addr : word64 = 0x108a0w
End

Definition chacha20_quarter_round_end_addr_def:
  chacha20_quarter_round_end_addr : word64 = 0x108f0w
End

(* column round *)

Definition chacha20_column_round_init_addr_def:
  chacha20_column_round_init_addr : word64 = 0x108a0w
End

Definition chacha20_column_round_end_addr_def:
  chacha20_column_round_end_addr : word64 = 0x109e0w
End

(* diagonal round *)

Definition chacha20_diagonal_round_init_addr_def:
  chacha20_diagonal_round_init_addr : word64 = 0x109e0w
End

Definition chacha20_diagonal_round_end_addr_def:
  chacha20_diagonal_round_end_addr : word64 = 0x10b64w
End

(* double round loop body *)

Definition chacha20_double_round_init_addr_def:
  chacha20_double_round_init_addr : word64 = 0x108a0w
End

Definition chacha20_double_round_end_addr_def:
  chacha20_double_round_end_addr : word64 = 0x10b64w
End

(* double round loop branch *)

Definition chacha20_double_round_branch_init_addr_def:
  chacha20_double_round_branch_init_addr : word64 = 0x10b64w
End

Definition chacha20_double_round_branch_end_addr_loop_def:
  chacha20_double_round_branch_end_addr_loop : word64 = 0x108a0w
End

Definition chacha20_double_round_branch_end_addr_continue_def:
  chacha20_double_round_branch_end_addr_continue : word64 = 0x10b68w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* single line contract *)

Definition riscv_chacha20_line_pre_def:
 riscv_chacha20_line_pre (pre_a:word32) (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 10w)) = pre_a /\
  n2w (w2n (m.c_gpr m.procID 22w)) = pre_b /\
  n2w (w2n (m.c_gpr m.procID 26w)) = pre_d)
End

Definition riscv_chacha20_line_post_def:
 riscv_chacha20_line_post (pre_a:word32) (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 20w)) =
   chacha_line_exp_fst pre_a pre_b /\
  n2w (w2n (m.c_gpr m.procID 10w)) =
   chacha_line_exp_snd (chacha_line_exp_fst pre_a pre_b) pre_d 16w)
End

(* single quarter round contract *)

Definition riscv_chacha20_quarter_round_pre_def:
 riscv_chacha20_quarter_round_pre (pre_a:word32) (pre_b:word32) (pre_c:word32) (pre_d:word32)
  (m:riscv_state) : bool =
  (n2w (w2n (m.c_gpr m.procID 10w)) = pre_a /\
   n2w (w2n (m.c_gpr m.procID 22w)) = pre_b /\
   n2w (w2n (m.c_gpr m.procID 28w)) = pre_c /\
   n2w (w2n (m.c_gpr m.procID 26w)) = pre_d)
End

Definition riscv_chacha20_quarter_round_post_def:
 riscv_chacha20_quarter_round_post (pre_a:word32) (pre_b:word32) (pre_c:word32) (pre_d:word32)
  (m:riscv_state) : bool =
  (let (a,b,c,d) = chacha_quarter_round_exprs pre_a pre_b pre_c pre_d in
   n2w (w2n (m.c_gpr m.procID 20w)) = a /\
   n2w (w2n (m.c_gpr m.procID 21w)) = b /\
   n2w (w2n (m.c_gpr m.procID 8w)) = c /\
   n2w (w2n (m.c_gpr m.procID 22w)) = d)
End

(* column round contract *)

Definition riscv_chacha20_column_round_pre_def:
 riscv_chacha20_column_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 10w)) = pre_arr_0 /\
  n2w (w2n (m.c_gpr m.procID 16w)) = pre_arr_1 /\
  n2w (w2n (m.c_gpr m.procID 17w)) = pre_arr_2 /\
  n2w (w2n (m.c_gpr m.procID 6w))  = pre_arr_3 /\
  n2w (w2n (m.c_gpr m.procID 22w)) = pre_arr_4 /\
  n2w (w2n (m.c_gpr m.procID 11w)) = pre_arr_5 /\
  n2w (w2n (m.c_gpr m.procID 13w)) = pre_arr_6 /\
  n2w (w2n (m.c_gpr m.procID 14w)) = pre_arr_7 /\
  n2w (w2n (m.c_gpr m.procID 28w)) = pre_arr_8 /\
  n2w (w2n (m.c_gpr m.procID 29w)) = pre_arr_9 /\
  n2w (w2n (m.c_gpr m.procID 30w)) = pre_arr_10 /\
  n2w (w2n (m.c_gpr m.procID 31w)) = pre_arr_11 /\
  n2w (w2n (m.c_gpr m.procID 26w)) = pre_arr_12 /\
  n2w (w2n (m.c_gpr m.procID 25w)) = pre_arr_13 /\
  n2w (w2n (m.c_gpr m.procID 24w)) = pre_arr_14 /\
  n2w (w2n (m.c_gpr m.procID 23w)) = pre_arr_15)
End

Definition riscv_chacha20_column_round_post_def:
 riscv_chacha20_column_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,arr_8,
       arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15) =
   chacha_column_round_exprs
     pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
     pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
  in
  n2w (w2n (m.c_gpr m.procID 20w)) = arr_0 /\
  n2w (w2n (m.c_gpr m.procID 19w)) = arr_1 /\
  n2w (w2n (m.c_gpr m.procID 18w)) = arr_2 /\
  n2w (w2n (m.c_gpr m.procID 9w)) = arr_3 /\
  n2w (w2n (m.c_gpr m.procID 21w)) = arr_4 /\
  n2w (w2n (m.c_gpr m.procID 10w)) = arr_5 /\
  n2w (w2n (m.c_gpr m.procID 13w)) = arr_6 /\
  n2w (w2n (m.c_gpr m.procID 14w)) = arr_7 /\
  n2w (w2n (m.c_gpr m.procID 8w)) = arr_8 /\
  n2w (w2n (m.c_gpr m.procID 7w)) = arr_9 /\
  n2w (w2n (m.c_gpr m.procID 5w)) = arr_10 /\
  n2w (w2n (m.c_gpr m.procID 15w)) = arr_11 /\
  n2w (w2n (m.c_gpr m.procID 22w)) = arr_12 /\
  n2w (w2n (m.c_gpr m.procID 28w)) = arr_13 /\
  n2w (w2n (m.c_gpr m.procID 29w)) = arr_14 /\
  n2w (w2n (m.c_gpr m.procID 16w)) = arr_15)
End

(* diagonal round contract *)

Definition riscv_chacha20_diagonal_round_pre_def:
 riscv_chacha20_diagonal_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 20w)) = pre_arr_0 /\
  n2w (w2n (m.c_gpr m.procID 19w)) = pre_arr_1 /\
  n2w (w2n (m.c_gpr m.procID 18w)) = pre_arr_2 /\
  n2w (w2n (m.c_gpr m.procID 9w)) = pre_arr_3 /\
  n2w (w2n (m.c_gpr m.procID 21w)) = pre_arr_4 /\
  n2w (w2n (m.c_gpr m.procID 10w)) = pre_arr_5 /\
  n2w (w2n (m.c_gpr m.procID 13w)) = pre_arr_6 /\
  n2w (w2n (m.c_gpr m.procID 14w)) = pre_arr_7 /\
  n2w (w2n (m.c_gpr m.procID 8w)) = pre_arr_8 /\
  n2w (w2n (m.c_gpr m.procID 7w)) = pre_arr_9 /\
  n2w (w2n (m.c_gpr m.procID 5w)) = pre_arr_10 /\
  n2w (w2n (m.c_gpr m.procID 15w)) = pre_arr_11 /\
  n2w (w2n (m.c_gpr m.procID 22w)) = pre_arr_12 /\
  n2w (w2n (m.c_gpr m.procID 28w)) = pre_arr_13 /\
  n2w (w2n (m.c_gpr m.procID 29w)) = pre_arr_14 /\
  n2w (w2n (m.c_gpr m.procID 16w)) = pre_arr_15)
End

Definition riscv_chacha20_diagonal_round_post_def:
 riscv_chacha20_diagonal_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,arr_8,
       arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15) =
   chacha_diagonal_round_exprs
     pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
     pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
  in
  n2w (w2n (m.c_gpr m.procID 10w)) = arr_0 /\
  n2w (w2n (m.c_gpr m.procID 16w)) = arr_1 /\
  n2w (w2n (m.c_gpr m.procID 17w)) = arr_2 /\
  n2w (w2n (m.c_gpr m.procID 6w)) = arr_3 /\
  n2w (w2n (m.c_gpr m.procID 22w)) = arr_4 /\
  n2w (w2n (m.c_gpr m.procID 11w)) = arr_5 /\
  n2w (w2n (m.c_gpr m.procID 13w)) = arr_6 /\
  n2w (w2n (m.c_gpr m.procID 14w)) = arr_7 /\
  n2w (w2n (m.c_gpr m.procID 28w)) = arr_8 /\
  n2w (w2n (m.c_gpr m.procID 29w)) = arr_9 /\
  n2w (w2n (m.c_gpr m.procID 30w)) = arr_10 /\
  n2w (w2n (m.c_gpr m.procID 31w)) = arr_11 /\
  n2w (w2n (m.c_gpr m.procID 26w)) = arr_12 /\
  n2w (w2n (m.c_gpr m.procID 25w)) = arr_13 /\
  n2w (w2n (m.c_gpr m.procID 24w)) = arr_14 /\
  n2w (w2n (m.c_gpr m.procID 23w)) = arr_15)
End

val _ = export_theory ();
