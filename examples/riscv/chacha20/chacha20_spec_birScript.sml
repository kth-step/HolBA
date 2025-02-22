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
open chacha20_spec_riscvTheory;

val _ = new_theory "chacha20_spec_bir";

(* ----------------- *)
(* BIR specification *)
(* ----------------- *)

Definition bir_var_equal_32_lowcast_64_def:
 bir_var_equal_32_lowcast_64 var exp =
  BExp_BinPred
   BIExp_Equal
   (BExp_Cast BIExp_LowCast (BExp_Den (BVar var (BType_Imm Bit64))) Bit32)
   exp
End

(* a =+ (m a) + (m b) *)
Definition chacha_line_bir_exp_fst_def:
 chacha_line_bir_exp_fst pre_a_exp pre_b_exp : bir_exp_t =
  BExp_BinExp BIExp_Plus pre_a_exp pre_b_exp
End

(* d =+ (((m d) ?? (m a)) <<~ s) || (((m d) ?? (m a)) >>>~ (32w - s)) *)
Definition chacha_line_bir_exp_snd_def:
 chacha_line_bir_exp_snd pre_a_exp pre_d_exp (s:word32) : bir_exp_t =
   BExp_BinExp BIExp_Or
     (BExp_BinExp BIExp_LeftShift 
      (BExp_BinExp BIExp_Xor pre_a_exp pre_d_exp)
     (BExp_Const (Imm32 s)))
     (BExp_BinExp BIExp_RightShift
      (BExp_BinExp BIExp_Xor pre_a_exp pre_d_exp)
      (BExp_Const (Imm32 (32w-s))))
End

Definition chacha_quarter_round_bir_exprs_def:
 chacha_quarter_round_bir_exprs pre_a_exp pre_b_exp pre_c_exp pre_d_exp
  : bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t =
  let a = pre_a_exp in
  let b = pre_b_exp in
  let c = pre_c_exp in
  let d = pre_d_exp in

  let a = chacha_line_bir_exp_fst a b in
  let d = chacha_line_bir_exp_snd a d 16w in

  let c = chacha_line_bir_exp_fst c d in
  let b = chacha_line_bir_exp_snd c b 12w in
    
  let a = chacha_line_bir_exp_fst a b in
  let d = chacha_line_bir_exp_snd a d 8w in

  let c = chacha_line_bir_exp_fst c d in
  let b = chacha_line_bir_exp_snd c b 7w in

  (a,b,c,d)
End

Definition chacha_column_round_bir_exprs_def:
 chacha_column_round_bir_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t
  =
 let (arr_0,arr_4,arr_8,arr_12) =
   chacha_quarter_round_bir_exprs pre_arr_0 pre_arr_4 pre_arr_8 pre_arr_12
 in
 let (arr_1,arr_5,arr_9,arr_13) =
   chacha_quarter_round_bir_exprs pre_arr_1 pre_arr_5 pre_arr_9 pre_arr_13
 in
 let (arr_2,arr_6,arr_10,arr_14) =
   chacha_quarter_round_bir_exprs pre_arr_2 pre_arr_6 pre_arr_10 pre_arr_14
 in
 let (arr_3,arr_7,arr_11,arr_15) =
   chacha_quarter_round_bir_exprs pre_arr_3 pre_arr_7 pre_arr_11 pre_arr_15
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition chacha_diagonal_round_bir_exprs_def:
 chacha_diagonal_round_bir_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t
  =
 let (arr_0,arr_5,arr_10,arr_15) =
   chacha_quarter_round_bir_exprs pre_arr_0 pre_arr_5 pre_arr_10 pre_arr_15
 in
 let (arr_1,arr_6,arr_11,arr_12) =
   chacha_quarter_round_bir_exprs pre_arr_1 pre_arr_6 pre_arr_11 pre_arr_12
 in
 let (arr_2,arr_7,arr_8,arr_13) =
   chacha_quarter_round_bir_exprs pre_arr_2 pre_arr_7 pre_arr_8 pre_arr_13
 in
 let (arr_3,arr_4,arr_9,arr_14) =
   chacha_quarter_round_bir_exprs pre_arr_3 pre_arr_4 pre_arr_9 pre_arr_14
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition chacha_double_round_bir_exprs_def:
 chacha_double_round_bir_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t #
   bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t
  =
  let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
       arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15) =
   chacha_column_round_bir_exprs
    pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
    pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
    pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
    pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
  in

  let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
       arr_8,arr_9,arr_10,arr_11, arr_12,arr_13,arr_14,arr_15) =
   chacha_diagonal_round_bir_exprs
    arr_0 arr_1 arr_2 arr_3 arr_4 arr_5 arr_6 arr_7
    arr_8 arr_9 arr_10 arr_11 arr_12 arr_13 arr_14 arr_15
  in

  (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
   arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* keysetup *)

val bspec_chacha20_keysetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha20_keysetup_pre_def:
 bspec_chacha20_keysetup_pre : bir_exp_t =
  ^bspec_chacha20_keysetup_pre_tm
End

(* ivsetup *)

val bspec_chacha20_ivsetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha20_ivsetup_pre_def:
 bspec_chacha20_ivsetup_pre : bir_exp_t =
  ^bspec_chacha20_ivsetup_pre_tm
End

(* first line *)

val bspec_chacha20_line_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_a))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_b))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_d))``  
];

Definition bspec_chacha20_line_pre_def:
 bspec_chacha20_line_pre (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_line_pre_tm
End

val bspec_chacha20_line_post_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bir_var_equal_32_lowcast_64 "x20"
    (chacha_line_bir_exp_fst
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))``),
  (snd o dest_eq o concl)
   (EVAL ``bir_var_equal_32_lowcast_64 "x10"
    (chacha_line_bir_exp_snd
     (chacha_line_bir_exp_fst (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))
     (BExp_Const (Imm32 pre_d)) 16w)``)
];

Definition bspec_chacha20_line_post_def:
 bspec_chacha20_line_post (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_line_post_tm
End

(* second line *)

val bspec_chacha20_line_pre_other_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_b))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_d))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x28" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_a))``  
];

Definition bspec_chacha20_line_pre_other_def:
 bspec_chacha20_line_pre_other (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_line_pre_other_tm
End

val bspec_chacha20_line_post_other_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bir_var_equal_32_lowcast_64 "x8"
    (chacha_line_bir_exp_fst
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))``),
  (snd o dest_eq o concl)
   (EVAL ``bir_var_equal_32_lowcast_64 "x15"
    (chacha_line_bir_exp_snd
     (chacha_line_bir_exp_fst (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))
     (BExp_Const (Imm32 pre_d)) 12w)``)
];

Definition bspec_chacha20_line_post_other_def:
 bspec_chacha20_line_post_other (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_line_post_other_tm
End

(* first quarter round *)

val bspec_chacha20_quarter_round_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_a))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_b))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x28" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_c))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_d))``  
];

Definition bspec_chacha20_quarter_round_pre_def:
 bspec_chacha20_quarter_round_pre (pre_a:word32) (pre_b:word32)
 (pre_c:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_quarter_round_pre_tm
End

val bspec_chacha20_quarter_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``chacha_quarter_round_bir_exprs 
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b))
     (BExp_Const (Imm32 pre_c)) (BExp_Const (Imm32 pre_d))``);
   val (a_exp, bir_exprs) = dest_pair bir_exprs;
   val (b_exp, bir_exprs) = dest_pair bir_exprs;
   val (c_exp, d_exp) = dest_pair bir_exprs;
 in
   bslSyntax.bandl [
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x20" ^a_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x21" ^b_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x8" ^c_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x22" ^d_exp``)
   ]
 end;

Definition bspec_chacha20_quarter_round_post_def:
 bspec_chacha20_quarter_round_post (pre_a:word32) (pre_b:word32)
  (pre_c:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha20_quarter_round_post_tm
End

(* column round *)

val bspec_chacha20_column_round_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_0))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x16" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x17" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_2))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x6" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_3))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_4))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x11" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_5))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x13" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_6))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x14" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_7))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x28" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_8))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x29" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_9))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x30" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x31" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_11))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_12))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x25" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x24" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_14))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x23" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_15))``
];

Definition bspec_chacha20_column_round_pre_def:
 bspec_chacha20_column_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha20_column_round_pre_tm
End

val bspec_chacha20_column_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``chacha_column_round_bir_exprs 
     (BExp_Const (Imm32 pre_arr_0))
     (BExp_Const (Imm32 pre_arr_1))
     (BExp_Const (Imm32 pre_arr_2))
     (BExp_Const (Imm32 pre_arr_3))
     (BExp_Const (Imm32 pre_arr_4))
     (BExp_Const (Imm32 pre_arr_5))
     (BExp_Const (Imm32 pre_arr_6))
     (BExp_Const (Imm32 pre_arr_7))
     (BExp_Const (Imm32 pre_arr_8))
     (BExp_Const (Imm32 pre_arr_9))
     (BExp_Const (Imm32 pre_arr_10))
     (BExp_Const (Imm32 pre_arr_11))
     (BExp_Const (Imm32 pre_arr_12))
     (BExp_Const (Imm32 pre_arr_13))
     (BExp_Const (Imm32 pre_arr_14))
     (BExp_Const (Imm32 pre_arr_15))``);
   val (arr_0_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_1_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_2_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_3_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_4_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_5_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_6_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_7_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_8_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_9_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_10_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_11_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_12_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_13_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_14_exp, arr_15_exp) = dest_pair bir_exprs;
 in
   bslSyntax.bandl [
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x20" ^arr_0_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x19" ^arr_1_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x18" ^arr_2_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x9" ^arr_3_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x21" ^arr_4_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x10" ^arr_5_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x13" ^arr_6_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x14" ^arr_7_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x8" ^arr_8_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x7" ^arr_9_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x5" ^arr_10_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x15" ^arr_11_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x22" ^arr_12_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x28" ^arr_13_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x29" ^arr_14_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x16" ^arr_15_exp``)
   ]
 end;

Definition bspec_chacha20_column_round_post_def:
 bspec_chacha20_column_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha20_column_round_post_tm
End

(* diagonal round *)

val bspec_chacha20_diagonal_round_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x20" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_0))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x19" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x18" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_2))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x9" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_3))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x21" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_4))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_5))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x13" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_6))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x14" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_7))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x8" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_8))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x7" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_9))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x5" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x15" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_11))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_12))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x28" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x29" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_14))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x16" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_15))``
];

Definition bspec_chacha20_diagonal_round_pre_def:
 bspec_chacha20_diagonal_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha20_diagonal_round_pre_tm
End

val bspec_chacha20_diagonal_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``chacha_diagonal_round_bir_exprs 
     (BExp_Const (Imm32 pre_arr_0))
     (BExp_Const (Imm32 pre_arr_1))
     (BExp_Const (Imm32 pre_arr_2))
     (BExp_Const (Imm32 pre_arr_3))
     (BExp_Const (Imm32 pre_arr_4))
     (BExp_Const (Imm32 pre_arr_5))
     (BExp_Const (Imm32 pre_arr_6))
     (BExp_Const (Imm32 pre_arr_7))
     (BExp_Const (Imm32 pre_arr_8))
     (BExp_Const (Imm32 pre_arr_9))
     (BExp_Const (Imm32 pre_arr_10))
     (BExp_Const (Imm32 pre_arr_11))
     (BExp_Const (Imm32 pre_arr_12))
     (BExp_Const (Imm32 pre_arr_13))
     (BExp_Const (Imm32 pre_arr_14))
     (BExp_Const (Imm32 pre_arr_15))``);
   val (arr_0_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_1_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_2_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_3_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_4_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_5_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_6_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_7_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_8_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_9_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_10_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_11_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_12_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_13_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_14_exp, arr_15_exp) = dest_pair bir_exprs;
 in
   bslSyntax.bandl [
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x10" ^arr_0_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x16" ^arr_1_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x17" ^arr_2_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x6" ^arr_3_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x22" ^arr_4_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x11" ^arr_5_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x13" ^arr_6_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x14" ^arr_7_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x28" ^arr_8_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x29" ^arr_9_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x30" ^arr_10_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x31" ^arr_11_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x26" ^arr_12_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x25" ^arr_13_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x24" ^arr_14_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x23" ^arr_15_exp``)
   ]
 end;

Definition bspec_chacha20_diagonal_round_post_def:
 bspec_chacha20_diagonal_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha20_diagonal_round_post_tm
End

(* double round *)

val bspec_chacha20_double_round_pre_tm = bslSyntax.bandl [
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_0))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x16" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_1))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x17" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_2))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x6" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_3))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_4))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x11" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_5))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x13" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_6))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x14" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_7))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x28" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_8))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x29" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_9))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x30" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x31" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_11))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_12))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x25" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_13))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x24" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_14))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x23" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_arr_15))``
];

Definition bspec_chacha20_double_round_pre_def:
 bspec_chacha20_double_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha20_double_round_pre_tm
End

val bspec_chacha20_double_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``chacha_double_round_bir_exprs 
     (BExp_Const (Imm32 pre_arr_0))
     (BExp_Const (Imm32 pre_arr_1))
     (BExp_Const (Imm32 pre_arr_2))
     (BExp_Const (Imm32 pre_arr_3))
     (BExp_Const (Imm32 pre_arr_4))
     (BExp_Const (Imm32 pre_arr_5))
     (BExp_Const (Imm32 pre_arr_6))
     (BExp_Const (Imm32 pre_arr_7))
     (BExp_Const (Imm32 pre_arr_8))
     (BExp_Const (Imm32 pre_arr_9))
     (BExp_Const (Imm32 pre_arr_10))
     (BExp_Const (Imm32 pre_arr_11))
     (BExp_Const (Imm32 pre_arr_12))
     (BExp_Const (Imm32 pre_arr_13))
     (BExp_Const (Imm32 pre_arr_14))
     (BExp_Const (Imm32 pre_arr_15))``);
   val (arr_0_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_1_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_2_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_3_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_4_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_5_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_6_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_7_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_8_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_9_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_10_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_11_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_12_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_13_exp, bir_exprs) = dest_pair bir_exprs;
   val (arr_14_exp, arr_15_exp) = dest_pair bir_exprs;
 in
   bslSyntax.bandl [
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x10" ^arr_0_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x16" ^arr_1_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x17" ^arr_2_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x6" ^arr_3_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x22" ^arr_4_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x11" ^arr_5_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x13" ^arr_6_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x14" ^arr_7_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x28" ^arr_8_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x29" ^arr_9_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x30" ^arr_10_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x31" ^arr_11_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x26" ^arr_12_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x25" ^arr_13_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x24" ^arr_14_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bir_var_equal_32_lowcast_64 "x23" ^arr_15_exp``)
   ]
 end;

Definition bspec_chacha20_double_round_post_def:
 bspec_chacha20_double_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha20_double_round_post_tm
End

val _ = export_theory ();
