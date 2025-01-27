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

val _ = new_theory "chacha_spec";

Theorem w2w_32_64:
 !(b1:word32). w2w ((w2w b1):word64) = b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11] >>
  IMP_RES_TAC (DECIDE ``n < 4294967296 ==> n < 18446744073709551616:num``) >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
QED

Theorem n2w_w2n_w2w_32_64:
 !(b1:word32). n2w ((w2n b1)) = (w2w:word32 -> word64) b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

Theorem w2w_n2w_w2n_64_32:
 !(b1:word64). (w2w:word64 -> word32) b1 = n2w ((w2n b1))
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

(* ------------- *)
(* ChaCha theory *)
(* ------------- *)

(*
op line (a:idx) (b:idx) (d:idx) (s:int) (m:state) : state =
  let m = m.[a <- (m.[a] + m.[b])] in
  let m = m.[d <- W32.rol (m.[d] +^ m.[a]) s] in m.
*)

Definition chacha_line:
 chacha_line (a:word32) (b:word32) (d:word32) (s:word32)
  (m:word32 -> word32) =
  let m = (a =+ (m a) + (m b)) m in
  let m = (d =+ ((m d) ?? (m a)) #<<~ s) m in
  m
End

Definition chacha_line_alt:
 chacha_line_alt (a:word32) (b:word32) (d:word32) (s:word32)
  (m:word32 -> word32) =
 let m = (a =+ (m a) + (m b)) m in
 let m = (d =+ (((m d) ?? (m a)) <<~ s) || (((m d) ?? (m a)) >>>~ (32w - s))) m in
 m
End

Theorem word32_le_31_eq:
 !(w:word32). w <=+ 31w ==> 31w && w = w
Proof
 blastLib.BBLAST_TAC
QED

Theorem replace_word_rol_bv_or_shifts:
 !x s : word32. s <=+ 31w ==>
  x #<<~ s = (x <<~ s) || (x >>>~ (32w - s))
Proof
 rw [] >>
 `dimindex (:32) = 2 ** 5` by rw [] >>
 MP_TAC (Q.SPECL [`5`, `x`, `s`] (INST_TYPE [Type.alpha |-> ``:32``] word_rol_OR_SHIFT)) >>
 rw [word32_le_31_eq]
QED

Theorem chacha_line_expand:
 !a b d s m. s <=+ 31w ==>
  chacha_line a b d s m = 
   (let m = (a =+ (m a) + (m b)) m in
    let m = (d =+ (((m d) ?? (m a)) <<~ s) || (((m d) ?? (m a)) >>>~ (32w - s))) m
    in m)  
Proof
 rw [chacha_line,replace_word_rol_bv_or_shifts]
QED

Theorem chacha_line_alt_eq:
 !a b d s m. s <=+ 31w ==>
  chacha_line a b d s m = chacha_line_alt a b d s m
Proof
 rw [chacha_line_expand,chacha_line_alt]
QED

(*
op quarter_round a b c d : shuffle =
  line a b d 16 \oo
  line c d b 12 \oo
  line a b d 8  \oo
  line c d b 7.
*)

Definition chacha_quarter_round:
 chacha_quarter_round (a:word32) (b:word32) (c:word32) (d:word32) =
  chacha_line c d b 7w o
  chacha_line a b d 8w o 
  chacha_line c d b 12w o 
  chacha_line a b d 16w
End

Definition chacha_quarter_round_alt:
 chacha_quarter_round_alt (a:word32) (b:word32) (c:word32) (d:word32) =
  chacha_line_alt c d b 7w o
  chacha_line_alt a b d 8w o 
  chacha_line_alt c d b 12w o 
  chacha_line_alt a b d 16w
End

Theorem chacha_quarter_round_alt_eq:
 !a b c d m.
 chacha_quarter_round a b c d m = 
 chacha_quarter_round_alt a b c d m
Proof
 rw [chacha_quarter_round,chacha_quarter_round_alt] >>
 `(7w:word32) <=+ 31w` by rw [] >>
 `(8w:word32) <=+ 31w` by rw [] >>
 `(12w:word32) <=+ 31w` by rw [] >>
 `(16w:word32) <=+ 31w` by rw [] >>
 rw [chacha_line_alt_eq]
QED

(*
op column_round : shuffle =
  quarter_round 0 4 8  12 \oo
  quarter_round 1 5 9  13 \oo
  quarter_round 2 6 10 14 \oo
  quarter_round 3 7 11 15.
*)
        
Definition chacha_column_round:
 chacha_column_round =
  chacha_quarter_round 3w 7w 11w 15w o
  chacha_quarter_round 2w 6w 10w 14w o
  chacha_quarter_round 1w 5w 9w 13w o
  chacha_quarter_round 0w 4w 8w 12w
End

Definition chacha_column_round_alt:
 chacha_column_round_alt =
  chacha_quarter_round_alt 3w 7w 11w 15w o
  chacha_quarter_round_alt 2w 6w 10w 14w o
  chacha_quarter_round_alt 1w 5w 9w 13w o
  chacha_quarter_round_alt 0w 4w 8w 12w
End

Theorem chacha_column_round_alt_eq:
 !m. chacha_column_round m = chacha_column_round_alt m
Proof
 rw [chacha_column_round,chacha_column_round_alt] >>
 rw [chacha_quarter_round_alt_eq]
QED

(*
op diagonal_round : shuffle =
  quarter_round 0 5 10 15 \oo
  quarter_round 1 6 11 12 \oo
  quarter_round 2 7 8  13 \oo
  quarter_round 3 4 9  14.
*)

Definition chacha_diagonal_round:
 chacha_diagonal_round =
  chacha_quarter_round 3w 4w 9w 14w o
  chacha_quarter_round 2w 7w 8w 13w o
  chacha_quarter_round 1w 6w 11w 12w o
  chacha_quarter_round 0w 5w 10w 15w
End

Definition chacha_diagonal_round_alt:
 chacha_diagonal_round_alt =
  chacha_quarter_round_alt 3w 4w 9w 14w o
  chacha_quarter_round_alt 2w 7w 8w 13w o
  chacha_quarter_round_alt 1w 6w 11w 12w o
  chacha_quarter_round_alt 0w 5w 10w 15w
End

Theorem chacha_diagonal_round_alt_eq:
 !m. chacha_diagonal_round m = chacha_diagonal_round_alt m
Proof
 rw [chacha_diagonal_round,chacha_diagonal_round_alt] >>
 rw [chacha_quarter_round_alt_eq]
QED

(*
op double_round: shuffle =
  column_round \oo diagonal_round.
*)

Definition chacha_double_round:
 chacha_double_round =
  chacha_diagonal_round o chacha_column_round
End

Definition chacha_double_round_alt:
 chacha_double_round_alt =
  chacha_diagonal_round_alt o chacha_column_round_alt
End

Theorem chacha_double_round_alt_eq:
 !m. chacha_double_round m = chacha_double_round_alt m
Proof
 rw [chacha_double_round,chacha_double_round_alt] >>
 rw [chacha_diagonal_round_alt_eq,chacha_column_round_alt_eq]
QED

Definition chacha_rounds:
 chacha_rounds =
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round o
  chacha_double_round
End

Definition chacha_rounds_alt:
 chacha_rounds_alt =
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt o
  chacha_double_round_alt
End

Theorem chacha_rounds_alt_eq:
 !m. chacha_rounds m = chacha_rounds_alt m
Proof
 rw [chacha_rounds,chacha_rounds_alt] >>
 rw [chacha_double_round_alt_eq]
QED

Definition chacha_add_16:
 chacha_add_16 (s: word32 -> word32)
  (s' : word32 -> word32) : word32 -> word32 =
  let m = s in
  let m = (0w =+ (s 0w) + (s' 0w)) m in
  let m = (1w =+ (s 1w) + (s' 1w)) m in
  let m = (2w =+ (s 2w) + (s' 2w)) m in
  let m = (3w =+ (s 3w) + (s' 3w)) m in
  let m = (4w =+ (s 4w) + (s' 4w)) m in
  let m = (5w =+ (s 5w) + (s' 5w)) m in
  let m = (6w =+ (s 6w) + (s' 6w)) m in
  let m = (7w =+ (s 7w) + (s' 7w)) m in
  let m = (8w =+ (s 8w) + (s' 8w)) m in
  let m = (9w =+ (s 9w) + (s' 9w)) m in
  let m = (10w =+ (s 10w) + (s' 10w)) m in
  let m = (11w =+ (s 11w) + (s' 11w)) m in
  let m = (12w =+ (s 12w) + (s' 12w)) m in
  let m = (13w =+ (s 13w) + (s' 13w)) m in
  let m = (14w =+ (s 14w) + (s' 14w)) m in
  let m = (15w =+ (s 15w) + (s' 15w)) m in
  m
End

Definition chacha_core:
 chacha_core (s:word32 -> word32) : word32 -> word32 =
  let s' = chacha_rounds s in
  chacha_add_16 s' s
End

Definition chacha_core_alt:
 chacha_core_alt (s:word32 -> word32) : word32 -> word32 =
  let s' = chacha_rounds_alt s in
  chacha_add_16 s' s
End

Theorem chacha_core_alt_eq:
 !s. chacha_core s = chacha_core_alt s
Proof
 rw [chacha_core,chacha_core_alt] >>
 rw [chacha_rounds_alt_eq]
QED

Definition chacha_setup:
 chacha_setup (m : word32 -> word32) 
  (k : word32 -> word32) (n : word32 -> word32) (c : word32) 
   : word32 -> word32 =
  let m = (0w =+ 0x61707865w) m in
  let m = (1w =+ 0x3320646ew) m in
  let m = (2w =+ 0x79622d32w) m in
  let m = (3w =+ 0x6b206574w) m in
  let m = (4w =+ (k 0w)) m in
  let m = (5w =+ (k 1w)) m in
  let m = (6w =+ (k 2w)) m in
  let m = (7w =+ (k 3w)) m in
  let m = (8w =+ (k 4w)) m in
  let m = (9w =+ (k 5w)) m in
  let m = (10w =+ (k 6w)) m in
  let m = (11w =+ (k 7w)) m in
  let m = (12w =+ c) m in
  let m = (13w =+ (n 0w)) m in
  let m = (14w =+ (n 1w)) m in
  let m = (15w =+ (n 2w)) m in
  m
End

(* Examples and validation *)

Definition chacha_example_state_row:
 chacha_example_state_row : word32 -> word32 =
  let m = ARB in
  let m = (0w =+ 0x11111111w) m in
  let m = (1w =+ 0x01020304w) m in
  let m = (2w =+ 0x9b8d6f43w) m in
  let m = (3w =+ 0x01234567w) m in
  m
End

Definition chacha_example_state_full:
 chacha_example_state_full : word32 -> word32 =
  let m = ARB in
  let m = (0w =+ 0x879531e0w) m in
  let m = (1w =+ 0xc5ecf37dw) m in
  let m = (2w =+ 0x516461b1w) m in
  let m = (3w =+ 0xc9a62f8aw) m in
  let m = (4w =+ 0x44c20ef3w) m in
  let m = (5w =+ 0x3390af7fw) m in
  let m = (6w =+ 0xd9fc690bw) m in
  let m = (7w =+ 0x2a5f714cw) m in
  let m = (8w =+ 0x53372767w) m in
  let m = (9w =+ 0xb00a5631w) m in
  let m = (10w =+ 0x974c541aw) m in
  let m = (11w =+ 0x359e9963w) m in
  let m = (12w =+ 0x5c971061w) m in
  let m = (13w =+ 0x3d631689w) m in
  let m = (14w =+ 0x2098d9d6w) m in
  let m = (15w =+ 0x91dbd320w) m in
  m
End

(* RFC7539 2.1.1 example *)
Theorem chacha_example_quarter_round_row[local]:
 chacha_quarter_round 0w 1w 2w 3w chacha_example_state_row 0w = 0xea2a92f4w
 /\
 chacha_quarter_round 0w 1w 2w 3w chacha_example_state_row 1w = 0xcb1cf8cew
 /\
 chacha_quarter_round 0w 1w 2w 3w chacha_example_state_row 2w = 0x4581472ew
 /\
 chacha_quarter_round 0w 1w 2w 3w chacha_example_state_row 3w = 0x5881c4bbw
Proof
 EVAL_TAC
QED

(* RFC7539 2.2.1 example *)
Theorem chacha_example_quarter_round_full[local]:
 chacha_quarter_round 2w 7w 8w 13w chacha_example_state_full 2w = 0xbdb886dcw
 /\
 chacha_quarter_round 2w 7w 8w 13w chacha_example_state_full 7w = 0xcfacafd2w
 /\
 chacha_quarter_round 2w 7w 8w 13w chacha_example_state_full 8w = 0xe46bea80w
 /\
 chacha_quarter_round 2w 7w 8w 13w chacha_example_state_full 13w = 0xccc07c79w
Proof
 EVAL_TAC
QED

Definition chacha_example_state_key_setup:
 chacha_example_state_key_setup : word32 -> word32 =
  let m = ARB in
  let m = (0w =+ 0x61707865w) m in
  let m = (1w =+ 0x3320646ew) m in
  let m = (2w =+ 0x79622d32w) m in
  let m = (3w =+ 0x6b206574w) m in
  let m = (4w =+ 0x03020100w) m in
  let m = (5w =+ 0x07060504w) m in
  let m = (6w =+ 0x0b0a0908w) m in
  let m = (7w =+ 0x0f0e0d0cw) m in
  let m = (8w =+ 0x13121110w) m in
  let m = (9w =+ 0x17161514w) m in
  let m = (10w =+ 0x1b1a1918w) m in
  let m = (11w =+ 0x1f1e1d1cw) m in
  let m = (12w =+ 0x00000001w) m in
  let m = (13w =+ 0x09000000w) m in
  let m = (14w =+ 0x4a000000w) m in
  let m = (15w =+ 0x00000000w) m in
  m
End

(* RFC7539 2.3.2 example *)
Theorem chacha_example_state_key_setup[local]:
 chacha_rounds chacha_example_state_key_setup 0w = 0x837778abw
 /\
 chacha_rounds chacha_example_state_key_setup 1w = 0xe238d763w
 /\
 chacha_rounds chacha_example_state_key_setup 2w = 0xa67ae21ew
 /\
 chacha_rounds chacha_example_state_key_setup 3w = 0x5950bb2fw
Proof
 EVAL_TAC
QED

(* RISC-V spec *)

Definition riscv_chacha_line_exp_fst_def:
 riscv_chacha_line_exp_fst (pre_a:word32) (pre_b:word32) : word32 =
  pre_a + pre_b
End

Definition riscv_chacha_line_exp_snd_def:
 riscv_chacha_line_exp_snd pre_a pre_d (s:word32) : word32 =
  ((pre_a ?? pre_d) <<~ s) || ((pre_a ?? pre_d) >>>~ (32w - s))
End

Definition riscv_chacha_line_pre_def:
 riscv_chacha_line_pre (pre_a:word32)
  (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 10w)) = pre_a /\
  n2w (w2n (m.c_gpr m.procID 22w)) = pre_b /\
  n2w (w2n (m.c_gpr m.procID 26w)) = pre_d)
End

Definition riscv_chacha_line_post_def:
 riscv_chacha_line_post (pre_a:word32) (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool =
 (n2w (w2n (m.c_gpr m.procID 20w)) = riscv_chacha_line_exp_fst pre_a pre_b /\
  n2w (w2n (m.c_gpr m.procID 10w)) = riscv_chacha_line_exp_snd (riscv_chacha_line_exp_fst pre_a pre_b) pre_d 16w)
End

(* BIR spec *)

Definition bspec_var_equal_32_lowcast_64_def:
 bspec_var_equal_32_lowcast_64 var exp =
  BExp_BinPred
   BIExp_Equal
   (BExp_Cast BIExp_LowCast (BExp_Den (BVar var (BType_Imm Bit64))) Bit32)
   exp
End

(* a =+ (m a) + (m b) *)
Definition bspec_chacha_line_bir_exp_fst_def:
 bspec_chacha_line_bir_exp_fst pre_a_exp pre_b_exp : bir_exp_t =
  BExp_BinExp BIExp_Plus pre_a_exp pre_b_exp
End

(* d =+ (((m d) ?? (m a)) <<~ s) || (((m d) ?? (m a)) >>>~ (32w - s)) *)
Definition bspec_chacha_line_bir_exp_snd_def:
 bspec_chacha_line_bir_exp_snd pre_a_exp pre_d_exp (s:word32) : bir_exp_t =
   BExp_BinExp BIExp_Or
     (BExp_BinExp BIExp_LeftShift 
      (BExp_BinExp BIExp_Xor pre_a_exp pre_d_exp)
     (BExp_Const (Imm32 s)))
     (BExp_BinExp BIExp_RightShift
      (BExp_BinExp BIExp_Xor pre_a_exp pre_d_exp)
      (BExp_Const (Imm32 (32w-s))))
End

Definition bspec_chacha_quarter_round_bir_exprs_def:
 bspec_chacha_quarter_round_bir_exprs pre_a_exp pre_b_exp pre_c_exp pre_d_exp
  : bir_exp_t # bir_exp_t # bir_exp_t # bir_exp_t =
  let a = pre_a_exp in
  let b = pre_b_exp in
  let c = pre_c_exp in
  let d = pre_d_exp in

  let a = bspec_chacha_line_bir_exp_fst a b in
  let d = bspec_chacha_line_bir_exp_snd a d 16w in

  let c = bspec_chacha_line_bir_exp_fst c d in
  let b = bspec_chacha_line_bir_exp_snd c b 12w in
    
  let a = bspec_chacha_line_bir_exp_fst a b in
  let d = bspec_chacha_line_bir_exp_snd a d 8w in

  let c = bspec_chacha_line_bir_exp_fst c d in
  let b = bspec_chacha_line_bir_exp_snd c b 7w in

  (a,b,c,d)
End

Definition bspec_chacha_column_round_bir_exprs_def:
 bspec_chacha_column_round_bir_exprs 
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
   bspec_chacha_quarter_round_bir_exprs pre_arr_0 pre_arr_4 pre_arr_8 pre_arr_12
 in
 let (arr_1,arr_5,arr_9,arr_13) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_1 pre_arr_5 pre_arr_9 pre_arr_13
 in
 let (arr_2,arr_6,arr_10,arr_14) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_2 pre_arr_6 pre_arr_10 pre_arr_14
 in
 let (arr_3,arr_7,arr_11,arr_15) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_3 pre_arr_7 pre_arr_11 pre_arr_15
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition bspec_chacha_diagonal_round_bir_exprs_def:
 bspec_chacha_diagonal_round_bir_exprs 
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
   bspec_chacha_quarter_round_bir_exprs pre_arr_0 pre_arr_5 pre_arr_10 pre_arr_15
 in
 let (arr_1,arr_6,arr_11,arr_12) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_1 pre_arr_6 pre_arr_11 pre_arr_12
 in
 let (arr_2,arr_7,arr_8,arr_13) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_2 pre_arr_7 pre_arr_8 pre_arr_13
 in
 let (arr_3,arr_4,arr_9,arr_14) =
   bspec_chacha_quarter_round_bir_exprs pre_arr_3 pre_arr_4 pre_arr_9 pre_arr_14
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition bspec_chacha_round_bir_exprs_def:
 bspec_chacha_round_bir_exprs 
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
   bspec_chacha_column_round_bir_exprs
    pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
    pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
    pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
    pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
  in

  let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
       arr_8,arr_9,arr_10,arr_11, arr_12,arr_13,arr_14,arr_15) =
   bspec_chacha_diagonal_round_bir_exprs
    arr_0 arr_1 arr_2 arr_3 arr_4 arr_5 arr_6 arr_7
    arr_8 arr_9 arr_10 arr_11 arr_12 arr_13 arr_14 arr_15
  in

  (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
   arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* keysetup *)

Definition chacha_keysetup_init_addr_def:
 chacha_keysetup_init_addr : word64 = 0x10488w
End

Definition chacha_keysetup_end_addr_def:
 chacha_keysetup_end_addr : word64 = (*0x106a8w*) 0x1053cw
End

(* ivsetup *)

Definition chacha_ivsetup_init_addr_def:
 chacha_ivsetup_init_addr : word64 = 0x106bcw
End

Definition chacha_ivsetup_end_addr_def:
 chacha_ivsetup_end_addr : word64 = 0x10778w
End

(* first line *)

Definition chacha_line_init_addr_def:
  chacha_line_init_addr : word64 = 0x108a0w
End

Definition chacha_line_end_addr_def:
 chacha_line_end_addr : word64 = 0x108b4w
End

(* second line *)

Definition chacha_other_line_init_addr_def:
  chacha_other_line_init_addr : word64 = 0x108b4w
End

Definition chacha_other_line_end_addr_def:
 chacha_other_line_end_addr : word64 = 0x108c8w
End

(* first quarter round *)

Definition chacha_quarter_round_init_addr_def:
  chacha_quarter_round_init_addr : word64 = 0x108a0w
End

Definition chacha_quarter_round_end_addr_def:
  chacha_quarter_round_end_addr : word64 = 0x108f0w
End

(* column round *)

Definition chacha_column_round_init_addr_def:
  chacha_column_round_init_addr : word64 = 0x108a0w
End

Definition chacha_column_round_end_addr_def:
  chacha_column_round_end_addr : word64 = 0x109e0w
End

(* diagonal round *)

Definition chacha_diagonal_round_init_addr_def:
  chacha_diagonal_round_init_addr : word64 = 0x109e0w
End

Definition chacha_diagonal_round_end_addr_def:
  chacha_diagonal_round_end_addr : word64 = 0x10b64w
End

(* double round loop body *)

Definition chacha_double_round_init_addr_def:
  chacha_double_round_init_addr : word64 = 0x108a0w
End

Definition chacha_double_round_end_addr_def:
  chacha_double_round_end_addr : word64 = 0x10b64w
End

(* double round loop branch *)

Definition chacha_double_round_branch_init_addr_def:
  chacha_double_round_branch_init_addr : word64 = 0x10b64w
End

Definition chacha_double_round_branch_end_addr_loop_def:
  chacha_double_round_branch_end_addr_loop : word64 = 0x108a0w
End

Definition chacha_double_round_branch_end_addr_continue_def:
  chacha_double_round_branch_end_addr_continue : word64 = 0x10b68w
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* keysetup *)

val bspec_chacha_keysetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha_keysetup_pre_def:
 bspec_chacha_keysetup_pre : bir_exp_t =
  ^bspec_chacha_keysetup_pre_tm
End

(* ivsetup *)

val bspec_chacha_ivsetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha_ivsetup_pre_def:
 bspec_chacha_ivsetup_pre : bir_exp_t =
  ^bspec_chacha_ivsetup_pre_tm
End

(* first line *)

val bspec_chacha_line_pre_tm = bslSyntax.bandl [
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

Definition bspec_chacha_line_pre_def:
 bspec_chacha_line_pre (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_line_pre_tm
End

val bspec_chacha_line_post_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bspec_var_equal_32_lowcast_64 "x20"
    (bspec_chacha_line_bir_exp_fst
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))``),
  (snd o dest_eq o concl)
   (EVAL ``bspec_var_equal_32_lowcast_64 "x10"
    (bspec_chacha_line_bir_exp_snd
     (bspec_chacha_line_bir_exp_fst (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))
     (BExp_Const (Imm32 pre_d)) 16w)``)
];

Definition bspec_chacha_line_post_def:
 bspec_chacha_line_post (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_line_post_tm
End

(* second line *)

val bspec_chacha_line_pre_other_tm = bslSyntax.bandl [
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

Definition bspec_chacha_line_pre_other_def:
 bspec_chacha_line_pre_other (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_line_pre_other_tm
End

val bspec_chacha_line_post_other_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bspec_var_equal_32_lowcast_64 "x8"
    (bspec_chacha_line_bir_exp_fst
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))``),
  (snd o dest_eq o concl)
   (EVAL ``bspec_var_equal_32_lowcast_64 "x15"
    (bspec_chacha_line_bir_exp_snd
     (bspec_chacha_line_bir_exp_fst (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b)))
     (BExp_Const (Imm32 pre_d)) 12w)``)
];

Definition bspec_chacha_line_post_other_def:
 bspec_chacha_line_post_other (pre_a:word32) (pre_b:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_line_post_other_tm
End

(* first quarter round *)

val bspec_chacha_quarter_round_pre_tm = bslSyntax.bandl [
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

Definition bspec_chacha_quarter_round_pre_def:
 bspec_chacha_quarter_round_pre (pre_a:word32) (pre_b:word32)
 (pre_c:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_quarter_round_pre_tm
End

val bspec_chacha_quarter_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``bspec_chacha_quarter_round_bir_exprs 
     (BExp_Const (Imm32 pre_a)) (BExp_Const (Imm32 pre_b))
     (BExp_Const (Imm32 pre_c)) (BExp_Const (Imm32 pre_d))``);
   val (a_exp, bir_exprs) = dest_pair bir_exprs;
   val (b_exp, bir_exprs) = dest_pair bir_exprs;
   val (c_exp, d_exp) = dest_pair bir_exprs;
 in
   bslSyntax.bandl [
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x20" ^a_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x21" ^b_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x8" ^c_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x22" ^d_exp``)
   ]
 end;

Definition bspec_chacha_quarter_round_post_def:
 bspec_chacha_quarter_round_post (pre_a:word32) (pre_b:word32)
  (pre_c:word32) (pre_d:word32) : bir_exp_t =
  ^bspec_chacha_quarter_round_post_tm
End

(* column round *)

val bspec_chacha_column_round_pre_tm = bslSyntax.bandl [
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

Definition bspec_chacha_column_round_pre_def:
 bspec_chacha_column_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha_column_round_pre_tm
End

val bspec_chacha_column_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``bspec_chacha_column_round_bir_exprs 
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
     (EVAL ``bspec_var_equal_32_lowcast_64 "x20" ^arr_0_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x19" ^arr_1_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x18" ^arr_2_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x9" ^arr_3_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x21" ^arr_4_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x10" ^arr_5_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x13" ^arr_6_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x14" ^arr_7_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x8" ^arr_8_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x7" ^arr_9_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x5" ^arr_10_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x15" ^arr_11_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x22" ^arr_12_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x28" ^arr_13_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x29" ^arr_14_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x16" ^arr_15_exp``)
   ]
 end;

Definition bspec_chacha_column_round_post_def:
 bspec_chacha_column_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha_column_round_post_tm
End

(* diagonal round *)

val bspec_chacha_diagonal_round_pre_tm = bslSyntax.bandl [
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

Definition bspec_chacha_diagonal_round_pre_def:
 bspec_chacha_diagonal_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha_diagonal_round_pre_tm
End

val bspec_chacha_diagonal_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``bspec_chacha_diagonal_round_bir_exprs 
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
     (EVAL ``bspec_var_equal_32_lowcast_64 "x10" ^arr_0_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x16" ^arr_1_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x17" ^arr_2_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x6" ^arr_3_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x22" ^arr_4_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x11" ^arr_5_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x13" ^arr_6_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x14" ^arr_7_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x28" ^arr_8_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x29" ^arr_9_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x30" ^arr_10_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x31" ^arr_11_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x26" ^arr_12_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x25" ^arr_13_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x24" ^arr_14_exp``),
    (snd o dest_eq o concl)
     (EVAL ``bspec_var_equal_32_lowcast_64 "x23" ^arr_15_exp``)
   ]
 end;

Definition bspec_chacha_diagonal_round_post_def:
 bspec_chacha_diagonal_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha_diagonal_round_post_tm
End

(* double round *)

val bspec_chacha_double_round_pre_tm = bslSyntax.bandl [
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

Definition bspec_chacha_double_round_pre_def:
 bspec_chacha_double_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32) 
 : bir_exp_t =
  ^bspec_chacha_double_round_pre_tm
End

val bspec_chacha_double_round_post_tm =
 let
   val bir_exprs = (snd o dest_eq o concl)
    (EVAL ``bspec_chacha_round_bir_exprs 
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
     (EVAL ``bspec_var_equal_32_lowcast_64 "x10" ^arr_0_exp``)
   ]
 end;

Definition bspec_chacha_double_round_post_def:
 bspec_chacha_double_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32)
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 : bir_exp_t =
  ^bspec_chacha_double_round_post_tm
End

val _ = export_theory ();
