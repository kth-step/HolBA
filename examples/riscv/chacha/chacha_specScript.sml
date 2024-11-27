open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

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

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

val _ = new_theory "chacha_spec";

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

Definition chacha_line_alt_word64:
 chacha_line_alt_word64 (a:word64) (b:word64) (d:word64) (s:word32)
  (m:word64 -> word64) =
  let m = (a =+ (sw2sw: word32 -> word64) ((w2w (m a)) + (w2w (m b)))) m in
  let m = (d =+ 
   ((sw2sw: word32 -> word64) ((w2w ((m a) ?? (m d))) <<~ s))
   ||
   ((sw2sw: word32 -> word64) ((w2w ((m a) ?? (m d))) >>>~ (32w - s)))
  ) m
  in m
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

Theorem chacha_line_alt_word64_eq[local]:
 !a b d s m x.
  s <=+ 31w ==>
  (w2w o (chacha_line (w2w a) (w2w b) (w2w d) s (\w. w2w (m (w2w w))) o w2w)) x =
  chacha_line_alt a b d s m x
Proof
 rw [chacha_line_expand,chacha_line_alt] >>
 rw [combinTheory.APPLY_UPDATE_THM] >>
 cheat
 (*rw [sw2sw_w2w]*)
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

(* first quarterround *)

Definition chacha_quarterround_init_addr_def:
  chacha_quarterround_init_addr : word64 = 0x108a0w
End

Definition chacha_quarterround_end_addr_def:
 chacha_quarterround_end_addr : word64 = 0x108b4w
End

(* second quarterround *)

Definition chacha_other_quarterround_init_addr_def:
  chacha_other_quarterround_init_addr : word64 = 0x108b4w
End

Definition chacha_other_quarterround_end_addr_def:
 chacha_other_quarterround_end_addr : word64 = 0x108c8w
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

(* quarterround *)

(*
1.  a += b; d ^= a; d <<<= 16;
2.  c += d; b ^= c; b <<<= 12;
3.  a += b; d ^= a; d <<<= 8;
4.  c += d; b ^= c; b <<<= 7;

----

x20 <- x10 + x22  // a += b
x26 <- x20 ^ x26  // d ^= a
x10 <- x26 lsl 16
x26 <- x26 lsr 16
x10 <- x10 | x26  // d <<<= 16

RESULT:
a: x20 <- x10 + x22
d: x10 <- (((x10 + x22) ^ x26) lsl 16) | (((x10 + x22) ^ x26) lsr 16)

---

a: x20
d: x10
c: x8
b: x22

---

x8 <- x28 + x10   // c += d
x22 <- x8 ^ x22   // b ^= c
x15 <- x22 lsl 12
x22 <- x22 lsr 20
x15 <- x15 | x22  // b <<<= 12

x8, x10, x15, x22

RESULT:
c: x8 <- x28 + x10
b: x15 <- (((x28 + x10) ^ x22) lsl 12) | (((x28 + x10) ^ x22) lsr 20)

x20 <- x15 + x20  // a += b
x10 <- x20 ^ x10  // d ^= a
x22 <- x10 lsl 8
x10 <- x10 lsr 24
x22 <- x10 | x22  // d <<<= 8

x8 <- x8 + x22    // c += d
x15 <- x15 ^ x8   // b ^= c
x21 <- x15 lsl 7
x15 <- x15 lsr 25
x21 <- x15 | x21  // b <<<= 7
*)

val bspec_chacha_quarterround_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x12",
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x10" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x20" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_x20))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x22" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_x22))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Cast BIExp_LowCast (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
    (BExp_Const (Imm32 pre_x26))``  
];

Definition bspec_chacha_quarterround_pre_def:
 bspec_chacha_quarterround_pre (pre_x10:word32) 
  (pre_x20:word32) (pre_x22:word32) (pre_x26:word32) : bir_exp_t =
  ^bspec_chacha_quarterround_pre_tm
End

val bspec_chacha_quarterround_pre_other_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x12",
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x8" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x8))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x10" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x10))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x15" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x15))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x22" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x22))``,
  ``BExp_BinPred
    BIExp_Equal
    (BExp_Den (BVar "x28" (BType_Imm Bit64)))
    (BExp_Const (Imm64 pre_x28))``  
];

Definition bspec_chacha_quarterround_pre_other_def:
 bspec_chacha_quarterround_pre_other (pre_x8:word64) (pre_x10:word64) 
  (pre_x15:word64) (pre_x22:word64) (pre_x28:word64) : bir_exp_t =
  ^bspec_chacha_quarterround_pre_other_tm
End

Definition bspec_chacha_quarterround_exp_1:
 bspec_chacha_quarterround_exp_1 varname pre_1 pre_2 : bir_exp_t =
 BExp_BinPred
   BIExp_Equal
   (BExp_Den (BVar varname (BType_Imm Bit64)))
   (BExp_Cast BIExp_SignedCast
    (BExp_Cast BIExp_LowCast 
     (BExp_BinExp BIExp_Plus
       (BExp_Const (Imm64 pre_1))
       (BExp_Const (Imm64 pre_2)))
     Bit32) Bit64)
End

Definition bspec_chacha_quarterround_exp_1_imm32:
 bspec_chacha_quarterround_exp_1_imm32 varname pre_1 pre_2 : bir_exp_t =
 BExp_BinPred
   BIExp_Equal
   (BExp_Cast BIExp_LowCast (BExp_Den (BVar varname (BType_Imm Bit64))) Bit32)
   (BExp_BinExp BIExp_Plus
     (BExp_Const (Imm32 pre_1))
     (BExp_Const (Imm32 pre_2)))
End

Definition bspec_chacha_quarterround_exp_2:
 bspec_chacha_quarterround_exp_2 varname pre_1 pre_2 pre_3 (s:word32) : bir_exp_t =
  BExp_BinPred
   BIExp_Equal
   (BExp_Den (BVar varname (BType_Imm Bit64)))
   (BExp_BinExp BIExp_Or
  (BExp_Cast BIExp_SignedCast
    (BExp_BinExp BIExp_LeftShift
      (BExp_Cast BIExp_LowCast 
       (BExp_BinExp BIExp_Xor
        (BExp_BinExp BIExp_Plus
         (BExp_Const (Imm64 pre_1))
         (BExp_Const (Imm64 pre_2)))
     (BExp_Const (Imm64 pre_3)))
       Bit32)
      (BExp_Const (Imm32 s))) Bit64)
  (BExp_Cast BIExp_SignedCast
    (BExp_BinExp BIExp_RightShift
      (BExp_Cast BIExp_LowCast 
       (BExp_BinExp BIExp_Xor
        (BExp_BinExp BIExp_Plus
         (BExp_Const (Imm64 pre_1))
         (BExp_Const (Imm64 pre_2)))
     (BExp_Const (Imm64 pre_3)))
       Bit32)
      (BExp_Const (Imm32 (32w-s)))) Bit64))
End

Definition bspec_chacha_quarterround_exp_2_imm32:
 bspec_chacha_quarterround_exp_2_imm32 varname pre_1 pre_2 pre_3 (s:word32) : bir_exp_t =
  BExp_BinPred
   BIExp_Equal
   (BExp_Cast BIExp_LowCast (BExp_Den (BVar varname (BType_Imm Bit64))) Bit32)
   (BExp_BinExp BIExp_Or
     (BExp_BinExp BIExp_LeftShift 
      (BExp_BinExp BIExp_Xor
        (BExp_BinExp BIExp_Plus
         (BExp_Const (Imm32 pre_1))
         (BExp_Const (Imm32 pre_2)))
        (BExp_Const (Imm32 pre_3)))
     (BExp_Const (Imm32 s)))
     (BExp_BinExp BIExp_RightShift
      (BExp_BinExp BIExp_Xor
        (BExp_BinExp BIExp_Plus
         (BExp_Const (Imm32 pre_1))
         (BExp_Const (Imm32 pre_2)))
        (BExp_Const (Imm32 pre_3)))
      (BExp_Const (Imm32 (32w-s)))))
End

val bspec_chacha_quarterround_post_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bspec_chacha_quarterround_exp_1_imm32 "x20" pre_x10 pre_x22``),
  (snd o dest_eq o concl)
   (EVAL ``bspec_chacha_quarterround_exp_2_imm32 "x10" pre_x10 pre_x22 pre_x26 (16w:word32)``)
];

Definition bspec_chacha_quarterround_post_def:
 bspec_chacha_quarterround_post (pre_x10:word32) 
  (pre_x20:word32) (pre_x22:word32) (pre_x26:word32)
  : bir_exp_t =
  ^bspec_chacha_quarterround_post_tm
End

val bspec_chacha_quarterround_post_other_tm = bslSyntax.bandl [
  (snd o dest_eq o concl)
   (EVAL ``bspec_chacha_quarterround_exp_1 "x8" pre_x28 pre_x10``),
  (snd o dest_eq o concl)
   (EVAL ``bspec_chacha_quarterround_exp_2 "x15" pre_x28 pre_x10 pre_x22 (12w:word32)``)
];

Definition bspec_chacha_quarterround_post_other_def:
 bspec_chacha_quarterround_post_other (pre_x8:word64)
  (pre_x10:word64) (pre_x15:word64) (pre_x22:word64) (pre_x28:word64)
  : bir_exp_t =
  ^bspec_chacha_quarterround_post_other_tm
End

val _ = export_theory ();
