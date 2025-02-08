open HolKernel boolLib Parse bossLib;

open pairTheory pred_setTheory markerTheory wordsTheory wordsLib;

open bir_extra_expsTheory;

val _ = new_theory "chacha";

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

val _ = export_theory ();
