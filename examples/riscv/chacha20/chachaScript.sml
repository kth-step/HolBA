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

(* ChaCha implementation spec *)

Definition chacha_line_exp_fst_def:
 chacha_line_exp_fst (pre_a:word32) (pre_b:word32) : word32 =
  pre_a + pre_b
End

Definition chacha_line_exp_snd_orig_def:
 chacha_line_exp_snd_orig pre_a pre_d (s:word32) : word32 =
  (pre_a ?? pre_d) #<<~ s
End

Definition chacha_line_exp_snd_def:
 chacha_line_exp_snd pre_a pre_d (s:word32) : word32 =
  ((pre_a ?? pre_d) <<~ s) || ((pre_a ?? pre_d) >>>~ (32w - s))
End

Theorem chacha_line_exp_snd_orig_eq:
 !(a:word32) (d:word32) (s:word32). s <=+ 31w ==>
  chacha_line_exp_snd_orig a d s = chacha_line_exp_snd a d s
Proof
 rw [
  chacha_line_exp_snd_orig_def,
  chacha_line_exp_snd_def,
  replace_word_rol_bv_or_shifts  
 ]
QED

Definition chacha_quarter_round_exprs_def:
 chacha_quarter_round_exprs pre_a pre_b pre_c pre_d
  : word32 # word32 # word32 # word32 =
  let a = pre_a in
  let b = pre_b in
  let c = pre_c in
  let d = pre_d in

  let a = chacha_line_exp_fst a b in
  let d = chacha_line_exp_snd a d 16w in

  let c = chacha_line_exp_fst c d in
  let b = chacha_line_exp_snd c b 12w in

  let a = chacha_line_exp_fst a b in
  let d = chacha_line_exp_snd a d 8w in

  let c = chacha_line_exp_fst c d in
  let b = chacha_line_exp_snd c b 7w in

  (a,b,c,d)
End

Definition chacha_column_round_exprs_def:
 chacha_column_round_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32
  =
 let (arr_0,arr_4,arr_8,arr_12) =
   chacha_quarter_round_exprs pre_arr_0 pre_arr_4 pre_arr_8 pre_arr_12
 in
 let (arr_1,arr_5,arr_9,arr_13) =
   chacha_quarter_round_exprs pre_arr_1 pre_arr_5 pre_arr_9 pre_arr_13
 in
 let (arr_2,arr_6,arr_10,arr_14) =
   chacha_quarter_round_exprs pre_arr_2 pre_arr_6 pre_arr_10 pre_arr_14
 in
 let (arr_3,arr_7,arr_11,arr_15) =
   chacha_quarter_round_exprs pre_arr_3 pre_arr_7 pre_arr_11 pre_arr_15
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition chacha_diagonal_round_exprs_def:
 chacha_diagonal_round_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32
  =
 let (arr_0,arr_5,arr_10,arr_15) =
   chacha_quarter_round_exprs pre_arr_0 pre_arr_5 pre_arr_10 pre_arr_15
 in
 let (arr_1,arr_6,arr_11,arr_12) =
   chacha_quarter_round_exprs pre_arr_1 pre_arr_6 pre_arr_11 pre_arr_12
 in
 let (arr_2,arr_7,arr_8,arr_13) =
   chacha_quarter_round_exprs pre_arr_2 pre_arr_7 pre_arr_8 pre_arr_13
 in
 let (arr_3,arr_4,arr_9,arr_14) =
   chacha_quarter_round_exprs pre_arr_3 pre_arr_4 pre_arr_9 pre_arr_14
 in
 (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
  arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Definition chacha_double_round_exprs_def:
 chacha_double_round_exprs 
  pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
  pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
  pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
  pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
 : word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32 #
   word32 # word32 # word32 # word32
  =
  let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
       arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15) =
   chacha_column_round_exprs
    pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3
    pre_arr_4 pre_arr_5 pre_arr_6 pre_arr_7
    pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11
    pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15
  in

  let (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
       arr_8,arr_9,arr_10,arr_11, arr_12,arr_13,arr_14,arr_15) =
   chacha_diagonal_round_exprs
    arr_0 arr_1 arr_2 arr_3 arr_4 arr_5 arr_6 arr_7
    arr_8 arr_9 arr_10 arr_11 arr_12 arr_13 arr_14 arr_15
  in

  (arr_0,arr_1,arr_2,arr_3,arr_4,arr_5,arr_6,arr_7,
   arr_8,arr_9,arr_10,arr_11,arr_12,arr_13,arr_14,arr_15)
End

Theorem chacha_quarter_round_eq_exprs:
 !m a b c d 
  pre_a_val pre_b_val pre_c_val pre_d_val
  post_a_val post_b_val post_c_val post_d_val.

  m a = pre_a_val /\ m b = pre_b_val /\ m c = pre_c_val /\ m d = pre_d_val /\

  a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d ==>

  ((chacha_quarter_round_exprs pre_a_val pre_b_val pre_c_val pre_d_val =
   (post_a_val,post_b_val,post_c_val,post_d_val))
  <=>
  (chacha_quarter_round a b c d m a = post_a_val /\
   chacha_quarter_round a b c d m b = post_b_val /\
   chacha_quarter_round a b c d m c = post_c_val /\
   chacha_quarter_round a b c d m d = post_d_val))
Proof
 once_rewrite_tac [chacha_quarter_round_alt_eq] >>
 rw [chacha_quarter_round_exprs_def,chacha_line_exp_fst_def,chacha_line_exp_snd_def,
  chacha_quarter_round_alt,chacha_line_alt,combinTheory.APPLY_UPDATE_THM] >>
 blastLib.BBLAST_TAC
QED

Theorem chacha_line_neq_eq:
 !a b d s m w. w <> a /\ w <> d ==>
  chacha_line a b d s m w = m w
Proof
 rw [chacha_line,combinTheory.APPLY_UPDATE_THM]
QED

Theorem chacha_quarter_round_neq_eq:
 !m a b c d s. 
 s <> a /\ s <> b /\ s <> c /\ s <> d ==>
 chacha_quarter_round a b c d m s = m s
Proof
 rw [chacha_quarter_round,chacha_line_neq_eq] 
QED

Theorem chacha_line_m_eq:
 !a b d s m m' w. m a = m' a /\ m b = m' b /\ m d = m' d /\ m w = m' w ==>
  chacha_line a b d s m w = chacha_line a b d s m' w
Proof
 rw [chacha_line,combinTheory.APPLY_UPDATE_THM]
QED

Theorem chacha_quarter_round_m_eq:
!m m' a b c d s.
 m a = m' a /\ m b = m' b /\ m c = m' c /\ m d = m' d /\ m s = m' s ==>
 chacha_quarter_round a b c d m s =
 chacha_quarter_round a b c d m' s
Proof
 rw [chacha_quarter_round,chacha_line_m_eq]
QED

Theorem chacha_quarter_round_eq_neq:
 !m a1 b1 c1 d1 a2 b2 c2 d2 s.
 s <> a2 /\ s <> b2 /\ s <> c2 /\ s <> d2 /\
 a1 <> a2 /\ a1 <> b2 /\ a1 <> c2 /\ a1 <> d2 /\
 b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ b1 <> d2 /\
 c1 <> a2 /\ c1 <> b2 /\ c1 <> c2 /\ c1 <> d2 /\
 d1 <> a2 /\ d1 <> b2 /\ d1 <> c2 /\ d1 <> d2 ==>
 chacha_quarter_round a1 b1 c1 d1 (chacha_quarter_round a2 b2 c2 d2 m) s =
 chacha_quarter_round a1 b1 c1 d1 m s
Proof
 rw [] >> 
 `chacha_quarter_round a2 b2 c2 d2 m s = m s` by METIS_TAC [chacha_quarter_round_neq_eq] >>
 `chacha_quarter_round a2 b2 c2 d2 m a1 = m a1` by METIS_TAC [chacha_quarter_round_neq_eq] >>
 `chacha_quarter_round a2 b2 c2 d2 m b1 = m b1` by METIS_TAC [chacha_quarter_round_neq_eq] >>
 `chacha_quarter_round a2 b2 c2 d2 m c1 = m c1` by METIS_TAC [chacha_quarter_round_neq_eq] >>
 `chacha_quarter_round a2 b2 c2 d2 m d1 = m d1` by METIS_TAC [chacha_quarter_round_neq_eq] >>
 METIS_TAC [chacha_quarter_round_m_eq]
QED

Theorem chacha_column_round_eq_exprs:
 !(m : word32 -> word32)

  pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val

  post_arr_0_val post_arr_1_val post_arr_2_val post_arr_3_val post_arr_4_val post_arr_5_val
  post_arr_6_val post_arr_7_val post_arr_8_val post_arr_9_val post_arr_10_val post_arr_11_val
  post_arr_12_val post_arr_13_val post_arr_14_val post_arr_15_val.

  m 0w = pre_arr_0_val /\ m 1w = pre_arr_1_val /\ m 2w = pre_arr_2_val /\ m 3w = pre_arr_3_val /\
  m 4w = pre_arr_4_val /\ m 5w = pre_arr_5_val /\ m 6w = pre_arr_6_val /\ m 7w = pre_arr_7_val /\
  m 8w = pre_arr_8_val /\ m 9w = pre_arr_9_val /\ m 10w = pre_arr_10_val /\ m 11w = pre_arr_11_val /\
  m 12w = pre_arr_12_val /\ m 13w = pre_arr_13_val /\ m 14w = pre_arr_14_val /\ m 15w = pre_arr_15_val /\

  (chacha_column_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)) ==>

  chacha_column_round m 0w = post_arr_0_val /\
  chacha_column_round m 1w = post_arr_1_val /\
  chacha_column_round m 2w = post_arr_2_val /\
  chacha_column_round m 3w = post_arr_3_val /\
  chacha_column_round m 4w = post_arr_4_val /\
  chacha_column_round m 5w = post_arr_5_val /\
  chacha_column_round m 6w = post_arr_6_val /\
  chacha_column_round m 7w = post_arr_7_val /\
  chacha_column_round m 8w = post_arr_8_val /\
  chacha_column_round m 9w = post_arr_9_val /\
  chacha_column_round m 10w = post_arr_10_val /\
  chacha_column_round m 11w = post_arr_11_val /\
  chacha_column_round m 12w = post_arr_12_val /\
  chacha_column_round m 13w = post_arr_13_val /\
  chacha_column_round m 14w = post_arr_14_val /\
  chacha_column_round m 15w = post_arr_15_val
Proof
 once_rewrite_tac [chacha_column_round,chacha_column_round_exprs_def] >>

 rw [] >> fs [] >>

 Cases_on `chacha_quarter_round_exprs (m 3w) (m 7w) (m 11w) (m 15w)` >>
 rename1 `(a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3)` >>

 Cases_on `chacha_quarter_round_exprs (m 2w) (m 6w) (m 10w) (m 14w)` >>
 rename1 `(a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,a6,a7)` >>

 Cases_on `chacha_quarter_round_exprs (m 1w) (m 5w) (m 9w) (m 13w)` >>
 rename1 `(a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,a10,a11)` >>

 Cases_on `chacha_quarter_round_exprs (m 0w) (m 4w) (m 8w) (m 12w)` >>
 rename1 `(a12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,a14,a15)` >>

 fs [] >> rw [] >>

 rw [chacha_quarter_round_neq_eq] >| [

 `(0w:word32) <> 4w /\ (0w:word32) <> 8w /\ (0w:word32) <> 12w /\
  (4w:word32) <> 8w /\ (4w:word32) <> 12w /\ (8w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 5w /\ (1w:word32) <> 9w /\ (1w:word32) <> 13w /\
  (5w:word32) <> 9w /\ (5w:word32) <> 13w /\ (9w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 6w /\ (2w:word32) <> 10w /\ (2w:word32) <> 14w /\
  (6w:word32) <> 10w /\ (6w:word32) <> 14w /\ (10w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 7w /\ (3w:word32) <> 11w /\ (3w:word32) <> 15w /\
  (7w:word32) <> 11w /\ (7w:word32) <> 15w /\ (11w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 4w /\ (0w:word32) <> 8w /\ (0w:word32) <> 12w /\
  (4w:word32) <> 8w /\ (4w:word32) <> 12w /\ (8w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 5w /\ (1w:word32) <> 9w /\ (1w:word32) <> 13w /\
  (5w:word32) <> 9w /\ (5w:word32) <> 13w /\ (9w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 6w /\ (2w:word32) <> 10w /\ (2w:word32) <> 14w /\
  (6w:word32) <> 10w /\ (6w:word32) <> 14w /\ (10w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 7w /\ (3w:word32) <> 11w /\ (3w:word32) <> 15w /\
  (7w:word32) <> 11w /\ (7w:word32) <> 15w /\ (11w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 4w /\ (0w:word32) <> 8w /\ (0w:word32) <> 12w /\
  (4w:word32) <> 8w /\ (4w:word32) <> 12w /\ (8w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 5w /\ (1w:word32) <> 9w /\ (1w:word32) <> 13w /\
  (5w:word32) <> 9w /\ (5w:word32) <> 13w /\ (9w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 6w /\ (2w:word32) <> 10w /\ (2w:word32) <> 14w /\
  (6w:word32) <> 10w /\ (6w:word32) <> 14w /\ (10w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 7w /\ (3w:word32) <> 11w /\ (3w:word32) <> 15w /\
  (7w:word32) <> 11w /\ (7w:word32) <> 15w /\ (11w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 4w /\ (0w:word32) <> 8w /\ (0w:word32) <> 12w /\
  (4w:word32) <> 8w /\ (4w:word32) <> 12w /\ (8w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 5w /\ (1w:word32) <> 9w /\ (1w:word32) <> 13w /\
  (5w:word32) <> 9w /\ (5w:word32) <> 13w /\ (9w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 6w /\ (2w:word32) <> 10w /\ (2w:word32) <> 14w /\
  (6w:word32) <> 10w /\ (6w:word32) <> 14w /\ (10w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 7w /\ (3w:word32) <> 11w /\ (3w:word32) <> 15w /\
  (7w:word32) <> 11w /\ (7w:word32) <> 15w /\ (11w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs]
]
QED

val _ = export_theory ();
