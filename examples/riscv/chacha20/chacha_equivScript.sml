open HolKernel boolLib Parse bossLib;

open pairTheory pred_setTheory markerTheory wordsTheory wordsLib;

open chachaTheory;

val _ = new_theory "chacha_equiv";

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

Theorem chacha_column_round_imp_exprs[local]:
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

Theorem chacha_column_round_exprs_imp[local]:
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

  (chacha_column_round m 0w = post_arr_0_val /\
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
  chacha_column_round m 15w = post_arr_15_val) ==>

  (chacha_column_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val))
Proof
 once_rewrite_tac [chacha_column_round,chacha_column_round_exprs_def] >>

 rw [] >> fs [] >>

 Cases_on `chacha_quarter_round_exprs (m 3w) (m 7w) (m 11w) (m 15w)` >>
 rename1 `chacha_quarter_round_exprs (m 3w) (m 7w) (m 11w) (m 15w) = (a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3)` >>

 Cases_on `chacha_quarter_round_exprs (m 2w) (m 6w) (m 10w) (m 14w)` >>
 rename1 `chacha_quarter_round_exprs (m 2w) (m 6w) (m 10w) (m 14w) = (a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,a6,a7)` >>

 Cases_on `chacha_quarter_round_exprs (m 1w) (m 5w) (m 9w) (m 13w)` >>
 rename1 `chacha_quarter_round_exprs (m 1w) (m 5w) (m 9w) (m 13w) = (a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,a10,a11)` >>

 Cases_on `chacha_quarter_round_exprs (m 0w) (m 4w) (m 8w) (m 12w)` >>
 rename1 `chacha_quarter_round_exprs (m 0w) (m 4w) (m 8w) (m 12w) = (a12,rest)` >>
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

Theorem chacha_column_round_exprs_eq:
 !m
  pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val

  post_arr_0_val post_arr_1_val post_arr_2_val post_arr_3_val post_arr_4_val post_arr_5_val
  post_arr_6_val post_arr_7_val post_arr_8_val post_arr_9_val post_arr_10_val post_arr_11_val
  post_arr_12_val post_arr_13_val post_arr_14_val post_arr_15_val.

  m 0w = pre_arr_0_val /\ m 1w = pre_arr_1_val /\ m 2w = pre_arr_2_val /\ m 3w = pre_arr_3_val /\
  m 4w = pre_arr_4_val /\ m 5w = pre_arr_5_val /\ m 6w = pre_arr_6_val /\ m 7w = pre_arr_7_val /\
  m 8w = pre_arr_8_val /\ m 9w = pre_arr_9_val /\ m 10w = pre_arr_10_val /\ m 11w = pre_arr_11_val /\
  m 12w = pre_arr_12_val /\ m 13w = pre_arr_13_val /\ m 14w = pre_arr_14_val /\ m 15w = pre_arr_15_val ==>

  ((chacha_column_round m 0w = post_arr_0_val /\
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
  chacha_column_round m 15w = post_arr_15_val)
  <=>
  (chacha_column_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)))
Proof
 METIS_TAC [chacha_column_round_exprs_imp,chacha_column_round_imp_exprs]
QED

Theorem chacha_diagonal_round_imp_exprs[local]:
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

  (chacha_diagonal_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)) ==>

  chacha_diagonal_round m 0w = post_arr_0_val /\
  chacha_diagonal_round m 1w = post_arr_1_val /\
  chacha_diagonal_round m 2w = post_arr_2_val /\
  chacha_diagonal_round m 3w = post_arr_3_val /\
  chacha_diagonal_round m 4w = post_arr_4_val /\
  chacha_diagonal_round m 5w = post_arr_5_val /\
  chacha_diagonal_round m 6w = post_arr_6_val /\
  chacha_diagonal_round m 7w = post_arr_7_val /\
  chacha_diagonal_round m 8w = post_arr_8_val /\
  chacha_diagonal_round m 9w = post_arr_9_val /\
  chacha_diagonal_round m 10w = post_arr_10_val /\
  chacha_diagonal_round m 11w = post_arr_11_val /\
  chacha_diagonal_round m 12w = post_arr_12_val /\
  chacha_diagonal_round m 13w = post_arr_13_val /\
  chacha_diagonal_round m 14w = post_arr_14_val /\
  chacha_diagonal_round m 15w = post_arr_15_val
Proof
 once_rewrite_tac [chacha_diagonal_round,chacha_diagonal_round_exprs_def] >>

 rw [] >> fs [] >>

 Cases_on `chacha_quarter_round_exprs (m 3w) (m 4w) (m 9w) (m 14w)` >>
 rename1 `(a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3)` >>

 Cases_on `chacha_quarter_round_exprs (m 2w) (m 7w) (m 8w) (m 13w)` >>
 rename1 `(a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,a6,a7)` >>

 Cases_on `chacha_quarter_round_exprs (m 1w) (m 6w) (m 11w) (m 12w)` >>
 rename1 `(a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,a10,a11)` >>

 Cases_on `chacha_quarter_round_exprs (m 0w) (m 5w) (m 10w) (m 15w)` >>
 rename1 `(a12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,a14,a15)` >>

 fs [] >> rw [] >>

 rw [chacha_quarter_round_neq_eq] >| [

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],
 
 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs]
]
QED

Theorem chacha_diagonal_round_exprs_imp[local]:
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

  (chacha_diagonal_round m 0w = post_arr_0_val /\
  chacha_diagonal_round m 1w = post_arr_1_val /\
  chacha_diagonal_round m 2w = post_arr_2_val /\
  chacha_diagonal_round m 3w = post_arr_3_val /\
  chacha_diagonal_round m 4w = post_arr_4_val /\
  chacha_diagonal_round m 5w = post_arr_5_val /\
  chacha_diagonal_round m 6w = post_arr_6_val /\
  chacha_diagonal_round m 7w = post_arr_7_val /\
  chacha_diagonal_round m 8w = post_arr_8_val /\
  chacha_diagonal_round m 9w = post_arr_9_val /\
  chacha_diagonal_round m 10w = post_arr_10_val /\
  chacha_diagonal_round m 11w = post_arr_11_val /\
  chacha_diagonal_round m 12w = post_arr_12_val /\
  chacha_diagonal_round m 13w = post_arr_13_val /\
  chacha_diagonal_round m 14w = post_arr_14_val /\
  chacha_diagonal_round m 15w = post_arr_15_val) ==>

  (chacha_diagonal_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val))
Proof
 once_rewrite_tac [chacha_diagonal_round,chacha_diagonal_round_exprs_def] >>

 rw [] >> fs [] >>

 Cases_on `chacha_quarter_round_exprs (m 3w) (m 4w) (m 9w) (m 14w)` >>
 rename1 `chacha_quarter_round_exprs (m 3w) (m 4w) (m 9w) (m 14w) = (a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3)` >>

 Cases_on `chacha_quarter_round_exprs (m 2w) (m 7w) (m 8w) (m 13w)` >>
 rename1 `chacha_quarter_round_exprs (m 2w) (m 7w) (m 8w) (m 13w) = (a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a4,a5,a6,a7)` >>

 Cases_on `chacha_quarter_round_exprs (m 1w) (m 6w) (m 11w) (m 12w)` >>
 rename1 `chacha_quarter_round_exprs (m 1w) (m 6w) (m 11w) (m 12w) = (a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a8,a9,a10,a11)` >>

 Cases_on `chacha_quarter_round_exprs (m 0w) (m 5w) (m 10w) (m 15w)` >>
 rename1 `chacha_quarter_round_exprs (m 0w) (m 5w) (m 10w) (m 15w) = (a12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a12,a13,a14,a15)` >>

 fs [] >> rw [] >>

 rw [chacha_quarter_round_neq_eq] >| [

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(1w:word32) <> 6w /\ (1w:word32) <> 11w /\ (1w:word32) <> 12w /\
  (6w:word32) <> 11w /\ (6w:word32) <> 12w /\ (11w:word32) <> 12w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >>
 `(2w:word32) <> 7w /\ (2w:word32) <> 8w /\ (2w:word32) <> 13w /\
  (7w:word32) <> 8w /\ (7w:word32) <> 13w /\ (8w:word32) <> 13w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],

 rw [chacha_quarter_round_eq_neq] >> 
 `(3w:word32) <> 4w /\ (3w:word32) <> 9w /\ (3w:word32) <> 14w /\
  (4w:word32) <> 9w /\ (4w:word32) <> 14w /\ (9w:word32) <> 14w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs],
 
 `(0w:word32) <> 5w /\ (0w:word32) <> 10w /\ (0w:word32) <> 15w /\
  (5w:word32) <> 10w /\ (5w:word32) <> 15w /\ (10w:word32) <> 15w`
 by rw [] >>
 METIS_TAC [chacha_quarter_round_eq_exprs]
]
QED

Theorem chacha_diagonal_round_exprs_eq:
 !m
  pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val

  post_arr_0_val post_arr_1_val post_arr_2_val post_arr_3_val post_arr_4_val post_arr_5_val
  post_arr_6_val post_arr_7_val post_arr_8_val post_arr_9_val post_arr_10_val post_arr_11_val
  post_arr_12_val post_arr_13_val post_arr_14_val post_arr_15_val.

  m 0w = pre_arr_0_val /\ m 1w = pre_arr_1_val /\ m 2w = pre_arr_2_val /\ m 3w = pre_arr_3_val /\
  m 4w = pre_arr_4_val /\ m 5w = pre_arr_5_val /\ m 6w = pre_arr_6_val /\ m 7w = pre_arr_7_val /\
  m 8w = pre_arr_8_val /\ m 9w = pre_arr_9_val /\ m 10w = pre_arr_10_val /\ m 11w = pre_arr_11_val /\
  m 12w = pre_arr_12_val /\ m 13w = pre_arr_13_val /\ m 14w = pre_arr_14_val /\ m 15w = pre_arr_15_val ==>

  ((chacha_diagonal_round m 0w = post_arr_0_val /\
  chacha_diagonal_round m 1w = post_arr_1_val /\
  chacha_diagonal_round m 2w = post_arr_2_val /\
  chacha_diagonal_round m 3w = post_arr_3_val /\
  chacha_diagonal_round m 4w = post_arr_4_val /\
  chacha_diagonal_round m 5w = post_arr_5_val /\
  chacha_diagonal_round m 6w = post_arr_6_val /\
  chacha_diagonal_round m 7w = post_arr_7_val /\
  chacha_diagonal_round m 8w = post_arr_8_val /\
  chacha_diagonal_round m 9w = post_arr_9_val /\
  chacha_diagonal_round m 10w = post_arr_10_val /\
  chacha_diagonal_round m 11w = post_arr_11_val /\
  chacha_diagonal_round m 12w = post_arr_12_val /\
  chacha_diagonal_round m 13w = post_arr_13_val /\
  chacha_diagonal_round m 14w = post_arr_14_val /\
  chacha_diagonal_round m 15w = post_arr_15_val)
  <=>
  (chacha_diagonal_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)))
Proof
 METIS_TAC [chacha_diagonal_round_exprs_imp,chacha_diagonal_round_imp_exprs]
QED

Theorem chacha_double_round_exprs_imp[local]:
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

 (chacha_double_round m 0w = post_arr_0_val /\
  chacha_double_round m 1w = post_arr_1_val /\
  chacha_double_round m 2w = post_arr_2_val /\
  chacha_double_round m 3w = post_arr_3_val /\
  chacha_double_round m 4w = post_arr_4_val /\
  chacha_double_round m 5w = post_arr_5_val /\
  chacha_double_round m 6w = post_arr_6_val /\
  chacha_double_round m 7w = post_arr_7_val /\
  chacha_double_round m 8w = post_arr_8_val /\
  chacha_double_round m 9w = post_arr_9_val /\
  chacha_double_round m 10w = post_arr_10_val /\
  chacha_double_round m 11w = post_arr_11_val /\
  chacha_double_round m 12w = post_arr_12_val /\
  chacha_double_round m 13w = post_arr_13_val /\
  chacha_double_round m 14w = post_arr_14_val /\
  chacha_double_round m 15w = post_arr_15_val) ==>

  (chacha_double_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val))
Proof
 once_rewrite_tac [chacha_double_round,chacha_double_round_exprs_def] >>

 rw [] >> fs [] >>

 Cases_on `chacha_column_round_exprs (m 0w) (m 1w) (m 2w) (m 3w) (m 4w) (m 5w)
  (m 6w) (m 7w) (m 8w) (m 9w) (m 10w) (m 11w) (m 12w) (m 13w) (m 14w) (m 15w)` >>
 rename1 `(a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15)` >>

 fs [] >>

 Cases_on `chacha_diagonal_round_exprs a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15` >>

 rename1 `chacha_diagonal_round_exprs a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = (a'0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,a'13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,a'13,a'14,a'15)` >>

 fs [] >>

 `chacha_column_round m 0w = a0 /\
  chacha_column_round m 1w = a1 /\
  chacha_column_round m 2w = a2 /\
  chacha_column_round m 3w = a3 /\
  chacha_column_round m 4w = a4 /\
  chacha_column_round m 5w = a5 /\
  chacha_column_round m 6w = a6 /\
  chacha_column_round m 7w = a7 /\
  chacha_column_round m 8w = a8 /\
  chacha_column_round m 9w = a9 /\
  chacha_column_round m 10w = a10 /\
  chacha_column_round m 11w = a11 /\
  chacha_column_round m 12w = a12 /\
  chacha_column_round m 13w = a13 /\
  chacha_column_round m 14w = a14 /\
  chacha_column_round m 15w = a15`
  by METIS_TAC [chacha_column_round_exprs_eq] >>

 METIS_TAC [chacha_diagonal_round_exprs_eq]
QED

Theorem chacha_double_round_imp_exprs[local]:
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

  (chacha_double_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)) ==>

 (chacha_double_round m 0w = post_arr_0_val /\
  chacha_double_round m 1w = post_arr_1_val /\
  chacha_double_round m 2w = post_arr_2_val /\
  chacha_double_round m 3w = post_arr_3_val /\
  chacha_double_round m 4w = post_arr_4_val /\
  chacha_double_round m 5w = post_arr_5_val /\
  chacha_double_round m 6w = post_arr_6_val /\
  chacha_double_round m 7w = post_arr_7_val /\
  chacha_double_round m 8w = post_arr_8_val /\
  chacha_double_round m 9w = post_arr_9_val /\
  chacha_double_round m 10w = post_arr_10_val /\
  chacha_double_round m 11w = post_arr_11_val /\
  chacha_double_round m 12w = post_arr_12_val /\
  chacha_double_round m 13w = post_arr_13_val /\
  chacha_double_round m 14w = post_arr_14_val /\
  chacha_double_round m 15w = post_arr_15_val)
Proof
 once_rewrite_tac [chacha_double_round,chacha_double_round_exprs_def] >>

 fs [] >>

 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> 

 Cases_on `chacha_column_round_exprs (m 0w) (m 1w) (m 2w) (m 3w) (m 4w) (m 5w)
  (m 6w) (m 7w) (m 8w) (m 9w) (m 10w) (m 11w) (m 12w) (m 13w) (m 14w) (m 15w)` >>
 rename1 `(a0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15)` >>

 fs [] >>

 Cases_on `chacha_diagonal_round_exprs a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15` >>

 rename1 `chacha_diagonal_round_exprs a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = (a'0,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,a'13,rest)` >>
 Cases_on `rest` >>
 rename1 `(a'0,a'1,a'2,a'3,a'4,a'5,a'6,a'7,a'8,a'9,a'10,a'11,a'12,a'13,a'14,a'15)` >>

 fs [] >> 

 `chacha_column_round m 0w = a0 /\
  chacha_column_round m 1w = a1 /\
  chacha_column_round m 2w = a2 /\
  chacha_column_round m 3w = a3 /\
  chacha_column_round m 4w = a4 /\
  chacha_column_round m 5w = a5 /\
  chacha_column_round m 6w = a6 /\
  chacha_column_round m 7w = a7 /\
  chacha_column_round m 8w = a8 /\
  chacha_column_round m 9w = a9 /\
  chacha_column_round m 10w = a10 /\
  chacha_column_round m 11w = a11 /\
  chacha_column_round m 12w = a12 /\
  chacha_column_round m 13w = a13 /\
  chacha_column_round m 14w = a14 /\
  chacha_column_round m 15w = a15`
  by METIS_TAC [chacha_column_round_exprs_eq] >>

 METIS_TAC [chacha_diagonal_round_exprs_eq]
QED

Theorem chacha_double_round_exprs_eq:
  !m
  pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val

  post_arr_0_val post_arr_1_val post_arr_2_val post_arr_3_val post_arr_4_val post_arr_5_val
  post_arr_6_val post_arr_7_val post_arr_8_val post_arr_9_val post_arr_10_val post_arr_11_val
  post_arr_12_val post_arr_13_val post_arr_14_val post_arr_15_val.

  m 0w = pre_arr_0_val /\ m 1w = pre_arr_1_val /\ m 2w = pre_arr_2_val /\ m 3w = pre_arr_3_val /\
  m 4w = pre_arr_4_val /\ m 5w = pre_arr_5_val /\ m 6w = pre_arr_6_val /\ m 7w = pre_arr_7_val /\
  m 8w = pre_arr_8_val /\ m 9w = pre_arr_9_val /\ m 10w = pre_arr_10_val /\ m 11w = pre_arr_11_val /\
  m 12w = pre_arr_12_val /\ m 13w = pre_arr_13_val /\ m 14w = pre_arr_14_val /\ m 15w = pre_arr_15_val ==>

((chacha_double_round m 0w = post_arr_0_val /\
  chacha_double_round m 1w = post_arr_1_val /\
  chacha_double_round m 2w = post_arr_2_val /\
  chacha_double_round m 3w = post_arr_3_val /\
  chacha_double_round m 4w = post_arr_4_val /\
  chacha_double_round m 5w = post_arr_5_val /\
  chacha_double_round m 6w = post_arr_6_val /\
  chacha_double_round m 7w = post_arr_7_val /\
  chacha_double_round m 8w = post_arr_8_val /\
  chacha_double_round m 9w = post_arr_9_val /\
  chacha_double_round m 10w = post_arr_10_val /\
  chacha_double_round m 11w = post_arr_11_val /\
  chacha_double_round m 12w = post_arr_12_val /\
  chacha_double_round m 13w = post_arr_13_val /\
  chacha_double_round m 14w = post_arr_14_val /\
  chacha_double_round m 15w = post_arr_15_val)
  <=>
  (chacha_double_round_exprs pre_arr_0_val pre_arr_1_val pre_arr_2_val pre_arr_3_val pre_arr_4_val pre_arr_5_val
  pre_arr_6_val pre_arr_7_val pre_arr_8_val pre_arr_9_val pre_arr_10_val pre_arr_11_val
  pre_arr_12_val pre_arr_13_val pre_arr_14_val pre_arr_15_val =
   (post_arr_0_val, post_arr_1_val, post_arr_2_val, post_arr_3_val, post_arr_4_val, post_arr_5_val,
    post_arr_6_val, post_arr_7_val, post_arr_8_val, post_arr_9_val, post_arr_10_val, post_arr_11_val,
    post_arr_12_val, post_arr_13_val, post_arr_14_val, post_arr_15_val)))
Proof
 METIS_TAC [chacha_double_round_exprs_imp,chacha_double_round_imp_exprs]
QED

val _ = export_theory ();
