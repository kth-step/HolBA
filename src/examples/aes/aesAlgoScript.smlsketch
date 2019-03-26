open wordsTheory;

val _ = new_theory "aes";

val _ = type_abbrev("aes_state_t", ``:((bool[2]) # (bool[2])) -> (bool[8])``);

val aes_box_def = Define `
aes_box (x:bool[8]) =
 x+1
`;

val aes_sub_bytes_def = Define `
  aes_sub_bytes s = 
    \x. (aes_box (s x))
`;

val aes_shift_row_def = Define `
  aes_shift_row s =
   \(x,y). s (x + y, y)
`;


val aes_round_def = Define `
aes_round (s:aes_state_t, i:word32, key:word32) =
((\(x,y).s ((x+y), y)), i+1w, key)
`;

EVAL ``aes_round (s,0w,0w)``;

val aes_sim_relation_def = Define `
aes_sim_relation b a =
(b.R0 = a.i) /\
(b.mem[key_add] = a.key[0]) /\
(b.mem[key_add+1] = a.key[1]) /\
(b.mem[key_add+2] = a.key[2]) /\
(b.mem[key_add+3] = a.key[3]) /\
!x y.
(b.mem[state_add + x + y*4] = a.s[x,y]
`;

val goal_def = Define `
! b a.
aes_sim_relation b a ==>
b' = ARM_exec_to_adr b ==>
a' = aes_round a ==>
aes_sim_relation b' a'
`;

val goal_bir_def = Define `
! c a.
aes_bir_sim_relation c a ==>
c' = BIR_exec_to_label c ==>
a' = aes_round a ==>
aes_bir_sim_relation c' a'
`;

val goal_from_bir_to_arm_def = Define `
! b a.
aes_sim_relation b a ==>
bir_lifter_sim_relation b c ==>
aes_bir_sim_relation c a
`;

val goal_from_bir_to_arm2_def = Define `
! b a.
aes_bir_sim_relation c' a' ==>
bir_lifter_sim_relation b' c' ==>
aes_sim_relation b' a'
`;




val _ = export_theory();
