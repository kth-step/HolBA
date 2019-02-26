open HolKernel Parse boolLib bossLib;
open bir_programTheory;
open bir_immTheory;
open HolBACoreSimps
open ASCIInumbersTheory listTheory

val _ = new_theory "bir_program_labels";

(* This theory reasons about the labels of a program *)


(*************************)
(* immediates to strings *)
(*************************)

(* In order to construct string labels corresponding to address labels below,
   we need to convert BIR immediates to strings and back. This is implemented by
   b2s and s2b *)

val num_to_hex_string_fix_width_def = Define
`num_to_hex_string_fix_width w n =
  let s = num_to_hex_string n in
  "0x" ++ (if LENGTH s < w then APPEND (REPLICATE (w - LENGTH s) #"0") s else s)`

val LENGTH_num_to_hex_string = store_thm (
  "LENGTH_num_to_hex_string",
``LENGTH (num_to_hex_string n) = (if n = 0 then 1 else SUC (LOG 16 n))``,
SIMP_TAC list_ss [num_to_hex_string_def, n2s_def, numposrepTheory.LENGTH_n2l]);


val LENGTH_num_to_hex_string_fixwidth = store_thm ("LENGTH_num_to_hex_string_fixwidth",
``!w n. (0 < w /\ n < 16 ** w) ==>
        (LENGTH (num_to_hex_string_fix_width w n) = w+2)``,

REPEAT STRIP_TAC >>
SIMP_TAC list_ss [num_to_hex_string_fix_width_def, LET_DEF] >>
`LENGTH (num_to_hex_string n) <= w` by (
  Cases_on `n = 0` >> (
    ASM_SIMP_TAC arith_ss [LENGTH_num_to_hex_string]
  ) >>
  `LOG 16 n <= LOG 16 (16 ** w * 1)` by (
     IRULE_TAC logrootTheory.LOG_LE_MONO >>
     ASM_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC std_ss [logrootTheory.LOG_EXP, logrootTheory.LOG_1] >>

  Cases_on `LOG 16 n = w` >> FULL_SIMP_TAC arith_ss [] >>
  MP_TAC (Q.SPECL [`16`, `n`] logrootTheory.LOG) >>
  FULL_SIMP_TAC arith_ss []
) >>
Cases_on `LENGTH (num_to_hex_string n) = w` >- (
  ASM_SIMP_TAC arith_ss []
) >>
FULL_SIMP_TAC list_ss [rich_listTheory.LENGTH_REPLICATE]);


val MEM_REPLICATE_EQ = store_thm ("MEM_REPLICATE_EQ",
``!x y n. MEM x (REPLICATE n y) <=> ((0 < n) /\ (x = y))``,
Induct_on `n` >> ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [rich_listTheory.REPLICATE]);


val num_from_hex_string_fix_width = store_thm ("num_from_hex_string_fix_width",
``!w n. num_from_hex_string (DROP 2 (num_to_hex_string_fix_width w n)) = n``,

REPEAT GEN_TAC >>
`(num_from_hex_string ∘ num_to_hex_string) n = I n` by REWRITE_TAC [num_hex_string] >>
FULL_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [num_to_hex_string_fix_width_def, LET_DEF, combinTheory.o_DEF] >>

FULL_SIMP_TAC list_ss [num_from_hex_string_def, s2n_def] >>
FULL_SIMP_TAC std_ss [Once (GSYM numposrepTheory.l2n_dropWhile_0)] >>
FULL_SIMP_TAC list_ss [rich_listTheory.MAP_REVERSE] >>

`EVERY ($= 0) (MAP UNHEX (REPLICATE (w − STRLEN (num_to_hex_string n)) #"0"))`
  suffices_by FULL_SIMP_TAC list_ss [listTheory.dropWhile_APPEND_EVERY] >>

SIMP_TAC list_ss [EVERY_MEM, MEM_MAP, PULL_EXISTS, MEM_REPLICATE_EQ,
  UNHEX_def]);

val num_to_hex_string_PREFIX = store_thm ("num_to_hex_string_PREFIX",
``!w n. TAKE 2 (num_to_hex_string_fix_width w n) = "0x"``,
SIMP_TAC list_ss [num_to_hex_string_fix_width_def, LET_DEF]);



val b2s_def = Define `
  (b2s ( Imm1   w ) = num_to_hex_string_fix_width 1  (w2n w)) /\
  (b2s ( Imm8   w ) = num_to_hex_string_fix_width 2  (w2n w)) /\
  (b2s ( Imm16  w ) = num_to_hex_string_fix_width 4  (w2n w)) /\
  (b2s ( Imm32  w ) = num_to_hex_string_fix_width 8  (w2n w)) /\
  (b2s ( Imm64  w ) = num_to_hex_string_fix_width 16 (w2n w)) /\
  (b2s ( Imm128 w ) = num_to_hex_string_fix_width 32 (w2n w))
`;


val s2b_def = Define `s2b s =
  if (TAKE 2 s <> "0x") then NONE else
  (let n = num_from_hex_string (DROP 2 s) in
  (case (LENGTH s) of
      3 => SOME (n2bs n Bit1)
    | 4 => SOME (n2bs n Bit8)
    | 6 => SOME (n2bs n Bit16)
    | 10 => SOME (n2bs n Bit32)
    | 18 => SOME (n2bs n Bit64)
    | 34 => SOME (n2bs n Bit128)
    | _ => NONE))`


val LENGTH_b2s = store_thm ("LENGTH_b2s",
``!i. LENGTH (b2s i) = case type_of_bir_imm i of
     Bit1   => 3
   | Bit8   => 4
   | Bit16  => 6
   | Bit32  => 10
   | Bit64  => 18
   | Bit128 => 34``,

Cases >> (
  ASM_SIMP_TAC (arith_ss++bir_TYPES_ss) [b2s_def, type_of_bir_imm_def]
) >| [
  MP_TAC (Q.SPEC `1` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:1``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [],

  MP_TAC (Q.SPEC `2` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:8``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [],

  MP_TAC (Q.SPEC `4` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:16``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [],

  MP_TAC (Q.SPEC `8` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:32``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [],

  MP_TAC (Q.SPEC `16` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:64``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [],

  MP_TAC (Q.SPEC `32` LENGTH_num_to_hex_string_fixwidth) >>
  MP_TAC (Q.SPEC `c` (INST_TYPE [``:'a`` |-> ``:128``] wordsTheory.w2n_lt)) >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) []
])

val s2b_b2s = store_thm ("s2b_b2s",
``!b. s2b (b2s b) = SOME b``,

SIMP_TAC std_ss [s2b_def, LENGTH_b2s] >>
Cases >> (
  SIMP_TAC (std_ss++bir_TYPES_ss) [type_of_bir_imm_def,
    b2s_def, num_from_hex_string_fix_width, LET_DEF, n2bs_def,
    wordsTheory.n2w_w2n, num_to_hex_string_PREFIX]
));

val b2s_11 = store_thm ("b2s_11",
``!b1 b2. (b2s b1 = b2s b2) <=> (b1 = b2)``,
METIS_TAC[s2b_b2s, optionTheory.SOME_11])

val num_to_hex_string_CHARS = store_thm ("num_to_hex_string_CHARS",
``!n c. MEM c (num_to_hex_string n) ==> MEM c [
     #"0"; #"1"; #"2"; #"3"; #"4"; #"5"; #"6";
     #"7"; #"8"; #"9"; #"A"; #"B"; #"C"; #"D"; #"E";  #"F"]``,

SIMP_TAC list_ss [num_to_hex_string_def, n2s_def, MEM_MAP, PULL_EXISTS] >>
REPEAT STRIP_TAC >>
rename1 `HEX y` >>

`MEM y (COUNT_LIST 16)` by (
  MP_TAC (Q.SPECL [`16`, `n`] numposrepTheory.n2l_BOUND) >>
  ASM_SIMP_TAC std_ss [EVERY_MEM, arithmeticTheory.GREATER_DEF,
    rich_listTheory.MEM_COUNT_LIST]
) >>
FULL_SIMP_TAC std_ss [rich_listTheory.COUNT_LIST_compute,
  rich_listTheory.COUNT_LIST_AUX_def_compute] >>
FULL_SIMP_TAC std_ss [MEM, HEX_def]);


val num_to_hex_string_fix_width_CHARS = store_thm ("num_to_hex_string_fix_width_CHARS",
``!n w c. MEM c (num_to_hex_string_fix_width w n) ==> MEM c [
     #"x"; #"0"; #"1"; #"2"; #"3"; #"4"; #"5"; #"6";
     #"7"; #"8"; #"9"; #"A"; #"B"; #"C"; #"D"; #"E";  #"F"]``,

REPEAT GEN_TAC >>
MP_TAC (Q.SPECL [`n`, `c`] num_to_hex_string_CHARS) >>
SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [num_to_hex_string_fix_width_def, LET_DEF,
  MEM_REPLICATE_EQ] >>
REPEAT STRIP_TAC >>
Cases_on `LENGTH (num_to_hex_string n) < w` >> (
  FULL_SIMP_TAC std_ss []
));


val b2s_CHARS = store_thm ("b2s_CHARS",
``!b c. MEM c (b2s b) ==> MEM c [
     #"x"; #"0"; #"1"; #"2"; #"3"; #"4"; #"5"; #"6";
     #"7"; #"8"; #"9"; #"A"; #"B"; #"C"; #"D"; #"E";  #"F"]``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC num_to_hex_string_fix_width_CHARS >>
Cases_on `b` >> (
  FULL_SIMP_TAC std_ss [b2s_def] >>
  METIS_TAC[]
));



(********************************)
(* Labels for adresses + string *)
(********************************)

val BL_Label_of_addr_def = Define `BL_Label_of_addr (i:bir_imm_t) s =
  BL_Label (STRCAT (b2s i) (#"_"::s))`

val bir_immediate_of_label_string_def = Define `
   bir_immediate_of_label_string s =
   case INDEX_OF #"_" s of
      NONE => NONE
    | SOME i => s2b (TAKE i s)`


val INDEX_OF_b2s_STRCAT = prove (
  ``!b s. INDEX_OF #"_" (STRCAT (b2s b) (STRING #"_" s)) = SOME (LENGTH (b2s b))``,

SIMP_TAC (list_ss++QI_ss) [INDEX_OF_def, bir_auxiliaryTheory.INDEX_FIND_EQ_SOME] >>
SIMP_TAC list_ss [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2] >>
REPEAT STRIP_TAC >>
`MEM #"_" (b2s b)` by METIS_TAC[MEM_EL] >>
Q.PAT_X_ASSUM `#"_" = _` (K ALL_TAC) >>
MP_TAC (Q.SPECL [`b`, `#"_"`] b2s_CHARS) >>
ASM_SIMP_TAC (list_ss++stringSimps.STRING_ss) []);


val BL_Label_of_addr_SPLIT = store_thm ("BL_Label_of_addr_SPLIT",
``!b s s'. (BL_Label_of_addr b s' = BL_Label s) <=>
           (?i. (INDEX_OF #"_" s = SOME i) /\
                (TAKE i s = b2s b) /\
                (DROP (SUC i) s = s'))``,

SIMP_TAC (list_ss++bir_TYPES_ss) [BL_Label_of_addr_def] >>
REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC >- (
  BasicProvers.VAR_EQ_TAC >>
  SIMP_TAC list_ss [INDEX_OF_b2s_STRCAT, rich_listTheory.TAKE_LENGTH_APPEND,
    rich_listTheory.DROP_APPEND2, GSYM arithmeticTheory.ADD1]
) >- (
  SUBST1_TAC (GSYM (ISPECL [``i:num``, ``s:string``] TAKE_DROP)) >>
  ASM_REWRITE_TAC[listTheory.APPEND_11] >>

  FULL_SIMP_TAC (std_ss++QI_ss) [INDEX_OF_def,
    bir_auxiliaryTheory.INDEX_FIND_EQ_SOME] >>
  REPEAT BasicProvers.VAR_EQ_TAC >>
  ASM_SIMP_TAC list_ss [rich_listTheory.DROP_CONS_EL]
));


val bir_immediate_of_label_string_THM = store_thm ("bir_immediate_of_label_string_THM",
``!b s' s. (BL_Label_of_addr b s' = BL_Label s) ==>
           (bir_immediate_of_label_string s = SOME b)``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`b`, `s`, `s'`] BL_Label_of_addr_SPLIT) >>
FULL_SIMP_TAC std_ss [bir_immediate_of_label_string_def, PULL_EXISTS, s2b_b2s]);


val BL_Label_of_addr_11 = store_thm ("BL_Label_of_addr_11",
``!b1 b2 s1 s2. (BL_Label_of_addr b1 s1 = BL_Label_of_addr b2 s2) <=> ((b1 = b2) /\ (s1 = s2))``,

REPEAT STRIP_TAC >> Tactical.REVERSE EQ_TAC >- METIS_TAC[] >>
STRIP_TAC >>

`b1 = b2` by (
  MP_TAC (Q.SPECL [`b1`, `s1`] bir_immediate_of_label_string_THM) >>
  MP_TAC (Q.SPECL [`b2`, `s2`] bir_immediate_of_label_string_THM) >>

  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [BL_Label_of_addr_def]
) >>
FULL_SIMP_TAC (list_ss++bir_TYPES_ss) [BL_Label_of_addr_def]);





(****************************************)
(* Labels core hex-codes use the lifter *)
(****************************************)

(* A definition that allows us to attach an extra string to an address label.
   This string carries no information. It is as an annotation by the
   instruction lifter. *)

val BL_Address_HC_def = Define `BL_Address_HC b (hc:string) =
  BL_Address b`



(*******************************)
(* Recognisers and destructors *)
(*******************************)

val IS_BL_Label_def = Define `
  (IS_BL_Label (BL_Label _) = T) /\
  (IS_BL_Label _ = F)`;

val IS_BL_Address_def = Define `
  (IS_BL_Address (BL_Address _) = T) /\
  (IS_BL_Address _ = F)`;

val IS_BL_Address_NOT = store_thm ("IS_BL_Address_NOT",
 ``!l. ~(IS_BL_Address l) <=> IS_BL_Label l``,
Cases >> SIMP_TAC std_ss [IS_BL_Label_def, IS_BL_Address_def])

val IS_BL_Label_NOT = store_thm ("IS_BL_Label_NOT",
 ``!l. ~(IS_BL_Label l) <=> IS_BL_Address l``,
Cases >> SIMP_TAC std_ss [IS_BL_Label_def, IS_BL_Address_def])

val IS_BL_Address_EXISTS = store_thm ("IS_BL_Address_EXISTS",
``!l. IS_BL_Address l <=> ?i. (l = BL_Address i)``,
Cases_on `l` >> SIMP_TAC (std_ss++bir_TYPES_ss) [IS_BL_Address_def]);

val IS_BL_Label_EXISTS = store_thm ("IS_BL_Label_EXISTS",
``!l. IS_BL_Label l <=> ?s. (l = BL_Label s)``,
Cases_on `l` >> SIMP_TAC (std_ss++bir_TYPES_ss) [IS_BL_Label_def]);

val BL_recognisers = store_thm ("BL_recognisers",
``(!l. (IS_BL_Label (BL_Label l))) /\
  (!l. ~(IS_BL_Label (BL_Address l))) /\
  (!b s. (IS_BL_Label (BL_Label_of_addr b s))) /\
  (!l s. ~(IS_BL_Label (BL_Address_HC l s))) /\
  (!l. ~(IS_BL_Address (BL_Label l))) /\
  (!l. (IS_BL_Address (BL_Address l))) /\
  (!b s. ~(IS_BL_Address (BL_Label_of_addr b s))) /\
  (!l s. IS_BL_Address (BL_Address_HC l s))``,

SIMP_TAC std_ss [IS_BL_Label_def, IS_BL_Address_def, BL_Label_of_addr_def,
  BL_Address_HC_def]);


val dest_BL_Label_def = Define `dest_BL_Label (BL_Label l) = l`
val dest_BL_Address_def = Define `dest_BL_Address (BL_Address b) = b`;


val BL_destructors = store_thm ("BL_destructors",
``(!l. dest_BL_Label (BL_Label l) = l) /\
  (!b s. dest_BL_Label (BL_Label_of_addr b s) = (b2s b ++ #"_"::s)) /\
  (!b. dest_BL_Address (BL_Address b) = b) /\
  (!b s. dest_BL_Address (BL_Address_HC b s) = b)``,

SIMP_TAC std_ss [dest_BL_Label_def, BL_Label_of_addr_def,
  dest_BL_Address_def, BL_Address_HC_def]);



(********************************)
(* Labels being nicely arranged *)
(********************************)


val bir_label_addresses_of_program_labels_def = Define `
  bir_label_addresses_of_program_labels l =
   (MAP (b2n o dest_BL_Address) (FILTER IS_BL_Address l))`

val bir_label_addresses_of_program_def = Define `
  bir_label_addresses_of_program p =
  bir_label_addresses_of_program_labels (bir_labels_of_program p)`;

val bir_program_addr_labels_sorted_def = Define `
  bir_program_addr_labels_sorted p <=>
  SORTED $< (bir_label_addresses_of_program p)`


val bir_labels_of_program_REWRS = store_thm ("bir_labels_of_program_REWRS",
``(bir_labels_of_program (BirProgram []) = []) /\
  (!bl bls. bir_labels_of_program (BirProgram (bl::bls)) =
            (bl.bb_label :: bir_labels_of_program (BirProgram bls)))``,
SIMP_TAC list_ss [bir_labels_of_program_def])


val bir_label_addresses_of_program_REWRS = store_thm ("bir_label_addresses_of_program_REWRS",
  ``(bir_label_addresses_of_program_labels [] = []) /\
    (!l ls. (bir_label_addresses_of_program_labels ((BL_Label l)::ls) =
             bir_label_addresses_of_program_labels ls)) /\
    (!l i ls. (bir_label_addresses_of_program_labels ((BL_Label_of_addr i l)::ls) =
               bir_label_addresses_of_program_labels ls)) /\
    (!i ls. (bir_label_addresses_of_program_labels ((BL_Address i)::ls) =
               (b2n i)::(bir_label_addresses_of_program_labels ls))) /\
    (!i s ls. (bir_label_addresses_of_program_labels ((BL_Address_HC i s)::ls) =
               (b2n i)::(bir_label_addresses_of_program_labels ls)))``,

SIMP_TAC list_ss [bir_label_addresses_of_program_labels_def,
  BL_recognisers, BL_destructors]);


val bir_program_string_labels_guarded_def = Define `
    bir_program_string_labels_guarded p <=>
    EVERY (\l. IS_BL_Label l ==> ?i s. (BL_Label_of_addr i s = l) /\
                                       (MEM (BL_Address i) (bir_labels_of_program p)))
      (bir_labels_of_program p)`;


val _ = export_theory();
