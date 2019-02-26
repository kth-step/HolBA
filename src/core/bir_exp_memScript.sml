open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_immSyntax;

val _ = new_theory "bir_exp_mem";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));


(* ------------------------------------------------------------------------- *)
(* Endian for memory                                                         *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_endian_t =
  | BEnd_BigEndian
  | BEnd_LittleEndian
  | BEnd_NoEndian`

val bir_endian_ss = rewrites (type_rws ``:bir_endian_t``);

val fold_bir_endian_THM = store_thm ("fold_bir_endian_THM",
  ``!P. (P BEnd_BigEndian /\ P BEnd_LittleEndian /\ P BEnd_NoEndian) <=> (!en. P en)``,
    SIMP_TAC (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``]) []);

(* ------------------------------------------------------------------------- *)
(*  How many splits are needed                                               *)
(* ------------------------------------------------------------------------- *)

(* given a value- and a result_type, compute how many values are needed to
   form a result. If the length of the result is not devidable by the value size
   return NONE. *)
val bir_number_of_mem_splits_def = Define `bir_number_of_mem_splits
   (value_ty : bir_immtype_t) (result_ty : bir_immtype_t) (a_ty : bir_immtype_t) =
   if ((size_of_bir_immtype result_ty) MOD (size_of_bir_immtype value_ty) = 0) then
      (if ((size_of_bir_immtype result_ty) DIV (size_of_bir_immtype value_ty) <=
           2 ** (size_of_bir_immtype a_ty)) then
        SOME ((size_of_bir_immtype result_ty) DIV (size_of_bir_immtype value_ty))
       else NONE)
   else NONE`;


fun remove_quant_from_thm vn thm = let
  val (vars, _) = strip_forall (concl thm)
  val (v, vars') = Lib.pluck (fn v => fst (dest_var v) = vn) vars
  val thm' = GENL vars' (SPEC_ALL thm)
in
  (v, thm')
end;

val bir_number_of_mem_splits_NEQ_SOME0 = store_thm ("bir_number_of_mem_splits_NEQ_SOME0",
  ``!vt rt at. bir_number_of_mem_splits vt rt at <> SOME 0``,
Cases >> Cases >> Cases >> SIMP_TAC std_ss [bir_number_of_mem_splits_def, size_of_bir_immtype_def]);

val bir_number_of_mem_splits_EQ_SOME1 = store_thm ("bir_number_of_mem_splits_EQ_SOME1",
  ``!vt rt at. (bir_number_of_mem_splits vt rt at = SOME 1) <=> (vt = rt)``,
Cases >> Cases >> Cases >>
  SIMP_TAC (std_ss++bir_imm_ss) [bir_number_of_mem_splits_def, size_of_bir_immtype_def]);

val bir_number_of_mem_splits_ID = store_thm ("bir_number_of_mem_splits_ID",
  ``!rt at. bir_number_of_mem_splits rt rt at = SOME 1``,
SIMP_TAC std_ss [bir_number_of_mem_splits_EQ_SOME1]);


val bir_number_of_mem_splits_REWRS = save_thm ("bir_number_of_mem_splits_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "a_ty" bir_number_of_mem_splits_def

  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    size_of_bir_immtype_def] thm0

  val thm2 = SIMP_RULE (std_ss) [FORALL_AND_THM] (GEN v thm1)

  val thm3 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    size_of_bir_immtype_def] thm2

  val thm3s = CONJUNCTS thm2

  val P_tm = ``\t. (bir_number_of_mem_splits s1 s2 t = X)``
  val thm4 =
      SIMP_RULE std_ss [SIMP_RULE std_ss [] (SPEC P_tm fold_bir_immtype_THM),
        bir_number_of_mem_splits_ID] thm3

  val thm5 = CONJ bir_number_of_mem_splits_ID thm4

  val thm6 = SIMP_RULE std_ss [GSYM CONJ_ASSOC] thm5
in
  thm6
end);




(* ------------------------------------------------------------------------- *)
(*  Loading                                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_mem_concat_def = Define `bir_mem_concat vl rty = v2bs (FLAT vl) rty`

val type_of_bir_mem_concat = store_thm ("type_of_bir_mem_concat",
  ``!vl ty. type_of_bir_imm (bir_mem_concat vl ty) = ty``,
SIMP_TAC std_ss [bir_mem_concat_def, type_of_v2bs]);

val bir_load_bitstring_from_mmap_def = Define `
  bir_load_bitstring_from_mmap value_ty mmap (a:num) =
    fixwidth (size_of_bir_immtype value_ty) (n2v (mmap a))`

val bir_load_bitstring_from_mmap_w2v = store_thm ("bir_load_bitstring_from_mmap_w2v",
  ``!value_ty mmap a. (size_of_bir_immtype value_ty = dimindex (:'a)) ==>
      (bir_load_bitstring_from_mmap value_ty mmap a =
       (w2v ((n2w (mmap a)):'a word)))``,
SIMP_TAC std_ss [bir_load_bitstring_from_mmap_def, GSYM w2v_v2w, v2w_n2v]);


val bir_load_bitstring_from_mmap_w2v_SIZES = save_thm ("bir_load_bitstring_from_mmap_w2v_SIZES",
  LIST_CONJ (MP_size_of_bir_immtype_t_EQ_dimindex bir_load_bitstring_from_mmap_w2v));


val bir_mem_addr_def = Define `
  bir_mem_addr aty a = MOD_2EXP (size_of_bir_immtype aty) a`;


val bir_mem_addr_id = store_thm ("bir_mem_addr_id",
  ``!s a. a < 2 ** size_of_bir_immtype s ==> (bir_mem_addr s a = a)``,
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_mem_addr_def, bitTheory.MOD_2EXP_def]);


val bir_mem_addr_w2n = store_thm ("bir_mem_addr_w2n",
 ``!s. (size_of_bir_immtype s = dimindex (:'a)) ==>
      !c. (bir_mem_addr s (w2n (c:'a word)) = w2n c)``,
GEN_TAC >> STRIP_TAC >>
Cases_on `c` >>
FULL_SIMP_TAC std_ss [bir_mem_addr_def, w2n_n2w, dimword_def, bitTheory.MOD_2EXP_def]);


val bir_mem_addr_w2n_SIZES = save_thm ("bir_mem_addr_w2n_SIZES",
  LIST_CONJ (MP_size_of_bir_immtype_t_EQ_dimindex bir_mem_addr_w2n));


val bir_mem_addr_w2n_add = store_thm ("bir_mem_addr_w2n_add",
 ``!s. (size_of_bir_immtype s = dimindex (:'a)) ==>
      !c n. (bir_mem_addr s (w2n (c:'a word) + n) = w2n (c + n2w n))``,
GEN_TAC >> STRIP_TAC >>
Cases_on `c` >>
ASM_SIMP_TAC std_ss [bir_mem_addr_def, w2n_n2w, wordsTheory.word_add_n2w,
  dimword_def, bitTheory.MOD_2EXP_def]);


val bir_mem_addr_w2n_add_SIZES = save_thm ("bir_mem_addr_w2n_add_SIZES",
  LIST_CONJ (MP_size_of_bir_immtype_t_EQ_dimindex bir_mem_addr_w2n_add));


val bir_load_from_mem_def = Define `bir_load_from_mem
  (value_ty : bir_immtype_t) (result_ty : bir_immtype_t) (a_ty : bir_immtype_t) (mmap : num -> num) (en: bir_endian_t) (a:num) =

   case (bir_number_of_mem_splits value_ty result_ty a_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = MAP (\n. bir_load_bitstring_from_mmap value_ty mmap (bir_mem_addr a_ty (a+n))) (COUNT_LIST n) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in
        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_mem_concat vs'' result_ty)
   )`;

val bir_load_from_mem_SINGLE = store_thm ("bir_load_from_mem_SINGLE",
  ``!en a vty aty mmap. bir_load_from_mem vty vty aty mmap en a =
    SOME (n2bs (mmap (bir_mem_addr aty a)) vty)``,

SIMP_TAC list_ss [bir_load_from_mem_def, bir_number_of_mem_splits_ID, LET_THM,
  rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def] >>
Cases_on `en` >> (
  SIMP_TAC (list_ss++bir_endian_ss) [bir_mem_concat_def, v2bs_fixwidth,
    v2bs_n2v, bir_load_bitstring_from_mmap_def]
));


val bir_load_from_mem_NO_ENDIAN = store_thm ("bir_load_from_mem_NO_ENDIAN",
  ``!a vty rty aty mmap. bir_load_from_mem vty rty aty mmap BEnd_NoEndian a =
    (if vty = rty then
      SOME (n2bs (mmap (bir_mem_addr aty a)) vty)
     else NONE)``,

REPEAT GEN_TAC >>
Cases_on `vty = rty` >> (
  ASM_SIMP_TAC std_ss [bir_load_from_mem_SINGLE]
) >>
`bir_number_of_mem_splits vty rty aty <> SOME 1` by (
  ASM_SIMP_TAC std_ss [bir_number_of_mem_splits_EQ_SOME1]
) >>
Cases_on `bir_number_of_mem_splits vty rty aty` >> (
  FULL_SIMP_TAC (std_ss++bir_endian_ss) [bir_load_from_mem_def, LET_DEF]
));


val bir_load_from_mem_EQ_NONE = store_thm ("bir_load_from_mem_EQ_NONE",
  ``!a en vty rty aty mmap. (bir_load_from_mem vty rty aty mmap en a = NONE) <=>
      ((bir_number_of_mem_splits vty rty aty = NONE) \/
      ((vty <> rty) /\ (en = BEnd_NoEndian)))``,

REPEAT GEN_TAC >>
Q.SUBGOAL_THEN `(vty <> rty) <=> (bir_number_of_mem_splits vty rty aty <> SOME 1)`
  SUBST1_TAC >- (
  SIMP_TAC std_ss [bir_number_of_mem_splits_EQ_SOME1]
) >>
Cases_on `bir_number_of_mem_splits vty rty aty` >> (
  ASM_SIMP_TAC std_ss [bir_load_from_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss) []
) >>
Cases_on `x=1` >> ASM_SIMP_TAC std_ss []);


val bir_load_from_mem_EQ_NONE_IMP = store_thm ("bir_load_from_mem_EQ_NONE_IMP",
  ``!a en vty rty aty mmap.
      ((bir_number_of_mem_splits vty rty aty = NONE) \/
      ((vty <> rty) /\ (en = BEnd_NoEndian))) ==>
      (bir_load_from_mem vty rty aty mmap en a = NONE)``,
METIS_TAC[bir_load_from_mem_EQ_NONE]);


val bir_load_from_mem_EQ_SOME = store_thm ("bir_load_from_mem_EQ_SOME",
  ``!a en vty rty aty mmap res. (bir_load_from_mem vty rty aty mmap en a = SOME res) <=>
      (?n vs vs'. (bir_number_of_mem_splits vty rty aty = SOME n) /\
                  (vs = MAP (\n. bir_load_bitstring_from_mmap vty mmap (bir_mem_addr aty (a+n))) (COUNT_LIST n)) /\
                  ((en = BEnd_BigEndian) /\ (vs' = vs) \/
                   (en = BEnd_LittleEndian) /\ (vs' = REVERSE vs) \/
                   (en = BEnd_NoEndian) /\ (n = 1) /\ (vs' = vs)) /\
                   (res = bir_mem_concat vs' rty))``,

SIMP_TAC std_ss [bir_load_from_mem_def] >>
REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vty rty aty` >> (
  ASM_SIMP_TAC std_ss [LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss++boolSimps.EQUIV_EXTRACT_ss) []
) >>
Cases_on `x=1` >>
ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) []);



val type_of_bir_load_from_mem = store_thm ("type_of_bir_load_from_mem",
  ``!a en vty rty aty mmap res. (bir_load_from_mem vty rty aty mmap en a = SOME res) ==>
      (type_of_bir_imm res = rty)``,

SIMP_TAC std_ss [bir_load_from_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM,
  type_of_bir_mem_concat]);


val bir_load_from_mem_NONE_REWRS = save_thm ("bir_load_from_mem_NONE_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "aty" bir_load_from_mem_EQ_NONE_IMP

  val thm1 = SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] thm0

  val thm2 = SIMP_RULE (std_ss++bir_imm_ss) [GSYM CONJ_ASSOC, FORALL_AND_THM,
     DISJ_IMP_THM] (GEN v thm1)

  val (thm2s1, thm2s2) = partition (is_imp_only o snd o strip_forall o concl) (CONJUNCTS thm2)

  val thm3s1 = map (SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS]) thm2s1


  val thm4 = LIST_CONJ (thm3s1 @ thm2s2)
in thm4 end);


(* One first rewrite *)
val bir_load_from_mem_REWRS0 = save_thm ("bir_load_from_mem_REWRS0",
let
  val (v, thm0) = remove_quant_from_thm "a_ty" bir_load_from_mem_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] thm0
  val (l1, l2) = partition (optionSyntax.is_option_case o rhs o snd o strip_forall o concl) (CONJUNCTS thm1)

  val l1' = map (SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] o (GEN v)) l1

  val thm2 = LIST_CONJ (l2 @ l1')

  val thm3 = SIMP_RULE list_ss [
      rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def, bir_load_bitstring_from_mmap_w2v_SIZES] thm2

  val thm4 = SIMP_RULE (list_ss++bir_endian_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm3

  val thm5 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm4
  val thm6 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] (GEN v thm5)

in thm6
end);

(* And a fancier one *)
val bir_load_from_mem_REWRS = save_thm ("bir_load_from_mem_REWRS",
let
  val thm0 = bir_load_from_mem_REWRS0
  val thm1 = SIMP_RULE (list_ss) [bir_mem_concat_def, v2bs_def, n2bs_def] thm0
  val thm2 = SIMP_RULE std_ss [GSYM listTheory.APPEND_ASSOC] thm1
  val thm3 = REWRITE_RULE [w2v_word_concat_SYM_REWRS] thm2
  val thm4 = REWRITE_RULE [n2w_v2n, v2w_w2v] thm3
in
  thm4
end);


(* Important addresses *)
val bir_load_from_mem_used_addrs_def = Define
  `bir_load_from_mem_used_addrs tv tr ta en a =
   case (bir_number_of_mem_splits tv tr ta) of
    | NONE => {}
    | SOME (n:num) => (if (n <> 1) /\ (en = BEnd_NoEndian) then {} else
        set (MAP (\n. (bir_mem_addr ta (a + n))) (COUNT_LIST n)))`;

val bir_load_from_mem_used_addrs_THM = store_thm ("bir_load_from_mem_used_addrs_THM",
  ``!vt rt at mmap mmap' en a.
      (!addr. addr IN (bir_load_from_mem_used_addrs vt rt at en a) ==>
              (mmap addr = mmap' addr)) ==>
      (bir_load_from_mem vt rt at mmap en a =
       bir_load_from_mem vt rt at mmap' en a)``,

SIMP_TAC std_ss [bir_load_from_mem_def, bir_load_from_mem_used_addrs_def] >>
REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vt rt at` >- (
  ASM_SIMP_TAC std_ss []
) >>
ASM_SIMP_TAC std_ss [] >>
COND_CASES_TAC >- (
  FULL_SIMP_TAC (list_ss++bir_endian_ss) [LET_DEF]
) >>
POP_ASSUM (K ALL_TAC) >>
STRIP_TAC >>
`MAP (\n. bir_load_bitstring_from_mmap vt mmap  (bir_mem_addr at (a + n))) (COUNT_LIST x) =
 MAP (\n. bir_load_bitstring_from_mmap vt mmap' (bir_mem_addr at (a + n))) (COUNT_LIST x)` suffices_by (
  ASM_SIMP_TAC std_ss []
) >>

FULL_SIMP_TAC list_ss [listTheory.MAP_EQ_f, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_load_bitstring_from_mmap_def]);


val bir_load_from_mem_used_addrs_REWRS = save_thm ("bir_load_from_mem_used_addrs_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "ta" bir_load_from_mem_used_addrs_def


  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] thm0
  val (l1, l2) = partition (optionSyntax.is_option_case o rhs o snd o strip_forall o concl) (CONJUNCTS thm1)

  val l1' = map (SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] o (GEN v)) l1

  val thm2 = LIST_CONJ (l2 @ l1')

  val thm3 = SIMP_RULE list_ss [
bir_number_of_mem_splits_REWRS, rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def,
   GSYM CONJ_ASSOC] thm2

  val thm4 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] (GEN v thm3)

in thm4
end);


val bir_load_from_mem_used_addrs_FINITE = store_thm ("bir_load_from_mem_used_addrs_FINITE",
  ``!tv tr ta en a.
      FINITE (bir_load_from_mem_used_addrs tv tr ta en a)``,
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_used_addrs_def] >>
Cases_on `bir_number_of_mem_splits tv tr ta` >> ASM_SIMP_TAC std_ss [pred_setTheory.FINITE_EMPTY] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [pred_setTheory.FINITE_EMPTY, listTheory.FINITE_LIST_TO_SET]);


val bir_load_from_mem_used_addrs_EMPTY = store_thm ("bir_load_from_mem_used_addrs_EMPTY",
  ``!mmap tv tr ta en a.
      (bir_load_from_mem_used_addrs tv tr ta en a = {}) <=>
      (bir_load_from_mem tv tr ta mmap en a = NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_EQ_NONE, bir_load_from_mem_used_addrs_def] >>
Cases_on `bir_number_of_mem_splits tv tr ta` >> ASM_SIMP_TAC std_ss [] >>
rename1 `_ = SOME n` >>
Q.SUBGOAL_THEN `(tv <> tr) <=> (bir_number_of_mem_splits tv tr ta <> SOME 1)`
  SUBST1_TAC >- METIS_TAC[bir_number_of_mem_splits_EQ_SOME1] >>

COND_CASES_TAC >> ASM_SIMP_TAC list_ss [] >>
Cases_on `n` >> FULL_SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def,
  bir_number_of_mem_splits_NEQ_SOME0]);


val bir_load_from_mem_used_addrs_NoEndian = store_thm ("bir_load_from_mem_used_addrs_NoEndian",
  ``!tv tr ta a.
      (bir_load_from_mem_used_addrs tv tr ta BEnd_NoEndian a = {}) \/
      (bir_load_from_mem_used_addrs tv tr ta BEnd_NoEndian a = {bir_mem_addr ta a})``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_EQ_NONE, bir_load_from_mem_used_addrs_def] >>
Cases_on `bir_number_of_mem_splits tv tr ta` >> ASM_SIMP_TAC std_ss [] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [] >>
SIMP_TAC list_ss [rich_listTheory.count_list_sub1,
  rich_listTheory.COUNT_LIST_def])




(* ------------------------------------------------------------------------- *)
(*  Storing                                                                  *)
(* ------------------------------------------------------------------------- *)


(* =============== *)
(* bitstring_split *)
(* =============== *)

val bitstring_split_aux_defn = Hol_defn "bitstring_split_aux"
 `(bitstring_split_aux 0 acc bs = ARB) /\
  (bitstring_split_aux n acc [] = REVERSE acc) /\
  (bitstring_split_aux n acc bs =
     bitstring_split_aux n ((TAKE n bs)::acc) (DROP n bs))`

(* Defn.tgoal bitstring_split_aux_defn *)
val (bitstring_split_aux_def, bitstring_split_aux_ind) = Defn.tstore_defn (bitstring_split_aux_defn,
  WF_REL_TAC `measure (\ (_, _, l). LENGTH l)` >>
  SIMP_TAC list_ss []);

val bitstring_split_def = Define `bitstring_split n bs = bitstring_split_aux n [] bs`

val bitstring_split_aux_REWR1 = SIMP_RULE std_ss [] (prove (``!n (_ : 'a list list) bs.
  (!acc. (n <> 0) ==> (bitstring_split_aux n acc (bs:'a list) =
         (REVERSE acc) ++ (bitstring_split_aux n [] bs)))``,

HO_MATCH_MP_TAC bitstring_split_aux_ind >>
REWRITE_TAC [numTheory.NOT_SUC] >>
REPEAT STRIP_TAC >| [
  SIMP_TAC list_ss [bitstring_split_aux_def],

  REWRITE_TAC [bitstring_split_aux_def] >>
  ONCE_ASM_REWRITE_TAC[] >>
  SIMP_TAC list_ss []
]));


val bitstring_split_aux_REWR2 = prove (``!n acc x xs.
  (bitstring_split_aux (SUC n) acc (x::xs) =
  (bitstring_split_aux (SUC n) ((TAKE (SUC n) (x::xs))::acc) (DROP (SUC n) (x::xs))))``,
REWRITE_TAC[bitstring_split_aux_def]);


val bitstring_split_REWRS = store_thm ("bitstring_split_REWRS",
  ``(!n. n <> 0 ==> (bitstring_split n [] = [])) /\
    (!n bs. n <> 0 /\ bs <> [] ==> (bitstring_split n bs = (TAKE n bs) :: (bitstring_split n (DROP n bs))))``,

SIMP_TAC std_ss [bitstring_split_def] >>
CONJ_TAC >- (
  Cases >> REWRITE_TAC [bitstring_split_aux_def, listTheory.REVERSE_DEF]
) >>
Cases >> Cases >> SIMP_TAC list_ss [bitstring_split_aux_REWR2] >>
SIMP_TAC list_ss [Once bitstring_split_aux_REWR1]);


val bitstring_split_REWRS_LENGTH = store_thm ("bitstring_split_REWRS_LENGTH",
  ``(!n bs. n <> 0 /\ (LENGTH bs = 0) ==> (bitstring_split n bs = [])) /\
    (!n bs. n <> 0 /\ 0 < LENGTH bs ==> (bitstring_split n bs = (TAKE n bs) :: (bitstring_split n (DROP n bs))))``,

REPEAT STRIP_TAC >> (
  Cases_on `bs` >>
  FULL_SIMP_TAC list_ss [bitstring_split_REWRS]
));


val bitstring_split_INDUCT = store_thm ("bitstring_split_INDUCT",
``!n P. (n <> 0 /\
        (P [] /\ (!l. (l <> [] /\ P (DROP n l)) ==> P l))) ==>
        (!l. P l)``,

REPEAT STRIP_TAC >>
completeInduct_on `LENGTH l` >>
Cases_on `v` >> Cases_on `l` >> ASM_SIMP_TAC list_ss []
)

val bitstring_split_FLAT = store_thm ("bitstring_split_FLAT",
  ``!n. n <> 0 ==> !bs. (FLAT (bitstring_split n bs) = bs)``,

GEN_TAC >> STRIP_TAC >>
HO_MATCH_MP_TAC (Q.SPEC `n` bitstring_split_INDUCT) >>
ASM_SIMP_TAC list_ss [bitstring_split_REWRS]);


val bitstring_split_LENGTHS = store_thm ("bitstring_split_LENGTHS",
  ``!n m bs. n <> 0 /\ (LENGTH bs = m*n) ==> (
      (EVERY (\l. LENGTH l = n) (bitstring_split n bs)) /\
      (LENGTH (bitstring_split n bs) = m))``,

GEN_TAC >>
Induct >- (
  Cases >> SIMP_TAC list_ss [bitstring_split_REWRS]
) >>
SIMP_TAC list_ss [arithmeticTheory.MULT_SUC] >>
GEN_TAC >> STRIP_TAC >>
`bs <> []` by (
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss []
) >>
ASM_SIMP_TAC list_ss [bitstring_split_REWRS]);


val bitstring_split_LENGTHS_MODDIV = store_thm ("bitstring_split_LENGTHS_MODDIV",
  ``!n bs. n <> 0 /\ (LENGTH bs MOD n = 0) ==> (
      (EVERY (\l. LENGTH l = n) (bitstring_split n bs)) /\
      (LENGTH (bitstring_split n bs) = LENGTH bs DIV n))``,

REPEAT STRIP_TAC >>
`0 < n` by DECIDE_TAC >>
`?m. LENGTH bs = m * n `by METIS_TAC[arithmeticTheory.MOD_EQ_0_DIVISOR] >>
ASM_SIMP_TAC std_ss [arithmeticTheory.MULT_DIV] >>
METIS_TAC [bitstring_split_LENGTHS]);


val bitstring_split_LENGTHS_b2v = store_thm ("bitstring_split_LENGTHS_b2v",
  ``!n v vty aty. (bir_number_of_mem_splits vty (type_of_bir_imm v) aty = SOME n) ==>
      (EVERY (\l. LENGTH l = (size_of_bir_immtype vty)) (bitstring_split (size_of_bir_immtype vty) (b2v v)) /\
      (LENGTH (bitstring_split (size_of_bir_immtype vty) (b2v v)) = n))``,

SIMP_TAC std_ss [bir_number_of_mem_splits_def] >>
METIS_TAC[bitstring_split_LENGTHS_MODDIV, size_of_bir_immtype_NEQ_0,
  b2v_LENGTH]);

val bitstring_split_SINGLE = store_thm ("bitstring_split_SINGLE",
  ``!n bs. n <> 0 ==>
      (LENGTH bs = n) ==>
      (bitstring_split n bs = [bs])``,

REPEAT STRIP_TAC >>
`bs <> []` by (Cases_on `bs` >> FULL_SIMP_TAC list_ss []) >>
ASM_SIMP_TAC list_ss [bitstring_split_REWRS, listTheory.TAKE_LENGTH_TOO_LONG,
  listTheory.DROP_LENGTH_TOO_LONG]);


val bir_mem_concat_bitstring_split = store_thm ("bir_mem_concat_bitstring_split",
``!v n rty.
      (n <> 0) ==>
      (bir_mem_concat (bitstring_split n (b2v v)) rty = n2bs (b2n v) rty)``,

SIMP_TAC std_ss [bir_mem_concat_def, bitstring_split_FLAT, v2bs_def, v2n_b2v, n2bs_def]);


val bitstring_split_num_REWRS = save_thm ("bitstring_split_num_REWRS",
let
  val words_sizes = bir_immSyntax.known_imm_sizes;

  val combined_sizes = flatten (map (fn sz1 => map (fn sz2 => (sz1, sz2)) words_sizes) words_sizes)
  val combined_sizes = filter (fn (sz1, sz2) => (sz1 <= sz2) andalso (sz2 mod sz1 = 0)) combined_sizes

  fun mk_sizes_thm (sz1, sz2) = let
    val sz1_tm = numSyntax.term_of_int sz1
    val sz2_tm = numSyntax.term_of_int sz2
    val l_tm = ``l:'a list``
    val pre = ``LENGTH ^l_tm = ^sz2_tm``
    val t = ``bitstring_split ^sz1_tm ^l_tm``

    val thm0 = SIMP_CONV list_ss [b2v_def, bitstring_split_REWRS_LENGTH,
       listTheory.TAKE_LENGTH_TOO_LONG,
       listTheory.DROP_LENGTH_TOO_LONG, rich_listTheory.DROP_DROP_T,
       ASSUME pre] t
    val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV list_ss [GSYM rich_listTheory.SEG_TAKE_BUTFISTN,
                 ASSUME pre, rich_listTheory.DROP_SEG, rich_listTheory.TAKE_SEG])) thm0
    val thm2 = GEN l_tm (DISCH pre thm1)
  in thm2 end

  val thm0 = LIST_CONJ (map mk_sizes_thm combined_sizes)
in
  thm0
end);


(* ================= *)
(* update_mmap       *)
(* ================= *)

val bir_update_mmap_def = Define `
    (!mmap aty a.      (bir_update_mmap aty mmap a [] = mmap)) /\
    (!mmap aty a v vs. (bir_update_mmap aty mmap a (v::vs) =
                        bir_update_mmap aty (((bir_mem_addr aty a) =+ v2n v) mmap) (SUC a) vs))`;


val bir_update_mmap_UNCHANGED = store_thm ("bir_update_mmap_UNCHANGED",
  ``!aty mmap a vs a'.
      (!n. n < LENGTH vs ==> (a' <> bir_mem_addr aty (a+n))) ==>
      ((bir_update_mmap aty mmap a vs) a' = mmap a')``,

GEN_TAC >>
Induct_on `vs` >> (
  SIMP_TAC list_ss [bir_update_mmap_def]
) >>
REPEAT STRIP_TAC >>
`bir_update_mmap aty ((bir_mem_addr aty a =+ v2n h) mmap) (SUC a) vs a' =
 (bir_mem_addr aty a =+ v2n h) mmap a'` by (
   Q.PAT_X_ASSUM `!aty a a'. _` MATCH_MP_TAC >>
   REPEAT STRIP_TAC >>
   Q.PAT_X_ASSUM `!n. _` (MP_TAC o Q.SPEC `SUC n`) >>
   ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_CLAUSES]
) >>
Q.PAT_X_ASSUM `!n. n < SUC _ ==> _` (MP_TAC o Q.SPEC `0`) >>
ASM_SIMP_TAC arith_ss [combinTheory.APPLY_UPDATE_THM]);



(* ================= *)
(* bir_store_in_mmap *)
(* ================= *)

val bir_store_in_mem_def = Define `bir_store_in_mem
  (value_ty : bir_immtype_t) (a_ty : bir_immtype_t) (result : bir_imm_t) (mmap : num -> num) (en: bir_endian_t) (a:num) =

   let result_ty = type_of_bir_imm result in
   case (bir_number_of_mem_splits value_ty result_ty a_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bitstring_split (size_of_bir_immtype value_ty) (b2v result) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in

        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_update_mmap a_ty mmap a vs'')
   )`;


val bir_store_in_mem_SINGLE = store_thm ("bir_store_in_mem_SINGLE",
  ``!en a vty aty mmap v.
     (type_of_bir_imm v = vty) ==>
     (bir_store_in_mem vty aty v mmap en a = SOME (((bir_mem_addr aty a) =+ b2n v) mmap))``,

Cases_on `en` >> (
  SIMP_TAC (list_ss++bir_endian_ss) [bir_store_in_mem_def, bir_number_of_mem_splits_ID, LET_DEF,
    bitstring_split_SINGLE, b2v_LENGTH, size_of_bir_immtype_NEQ_0, v2n_b2v,
    bir_update_mmap_def]
));


val bir_store_in_mem_NO_ENDIAN = store_thm ("bir_store_in_mem_NO_ENDIAN",
  ``!a vty aty v mmap. bir_store_in_mem vty aty v mmap BEnd_NoEndian a =
    (if vty = (type_of_bir_imm v) then
      SOME (((bir_mem_addr aty a) =+ b2n v) mmap)
     else NONE)``,

REPEAT GEN_TAC >>
Cases_on `vty = type_of_bir_imm v` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_SINGLE]
) >>
`bir_number_of_mem_splits vty (type_of_bir_imm v) aty <> SOME 1` by (
  ASM_SIMP_TAC std_ss [bir_number_of_mem_splits_EQ_SOME1]
) >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v) aty` >> (
  FULL_SIMP_TAC (std_ss++bir_endian_ss) [bir_store_in_mem_def, LET_DEF]
));


val bir_store_in_mem_EQ_NONE = store_thm ("bir_store_in_mem_EQ_NONE",
  ``!a en vty aty v mmap. (bir_store_in_mem vty aty v mmap en a = NONE) <=>
      ((bir_number_of_mem_splits vty (type_of_bir_imm v) aty = NONE) \/
      ((vty <> (type_of_bir_imm v)) /\ (en = BEnd_NoEndian)))``,

REPEAT GEN_TAC >>
Q.SUBGOAL_THEN `(vty <> (type_of_bir_imm v)) <=> (bir_number_of_mem_splits vty (type_of_bir_imm v) aty <> SOME 1)`
  SUBST1_TAC >- (
  SIMP_TAC std_ss [bir_number_of_mem_splits_EQ_SOME1]
) >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v) aty` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss) []
) >>
rename1 `_ = SOME n` >>
Cases_on `n=1` >> FULL_SIMP_TAC std_ss []);


val bir_store_in_mem_EQ_NONE_IMP = store_thm ("bir_store_in_mem_EQ_NONE_IMP",
  ``!a en vty aty v mmap.
      ((bir_number_of_mem_splits vty (type_of_bir_imm v) aty = NONE) \/
       ((vty <> (type_of_bir_imm v)) /\ (en = BEnd_NoEndian))) ==>
      (bir_store_in_mem vty aty v mmap en a = NONE)``,
METIS_TAC[bir_store_in_mem_EQ_NONE]);


val bir_store_in_mem_EQ_SOME = store_thm ("bir_store_in_mem_EQ_SOME",
  ``!a en vty aty v mmap res. (bir_store_in_mem vty aty v mmap en a = SOME res) <=>
      (?n vs vs'. (bir_number_of_mem_splits vty (type_of_bir_imm v) aty = SOME n) /\
                  (vs = (bitstring_split (size_of_bir_immtype vty) (b2v v))) /\
                  ((en = BEnd_BigEndian) /\ (vs' = vs) \/
                   (en = BEnd_LittleEndian) /\ (vs' = REVERSE vs) \/
                   (en = BEnd_NoEndian) /\ (n = 1) /\ (vs' = vs)) /\
                   (res = bir_update_mmap aty mmap a vs'))``,

REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v) aty` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss++boolSimps.EQUIV_EXTRACT_ss) []
) >>
rename1 `_ = SOME n` >>
Cases_on `n=1` >>
  ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) []);



val bir_store_in_mem_NONE_REWRS = save_thm ("bir_store_in_mem_NONE_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "aty" bir_store_in_mem_EQ_NONE_IMP

  val thm1 = SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``,
    ``:bir_imm_t``]) [type_of_bir_imm_def, bir_number_of_mem_splits_REWRS, DISJ_IMP_THM, FORALL_AND_THM, GSYM CONJ_ASSOC] thm0

  val (l1, l2) = partition (is_imp_only o snd o strip_forall o concl) (CONJUNCTS thm1)

  val l1' = map (SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] o (GEN v)) l1

  val thm2 = LIST_CONJ (l1' @ l2)

  val thm3 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] (GEN v thm2)
in
  thm3
end);


val bir_store_in_mem_REWRS = save_thm ("bir_store_in_mem_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "a_ty" bir_store_in_mem_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [
    bir_number_of_mem_splits_REWRS, LET_DEF, type_of_bir_imm_def] thm0

  val (l1, l2) = partition (optionSyntax.is_option_case o rhs o snd o strip_forall o concl) (CONJUNCTS thm1)

  val l1' = map (SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] o (GEN v)) l1

  val thm2 = LIST_CONJ (l2 @ l1')

  val thm3 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [b2v_def, bitstring_split_num_REWRS,
     bitstringTheory.length_w2v, size_of_bir_immtype_def] thm2
  val thm4 = SIMP_RULE (list_ss++bir_endian_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm3

  val thm5 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm4

  val thm6 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] (GEN v thm5)

in thm6
end);



val bir_store_in_mem_used_addrs_def = Define `
  bir_store_in_mem_used_addrs vty v aty en a =
  bir_load_from_mem_used_addrs vty (type_of_bir_imm v) aty en a`;


val bir_store_in_mem_used_addrs_THM = store_thm ("bir_store_in_mem_used_addrs_THM",
  ``!a en vty aty v mmap mmap'.
       (bir_store_in_mem vty aty v mmap en a = SOME mmap') ==>
       (!addr. ~(addr IN bir_store_in_mem_used_addrs vty v aty en a) ==>
               (mmap' addr = mmap addr))``,

SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_load_from_mem_used_addrs_def,
  bir_store_in_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM] >>
SIMP_TAC (list_ss++bir_endian_ss) [DISJ_IMP_THM, LEFT_AND_OVER_OR, FORALL_AND_THM,
  listTheory.MEM_MAP, rich_listTheory.MEM_COUNT_LIST] >>
REPEAT STRIP_TAC >> (
  MATCH_MP_TAC bir_update_mmap_UNCHANGED >>
  METIS_TAC[bitstring_split_LENGTHS_b2v, listTheory.LENGTH_REVERSE]
));



val bir_store_in_mem_used_addrs_REWRS = save_thm ("bir_store_in_mem_used_addrs_REWRS",
let
  val (v, thm0) = remove_quant_from_thm "aty" bir_store_in_mem_used_addrs_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``,
     ``:bir_imm_t``]) [
     bir_load_from_mem_used_addrs_REWRS, type_of_bir_imm_def] thm0
in thm1
end);

val bir_store_in_mem_used_addrs_FINITE = store_thm ("bir_store_in_mem_used_addrs_FINITE",
  ``!tv v ta en a.
      FINITE (bir_store_in_mem_used_addrs tv v ta en a)``,
SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_load_from_mem_used_addrs_FINITE])


val bir_store_in_mem_used_addrs_EMPTY = store_thm ("bir_store_in_mem_used_addrs_EMPTY",
  ``!mmap tv v ta en a.
      (bir_store_in_mem_used_addrs tv v ta en a = {}) <=>
      (bir_store_in_mem tv ta v mmap en a = NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_store_in_mem_EQ_NONE,
  bir_load_from_mem_used_addrs_def] >>
Q.SUBGOAL_THEN `(tv <> type_of_bir_imm v) <=> bir_number_of_mem_splits tv (type_of_bir_imm v) ta <> SOME 1` SUBST1_TAC >- METIS_TAC [bir_number_of_mem_splits_EQ_SOME1] >>

Cases_on `bir_number_of_mem_splits tv (type_of_bir_imm v) ta` >> ASM_SIMP_TAC std_ss [] >>
rename1 `_ = SOME n` >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [] >>
POP_ASSUM (K ALL_TAC) >>
Cases_on `n` >- (
  FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_NEQ_SOME0]
) >>
SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]);


val bir_store_in_mem_used_addrs_NoEndian = store_thm ("bir_store_in_mem_used_addrs_NoEndian",
  ``!tv v ta a.
      (bir_store_in_mem_used_addrs tv v ta BEnd_NoEndian a = {}) \/
      (bir_store_in_mem_used_addrs tv v ta BEnd_NoEndian a = {bir_mem_addr ta a})``,

SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def] >>
METIS_TAC[bir_load_from_mem_used_addrs_NoEndian]);



(* ------------------------------------------------------------------------- *)
(*  Loading and storing fit                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_load_bitstring_from_updated_mmap = store_thm ("bir_load_bitstring_from_updated_mmap",
  ``!aty vty vs n mmap a. (
      (LENGTH vs = n) /\
      (!v. MEM v vs ==> (LENGTH v = (size_of_bir_immtype vty))) /\
      (n <= 2 ** (size_of_bir_immtype aty))) ==>
   (MAP (\n.
    bir_load_bitstring_from_mmap vty
             (bir_update_mmap aty mmap a vs)
             (bir_mem_addr aty (a + n))) (COUNT_LIST n) = vs)``,
NTAC 2 GEN_TAC >>
Induct_on `vs` >- (
  SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]
) >>
CONV_TAC (RENAME_VARS_CONV ["v"]) >>
SIMP_TAC std_ss [listTheory.LENGTH, rich_listTheory.COUNT_LIST_def] >>
SIMP_TAC list_ss [listTheory.MAP_MAP_o, combinTheory.o_DEF, bir_update_mmap_def,
  DISJ_IMP_THM, FORALL_AND_THM] >>
REPEAT GEN_TAC >> STRIP_TAC >>
Q.ABBREV_TAC `mmap' = (bir_mem_addr aty a =+ v2n v) mmap` >>
Tactical.REVERSE CONJ_TAC >- (
  Q.PAT_X_ASSUM `!n. _` (MP_TAC o Q.SPECL [
    `LENGTH (vs:bitstring list)`, ` ((bir_mem_addr aty a =+ v2n v) mmap)`, `SUC a`]) >>
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_CLAUSES]
) >>

`(bir_update_mmap aty mmap' (SUC a) vs (bir_mem_addr aty a)) = mmap' (bir_mem_addr aty a)` by (
  MATCH_MP_TAC bir_update_mmap_UNCHANGED >>
  ASM_SIMP_TAC std_ss [bir_mem_addr_def, bitTheory.MOD_2EXP_def] >>
  GEN_TAC >> STRIP_TAC >>
  Q.SUBGOAL_THEN `a = 0 + a` SUBST1_TAC >- DECIDE_TAC >>
  Q.SUBGOAL_THEN `SUC (0 + a) + n = SUC n + a` SUBST1_TAC >- DECIDE_TAC >>
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_MOD]
) >>
UNABBREV_ALL_TAC >>
ASM_SIMP_TAC arith_ss [bir_load_bitstring_from_mmap_def,
  combinTheory.APPLY_UPDATE_THM, n2v_v2n]);



val bir_store_load_mem_THM = store_thm ("bir_store_load_mem_THM",
  ``!a en vty aty v mmap mmap'.
       (bir_store_in_mem vty aty v mmap en a = SOME mmap') ==>
       (bir_load_from_mem vty (type_of_bir_imm v) aty mmap' en a = SOME v)``,

SIMP_TAC (pure_ss) [bir_store_in_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM,
  bir_load_from_mem_EQ_SOME] >>
REPEAT GEN_TAC >>
Q.MATCH_ABBREV_TAC `(_ /\ _ /\ en_COND /\ _) ==> _` >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `vs'` >>
Tactical.REVERSE (Q.SUBGOAL_THEN `MAP (\n. bir_load_bitstring_from_mmap vty mmap' (bir_mem_addr aty (a + n)))
     (COUNT_LIST n) = vs'` SUBST1_TAC) >- (
  UNABBREV_ALL_TAC >> (
    FULL_SIMP_TAC (list_ss++bir_endian_ss) [bir_mem_concat_bitstring_split,
      size_of_bir_immtype_NEQ_0, n2bs_b2n]
  )
) >>

ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_load_bitstring_from_updated_mmap >>

`((EVERY (\v. (LENGTH v = size_of_bir_immtype vty)) vs) /\
  (LENGTH vs = n)) /\
 (n <= 2 ** size_of_bir_immtype aty)` suffices_by (
    UNABBREV_ALL_TAC >> FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM]
) >>
CONJ_TAC >- (
  METIS_TAC [bitstring_split_LENGTHS_b2v]
) >>
FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_def] >>
FULL_SIMP_TAC std_ss []);


val bir_store_load_mem_disjoint_THM = store_thm ("bir_store_load_mem_disjoint_THM",
  ``!a en vty aty v mmap mmap' a' en' vty' aty' rty'.
       (DISJOINT (bir_store_in_mem_used_addrs vty v aty en a)
                 (bir_load_from_mem_used_addrs vty' aty' rty' en' a')) ==>
       (bir_store_in_mem vty aty v mmap en a = SOME mmap') ==>
       (bir_load_from_mem vty' aty' rty' mmap' en' a' =
        bir_load_from_mem vty' aty' rty' mmap en' a')``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC (bir_load_from_mem_used_addrs_THM) >>
REPEAT STRIP_TAC >>
`~(addr IN (bir_store_in_mem_used_addrs vty v aty en a))` by (
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DISJOINT] >>
  METIS_TAC[]
) >>
METIS_TAC[bir_store_in_mem_used_addrs_THM]);












(* ------------------------------------------------------------------------- *)
(*  Memory equality                                                          *)
(* ------------------------------------------------------------------------- *)

val bir_memeq_def = Define `
  (bir_memeq aty vty mmap1 mmap2 = !a. (n2bs (mmap1 (bir_mem_addr aty a)) vty) =
                                       (n2bs (mmap2 (bir_mem_addr aty a)) vty))`;







val _ = export_theory();
