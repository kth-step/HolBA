open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory;

val _ = new_theory "bir_mem_exp";

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
   (value_ty : bir_immtype_t) (result_ty : bir_immtype_t) =
   if ((size_of_bir_immtype result_ty) MOD (size_of_bir_immtype value_ty) = 0) then
      SOME ((size_of_bir_immtype result_ty) DIV (size_of_bir_immtype value_ty))
   else NONE`;

val bir_number_of_mem_splits_REWRS = save_thm ("bir_number_of_mem_splits_REWRS",
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    size_of_bir_immtype_def, GSYM CONJ_ASSOC]
     bir_number_of_mem_splits_def)

val bir_number_of_mem_splits_NEQ_SOME0 = store_thm ("bir_number_of_mem_splits_NEQ_SOME0",
  ``!vt rt. bir_number_of_mem_splits vt rt <> SOME 0``,
Cases >> Cases >> SIMP_TAC std_ss [bir_number_of_mem_splits_def, size_of_bir_immtype_def]);

val bir_number_of_mem_splits_ID = store_thm ("bir_number_of_mem_splits_ID",
  ``!r. bir_number_of_mem_splits r r = SOME 1``,
Cases >> SIMP_TAC std_ss [bir_number_of_mem_splits_REWRS]);


val bir_number_of_mem_splits_EQ_SOME1 = store_thm ("bir_number_of_mem_splits_EQ_SOME1",
  ``!vt rt. (bir_number_of_mem_splits vt rt = SOME 1) <=> (vt = rt)``,
Cases >> Cases >> SIMP_TAC (std_ss++bir_imm_ss) [bir_number_of_mem_splits_REWRS]);




(* ------------------------------------------------------------------------- *)
(*  Loading                                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_mem_concat_def = Define `bir_mem_concat vl rty = v2bs (FLAT vl) rty`

val type_of_bir_mem_concat = store_thm ("type_of_bir_mem_concat",
  ``!vl ty. type_of_bir_imm (bir_mem_concat vl ty) = ty``,
SIMP_TAC std_ss [bir_mem_concat_def, type_of_v2bs]);

val bir_load_bitstring_from_mmap_def = Define `
  bir_load_bitstring_from_mmap value_ty mmap a =
    fixwidth (size_of_bir_immtype value_ty) (n2v (mmap a))`

val bir_load_bitstring_from_mmap_w2v = store_thm ("bir_load_bitstring_from_mmap_w2v",
  ``!value_ty mmap a. (size_of_bir_immtype value_ty = dimindex (:'a)) ==>
      (bir_load_bitstring_from_mmap value_ty mmap a =
       (w2v ((n2w (mmap a)):'a word)))``,
SIMP_TAC std_ss [bir_load_bitstring_from_mmap_def, GSYM w2v_v2w, v2w_n2v]);


val bir_load_bitstring_from_mmap_w2v_THMS = store_thm ("bir_load_bitstring_from_mmap_w2v_THMS",
``(!mmap a. (bir_load_bitstring_from_mmap Bit1  mmap a = (w2v ((n2w (mmap a)):word1)))) /\
  (!mmap a. (bir_load_bitstring_from_mmap Bit8  mmap a = (w2v ((n2w (mmap a)):word8)))) /\
  (!mmap a. (bir_load_bitstring_from_mmap Bit16 mmap a = (w2v ((n2w (mmap a)):word16)))) /\
  (!mmap a. (bir_load_bitstring_from_mmap Bit32 mmap a = (w2v ((n2w (mmap a)):word32)))) /\
  (!mmap a. (bir_load_bitstring_from_mmap Bit64 mmap a = (w2v ((n2w (mmap a)):word64))))``,

REPEAT STRIP_TAC >> (
  MATCH_MP_TAC bir_load_bitstring_from_mmap_w2v >>
  SIMP_TAC (std_ss++wordsLib.WORD_ss) [size_of_bir_immtype_def]
));


val bir_load_from_mem_def = Define `bir_load_from_mem
  (value_ty : bir_immtype_t) (result_ty : bir_immtype_t) (mmap : num -> num) (en: bir_endian_t) (a:num) =

   case (bir_number_of_mem_splits value_ty result_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = MAP (\n. bir_load_bitstring_from_mmap value_ty mmap (a+n)) (COUNT_LIST n) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in
        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_mem_concat vs'' result_ty)
   )`;

val bir_load_from_mem_SINGLE = store_thm ("bir_load_from_mem_SINGLE",
  ``!en a vty mmap. bir_load_from_mem vty vty mmap en a =
    SOME (n2bs (mmap a) vty)``,

SIMP_TAC list_ss [bir_load_from_mem_def, bir_number_of_mem_splits_ID, LET_THM,
  rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def] >>
Cases_on `en` >> (
  SIMP_TAC (list_ss++bir_endian_ss) [bir_mem_concat_def, v2bs_fixwidth,
    v2bs_n2v, bir_load_bitstring_from_mmap_def]
));


val bir_load_from_mem_NO_ENDIAN = store_thm ("bir_load_from_mem_NO_ENDIAN",
  ``!a vty rty mmap. bir_load_from_mem vty rty mmap BEnd_NoEndian a =
    (if vty = rty then
      SOME (n2bs (mmap a) vty)
     else NONE)``,

REPEAT GEN_TAC >>
Cases_on `vty = rty` >> (
  ASM_SIMP_TAC std_ss [bir_load_from_mem_SINGLE]
) >>
`bir_number_of_mem_splits vty rty <> SOME 1` by (
  Cases_on `vty` >> Cases_on `rty` >>
  FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_REWRS]
) >>
Cases_on `bir_number_of_mem_splits vty rty` >> (
  FULL_SIMP_TAC (std_ss++bir_endian_ss) [bir_load_from_mem_def, LET_DEF]
));


val bir_load_from_mem_EQ_NONE = store_thm ("bir_load_from_mem_EQ_NONE",
  ``!a en vty rty mmap. (bir_load_from_mem vty rty mmap en a = NONE) <=>
      ((bir_number_of_mem_splits vty rty = NONE) \/
      ((vty <> rty) /\ (en = BEnd_NoEndian)))``,

REPEAT GEN_TAC >>
ASM_REWRITE_TAC [GSYM bir_number_of_mem_splits_EQ_SOME1] >>
Cases_on `bir_number_of_mem_splits vty rty` >> (
  ASM_SIMP_TAC std_ss [bir_load_from_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss) []
) >>
Cases_on `x=1` >> ASM_SIMP_TAC std_ss []);


val bir_load_from_mem_EQ_NONE_IMP = store_thm ("bir_load_from_mem_EQ_NONE_IMP",
  ``!a en vty rty mmap. 
      ((bir_number_of_mem_splits vty rty = NONE) \/
      ((vty <> rty) /\ (en = BEnd_NoEndian))) ==>
      (bir_load_from_mem vty rty mmap en a = NONE)``,
METIS_TAC[bir_load_from_mem_EQ_NONE]);


val bir_load_from_mem_EQ_SOME = store_thm ("bir_load_from_mem_EQ_SOME",
  ``!a en vty rty mmap res. (bir_load_from_mem vty rty mmap en a = SOME res) <=>
      (?n vs vs'. (bir_number_of_mem_splits vty rty = SOME n) /\
                  (vs = MAP (\n. bir_load_bitstring_from_mmap vty mmap (a+n)) (COUNT_LIST n)) /\
                  ((en = BEnd_BigEndian) /\ (vs' = vs) \/
                   (en = BEnd_LittleEndian) /\ (vs' = REVERSE vs) \/
                   (en = BEnd_NoEndian) /\ (n = 1) /\ (vs' = vs)) /\
                   (res = bir_mem_concat vs' rty))``,

SIMP_TAC std_ss [bir_load_from_mem_def] >>
REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vty rty` >> (
  ASM_SIMP_TAC std_ss [LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss++boolSimps.EQUIV_EXTRACT_ss) []
) >>
Cases_on `x=1` >>
ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) []);



val type_of_bir_load_from_mem = store_thm ("type_of_bir_load_from_mem",
  ``!a en vty rty mmap res. (bir_load_from_mem vty rty mmap en a = SOME res) ==>
      (type_of_bir_imm res = rty)``,

SIMP_TAC std_ss [bir_load_from_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM,
  type_of_bir_mem_concat]);


val bir_load_from_mem_NONE_REWRS = save_thm ("bir_load_from_mem_NONE_REWRS",
let
  val thm0 = bir_load_from_mem_EQ_NONE_IMP

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS] thm0

  val thm2 = SIMP_RULE (std_ss++bir_imm_ss) [GSYM CONJ_ASSOC, FORALL_AND_THM] thm1
in thm2 end);


(* One first rewrite *)
val bir_load_from_mem_REWRS0 = save_thm ("bir_load_from_mem_REWRS0",
let
  val thm0 = bir_load_from_mem_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
    bir_number_of_mem_splits_REWRS, rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def, bir_load_bitstring_from_mmap_w2v_THMS] thm0

  val thm2 = SIMP_RULE (list_ss++bir_endian_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm1

  val thm3 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm2

  val thm4 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] thm3

in thm4
end)

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
  `bir_load_from_mem_used_addrs tv tr en a =
   case (bir_number_of_mem_splits tv tr) of
    | NONE => {}
    | SOME (n:num) => (if (n <> 1) /\ (en = BEnd_NoEndian) then {} else
        set (MAP (\n. a + n) (COUNT_LIST n)))`

val bir_load_from_mem_used_addrs_THM = store_thm ("bir_load_from_mem_used_addrs_THM",
  ``!vt rt mmap mmap' en a.
      (!addr. addr IN (bir_load_from_mem_used_addrs vt rt en a) ==>
              (mmap addr = mmap' addr)) ==>
      (bir_load_from_mem vt rt mmap en a =
       bir_load_from_mem vt rt mmap' en a)``,

SIMP_TAC std_ss [bir_load_from_mem_def, bir_load_from_mem_used_addrs_def] >>
REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vt rt` >- (
  ASM_SIMP_TAC std_ss []
) >>
ASM_SIMP_TAC std_ss [] >>
COND_CASES_TAC >- (
  FULL_SIMP_TAC (list_ss++bir_endian_ss) [LET_DEF]
) >>
POP_ASSUM (K ALL_TAC) >>
STRIP_TAC >>
`MAP (\n. bir_load_bitstring_from_mmap vt mmap (a + n)) (COUNT_LIST x) =
 MAP (\n. bir_load_bitstring_from_mmap vt mmap' (a + n)) (COUNT_LIST x)` suffices_by (
  ASM_SIMP_TAC std_ss []
) >>

FULL_SIMP_TAC list_ss [listTheory.MAP_EQ_f, listTheory.MEM_MAP,
  GSYM LEFT_FORALL_IMP_THM, bir_load_bitstring_from_mmap_def]);


val bir_load_from_mem_used_addrs_REWRS = save_thm ("bir_load_from_mem_used_addrs_REWRS",
let
  val thm0 = bir_load_from_mem_used_addrs_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [
bir_number_of_mem_splits_REWRS, rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def,
   GSYM CONJ_ASSOC] thm0
in thm1
end);


val bir_load_from_mem_used_addrs_FINITE = store_thm ("bir_load_from_mem_used_addrs_FINITE",
  ``!tv tr en a.
      FINITE (bir_load_from_mem_used_addrs tv tr en a)``,
REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_used_addrs_def] >>
Cases_on `bir_number_of_mem_splits tv tr` >> ASM_SIMP_TAC std_ss [pred_setTheory.FINITE_EMPTY] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [pred_setTheory.FINITE_EMPTY, listTheory.FINITE_LIST_TO_SET]);


val bir_load_from_mem_used_addrs_EMPTY = store_thm ("bir_load_from_mem_used_addrs_EMPTY",
  ``!mmap tv tr en a.
      (bir_load_from_mem_used_addrs tv tr en a = {}) <=>
      (bir_load_from_mem tv tr mmap en a = NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_EQ_NONE, bir_load_from_mem_used_addrs_def,
  GSYM bir_number_of_mem_splits_EQ_SOME1] >>
Cases_on `bir_number_of_mem_splits tv tr` >> ASM_SIMP_TAC std_ss [] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [] >>
POP_ASSUM (K ALL_TAC) >>
Cases_on `x` >- (
  FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_NEQ_SOME0]
) >>
SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]);


val bir_load_from_mem_used_addrs_NoEndian = store_thm ("bir_load_from_mem_used_addrs_NoEndian",
  ``!tv tr a.
      (bir_load_from_mem_used_addrs tv tr BEnd_NoEndian a = {}) \/
      (bir_load_from_mem_used_addrs tv tr BEnd_NoEndian a = {a})``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_load_from_mem_EQ_NONE, bir_load_from_mem_used_addrs_def] >>
Cases_on `bir_number_of_mem_splits tv tr` >> ASM_SIMP_TAC std_ss [] >>
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
  ``!n v vty. (bir_number_of_mem_splits vty (type_of_bir_imm v) = SOME n) ==>
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
  val words_sizes = [1,8,16,32,64];

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
    val thm1 = GEN l_tm (DISCH pre thm0)
  in thm1 end

  val thm0 = LIST_CONJ (map mk_sizes_thm combined_sizes)
in
  thm0
end);


(* ================= *)
(* update_mmap       *)
(* ================= *)

val bir_update_mmap_def = Define `
    (!mmap a. (bir_update_mmap mmap a [] = mmap)) /\
    (!mmap a v vs. (bir_update_mmap mmap a (v::vs) =
                    bir_update_mmap ((a =+ v2n v) mmap) (SUC a) vs))`;


val bir_update_mmap_ALT_DEF = store_thm ("bir_update_mmap_ALT_DEF",
  ``!mmap a vs a'. (bir_update_mmap mmap a vs) a' =
      (if (a <= a' /\ a' < a + LENGTH vs) then v2n (EL (a' - a) vs) else mmap a')``,

Induct_on `vs` >> (
  ASM_SIMP_TAC list_ss [bir_update_mmap_def]
) >>
REPEAT GEN_TAC >>
Cases_on `~(a' < (LENGTH vs) + SUC a) \/ ~(a <= a')` >- (
  ASM_SIMP_TAC arith_ss [combinTheory.APPLY_UPDATE_THM]
) >>
FULL_SIMP_TAC arith_ss [] >>
Cases_on `SUC a <= a'` >- (
  `a' - a = SUC (a' - SUC a)` by DECIDE_TAC >>
  ASM_SIMP_TAC list_ss []
) >>
`a' = a` by DECIDE_TAC >>
ASM_SIMP_TAC list_ss [combinTheory.APPLY_UPDATE_THM]);



(* ================= *)
(* bir_store_in_mmap *)
(* ================= *)

val bir_store_in_mem_def = Define `bir_store_in_mem
  (value_ty : bir_immtype_t) (result : bir_imm_t) (mmap : num -> num) (en: bir_endian_t) (a:num) =

   let result_ty = type_of_bir_imm result in
   case (bir_number_of_mem_splits value_ty result_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bitstring_split (size_of_bir_immtype value_ty) (b2v result) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in

        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_update_mmap mmap a vs'')
   )`;


val bir_store_in_mem_SINGLE = store_thm ("bir_store_in_mem_SINGLE",
  ``!en a vty mmap v.
     (type_of_bir_imm v = vty) ==>
     (bir_store_in_mem vty v mmap en a = SOME ((a =+ b2n v) mmap))``,

Cases_on `en` >> (
  SIMP_TAC (list_ss++bir_endian_ss) [bir_store_in_mem_def, bir_number_of_mem_splits_ID, LET_DEF,
    bitstring_split_SINGLE, b2v_LENGTH, size_of_bir_immtype_NEQ_0, v2n_b2v,
    bir_update_mmap_def]
));


val bir_store_in_mem_NO_ENDIAN = store_thm ("bir_store_in_mem_NO_ENDIAN",
  ``!a vty v mmap. bir_store_in_mem vty v mmap BEnd_NoEndian a =
    (if vty = (type_of_bir_imm v) then
      SOME ((a =+ b2n v) mmap)
     else NONE)``,

REPEAT GEN_TAC >>
Cases_on `vty = type_of_bir_imm v` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_SINGLE]
) >>
`bir_number_of_mem_splits vty (type_of_bir_imm v) <> SOME 1` by (
  Cases_on `vty` >> Cases_on `v` >>
  FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_REWRS, type_of_bir_imm_def]
) >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v)` >> (
  FULL_SIMP_TAC (std_ss++bir_endian_ss) [bir_store_in_mem_def, LET_DEF]
));


val bir_store_in_mem_EQ_NONE = store_thm ("bir_store_in_mem_EQ_NONE",
  ``!a en vty v mmap. (bir_store_in_mem vty v mmap en a = NONE) <=>
      ((bir_number_of_mem_splits vty (type_of_bir_imm v) = NONE) \/
      ((vty <> (type_of_bir_imm v)) /\ (en = BEnd_NoEndian)))``,

REPEAT GEN_TAC >>
REWRITE_TAC[GSYM bir_number_of_mem_splits_EQ_SOME1] >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v)` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss) []
) >>
Cases_on `x=1` >> ASM_SIMP_TAC std_ss []);


val bir_store_in_mem_EQ_NONE_IMP = store_thm ("bir_store_in_mem_EQ_NONE_IMP",
  ``!a en vty v mmap. 
      ((bir_number_of_mem_splits vty (type_of_bir_imm v) = NONE) \/
       ((vty <> (type_of_bir_imm v)) /\ (en = BEnd_NoEndian))) ==>
      (bir_store_in_mem vty v mmap en a = NONE)``,
METIS_TAC[bir_store_in_mem_EQ_NONE]);


val bir_store_in_mem_EQ_SOME = store_thm ("bir_store_in_mem_EQ_SOME",
  ``!a en vty v mmap res. (bir_store_in_mem vty v mmap en a = SOME res) <=>
      (?n vs vs'. (bir_number_of_mem_splits vty (type_of_bir_imm v) = SOME n) /\
                  (vs = (bitstring_split (size_of_bir_immtype vty) (b2v v))) /\
                  ((en = BEnd_BigEndian) /\ (vs' = vs) \/
                   (en = BEnd_LittleEndian) /\ (vs' = REVERSE vs) \/
                   (en = BEnd_NoEndian) /\ (n = 1) /\ (vs' = vs)) /\
                   (res = bir_update_mmap mmap a vs'))``,

REPEAT GEN_TAC >>
Cases_on `bir_number_of_mem_splits vty (type_of_bir_imm v)` >> (
  ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]
) >>
Cases_on `en` >> (
  ASM_SIMP_TAC (std_ss++bir_endian_ss++boolSimps.EQUIV_EXTRACT_ss) []
) >>
Cases_on `x=1` >>
ASM_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) []);



val bir_store_in_mem_NONE_REWRS = save_thm ("bir_store_in_mem_NONE_REWRS",
let
  val thm0 = bir_store_in_mem_EQ_NONE_IMP

  val thm1 = SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``,
    ``:bir_imm_t``]) [type_of_bir_imm_def,
    bir_number_of_mem_splits_REWRS] thm0

  val thm2 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] thm1
in
  thm2
end);


val bir_store_in_mem_REWRS = save_thm ("bir_store_in_mem_REWRS",
let
  val thm0 = bir_store_in_mem_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``,
    ``:bir_imm_t``]) [
    bir_number_of_mem_splits_REWRS, type_of_bir_imm_def, bir_number_of_mem_splits_REWRS, LET_DEF,
      size_of_bir_immtype_def] thm0

  val thm2 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [b2v_def, bitstring_split_num_REWRS,
     bitstringTheory.length_w2v] thm1
  val thm3 = SIMP_RULE (list_ss++bir_endian_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm2

  val thm4 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm3

  val thm5 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] thm4

in thm5
end);


val bir_store_in_mem_used_addrs_def = Define `
  bir_store_in_mem_used_addrs vty v en a =
  bir_load_from_mem_used_addrs vty (type_of_bir_imm v) en a`;


val bir_store_in_mem_used_addrs_THM = store_thm ("bir_store_in_mem_used_addrs_THM",
  ``!a en vty v mmap mmap'.
       (bir_store_in_mem vty v mmap en a = SOME mmap') ==>
       (!addr. ~(addr IN bir_store_in_mem_used_addrs vty v en a) ==>
               (mmap' addr = mmap addr))``,

SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_load_from_mem_used_addrs_def,
  bir_store_in_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM] >>
REPEAT GEN_TAC >>

`!addr. ((!n'. addr <> a + n' \/ ~(n' < n)) <=>
 (~(a <= addr /\ addr < a + n)))` suffices_by (
  STRIP_TAC >> STRIP_TAC >> (
    MP_TAC (Q.SPECL [`n`, `v`, `vty`] bitstring_split_LENGTHS_b2v) >>
    FULL_SIMP_TAC (list_ss++bir_endian_ss) [bir_update_mmap_ALT_DEF,
      listTheory.MEM_MAP, rich_listTheory.MEM_COUNT_LIST]
  )
) >>

REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC >| [
  Q.PAT_X_ASSUM `!n'. _ ` (MP_TAC o Q.SPEC `addr - a`) >>
  ASM_SIMP_TAC arith_ss [],

  Cases_on `addr = a + n'` >>
  FULL_SIMP_TAC std_ss []
]);


val bir_store_in_mem_used_addrs_REWRS = save_thm ("bir_store_in_mem_used_addrs_REWRS",
let
  val thm0 = bir_store_in_mem_used_addrs_def

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``,
     ``:bir_imm_t``]) [
     bir_load_from_mem_used_addrs_REWRS, type_of_bir_imm_def] thm0
in thm1
end);

val bir_store_in_mem_used_addrs_FINITE = store_thm ("bir_store_in_mem_used_addrs_FINITE",
  ``!tv v en a.
      FINITE (bir_store_in_mem_used_addrs tv v en a)``,
SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_load_from_mem_used_addrs_FINITE])


val bir_store_in_mem_used_addrs_EMPTY = store_thm ("bir_store_in_mem_used_addrs_EMPTY",
  ``!mmap tv v en a.
      (bir_store_in_mem_used_addrs tv v en a = {}) <=>
      (bir_store_in_mem tv v mmap en a = NONE)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def, bir_store_in_mem_EQ_NONE,
  bir_load_from_mem_used_addrs_def, GSYM bir_number_of_mem_splits_EQ_SOME1] >>
Cases_on `bir_number_of_mem_splits tv (type_of_bir_imm v)` >> ASM_SIMP_TAC std_ss [] >>
COND_CASES_TAC >> ASM_SIMP_TAC std_ss [] >>
POP_ASSUM (K ALL_TAC) >>
Cases_on `x` >- (
  FULL_SIMP_TAC std_ss [bir_number_of_mem_splits_NEQ_SOME0]
) >>
SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]);


val bir_store_in_mem_used_addrs_NoEndian = store_thm ("bir_store_in_mem_used_addrs_NoEndian",
  ``!tv v a.
      (bir_store_in_mem_used_addrs tv v BEnd_NoEndian a = {}) \/
      (bir_store_in_mem_used_addrs tv v BEnd_NoEndian a = {a})``,

SIMP_TAC std_ss [bir_store_in_mem_used_addrs_def] >>
METIS_TAC[bir_load_from_mem_used_addrs_NoEndian]);



(* ------------------------------------------------------------------------- *)
(*  Loading and storing fit                                                  *)
(* ------------------------------------------------------------------------- *)

val bir_load_bitstring_from_updated_mmap = store_thm ("bir_load_bitstring_from_updated_mmap",
  ``!vty vs n mmap a. (LENGTH vs = n) /\
      (!v. MEM v vs ==> (LENGTH v = (size_of_bir_immtype vty))) ==>
   (MAP (\n.
    bir_load_bitstring_from_mmap vty
             (bir_update_mmap mmap a vs)
             (a + n)) (COUNT_LIST n) = vs)``,
GEN_TAC >>
Induct_on `vs` >- (
  SIMP_TAC list_ss [rich_listTheory.COUNT_LIST_def]
) >>
CONV_TAC (RENAME_VARS_CONV ["v"]) >>
SIMP_TAC std_ss [listTheory.LENGTH, rich_listTheory.COUNT_LIST_def] >>
SIMP_TAC list_ss [listTheory.MAP_MAP_o, combinTheory.o_DEF, bir_update_mmap_def,
  DISJ_IMP_THM, FORALL_AND_THM] >>
REPEAT STRIP_TAC >- (
  ASM_SIMP_TAC arith_ss [bir_load_bitstring_from_mmap_def, bir_update_mmap_ALT_DEF,
    combinTheory.APPLY_UPDATE_THM, n2v_v2n]
) >>
Q.PAT_X_ASSUM `!n. _` (MP_TAC o Q.SPECL [`LENGTH (vs:bitstring list)`, ` ((a =+ v2n v) mmap)`,
  `SUC a`]) >>
ASM_SIMP_TAC std_ss [arithmeticTheory.ADD_CLAUSES]);



val bir_store_load_mem_THM = store_thm ("bir_store_load_mem_THM",
  ``!a en vty v mmap mmap'. (bir_store_in_mem vty v mmap en a = SOME mmap') ==>
       (bir_load_from_mem vty (type_of_bir_imm v) mmap' en a = SOME v)``,

SIMP_TAC (pure_ss) [bir_store_in_mem_EQ_SOME, GSYM LEFT_FORALL_IMP_THM,
  bir_load_from_mem_EQ_SOME] >>
REPEAT GEN_TAC >>
Q.MATCH_ABBREV_TAC `(_ /\ _ /\ en_COND /\ _) ==> _` >>
REPEAT STRIP_TAC >>
Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `vs'` >>
Tactical.REVERSE (Q.SUBGOAL_THEN `MAP (\n. bir_load_bitstring_from_mmap vty mmap' (a + n))
     (COUNT_LIST n) = vs'` SUBST1_TAC) >- (
  UNABBREV_ALL_TAC >> (
    FULL_SIMP_TAC (list_ss++bir_endian_ss) [bir_mem_concat_bitstring_split,
      size_of_bir_immtype_NEQ_0, n2bs_b2n]
  )
) >>

ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_load_bitstring_from_updated_mmap >>
`(EVERY (\v. (LENGTH v = size_of_bir_immtype vty)) vs) /\
 (LENGTH vs = n)` suffices_by (
    UNABBREV_ALL_TAC >> FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM]
) >>
ASM_SIMP_TAC std_ss [bitstring_split_LENGTHS_b2v]);


val bir_store_load_mem_disjoint_THM = store_thm ("bir_store_load_mem_disjoint_THM",
  ``!a en vty v mmap mmap' a' en' vty' rty'.
       (DISJOINT (bir_store_in_mem_used_addrs vty v en a)
                 (bir_load_from_mem_used_addrs vty' rty' en' a')) ==>
       (bir_store_in_mem vty v mmap en a = SOME mmap') ==>
       (bir_load_from_mem vty' rty' mmap' en' a' =
        bir_load_from_mem vty' rty' mmap en' a')``,

REPEAT STRIP_TAC >>
MATCH_MP_TAC (bir_load_from_mem_used_addrs_THM) >>
REPEAT STRIP_TAC >>
`~(addr IN (bir_store_in_mem_used_addrs vty v en a))` by (
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DISJOINT] >>
  METIS_TAC[]
) >>
METIS_TAC[bir_store_in_mem_used_addrs_THM]);


val _ = export_theory();
