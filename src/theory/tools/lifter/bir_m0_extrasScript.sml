open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_exp_liftingTheory
open m0Theory m0_stepTheory;
open bir_lifter_general_auxTheory;
open bir_interval_expTheory
open bir_extra_expsTheory;

(* In order to produce decent BIR code from step theorems,
   the concepts described by the step theorems need to be
   made very explicit. This is mostly due to the fact that
   the step theorems result from partially evaluating the
   machine definitions. However, translating a partial evaluation
   literally is often more cumbersome that translating the abstract
   concept.

   The work for the conditional execution flags is so extensive, that
   it is handled in bir_nzcv_introsScript.sml. Moreover, this theory
   only contains the arm8 specific stuff. *)

val _ = new_theory "bir_m0_extras";


(* Evaluate bitstring constants statically *)

val word4_list = List.tabulate (16, (fn i => wordsSyntax.mk_wordii (i, 4)))

val R_name_EVAL = save_thm ("R_name_EVAL", let
  val thms0 = (List.map (fn w => GEN ``sel:bool`` (EVAL ``R_name sel ^w``)) word4_list)
  val thms1 = List.map (SIMP_RULE (std_ss++QI_ss++boolSimps.LIFT_COND_ss) [boolTheory.COND_EXPAND,
    FORALL_AND_THM]) thms0
  val thm2 = SIMP_RULE std_ss [GSYM CONJ_ASSOC] (LIST_CONJ thms1)
in
  thm2
end);


Theorem EQ_13w_EVAL = LIST_CONJ (map (fn w => EVAL ``^w = 13w:word4``) word4_list)


Theorem EQ_15w_EVAL = LIST_CONJ (map (fn w => EVAL ``^w = 15w:word4``) word4_list)



val RName_distinct = save_thm ("RName_distinct", let
Theorem thm0[local]:
  !r r'.
     r < 17 ==> r' < r ==> ((num2RName r = num2RName r') <=> (r = r'))
Proof
SIMP_TAC arith_ss [m0Theory.num2RName_11]
QED

  val thm1 = REWRITE_RULE [GSYM rich_listTheory.MEM_COUNT_LIST] thm0
  val thm2 = SIMP_RULE std_ss [rich_listTheory.COUNT_LIST_compute,
     rich_listTheory.COUNT_LIST_AUX_compute, listTheory.MEM,
     DISJ_IMP_THM, FORALL_AND_THM, m0Theory.num2RName_thm] thm1
  val thm3 = SIMP_RULE std_ss [GSYM CONJ_ASSOC] thm2
in thm3 end);


(***********************)
(* Lifting Load for m0 *)
(***********************)

Definition m0_mem_half_LE_def:
  m0_mem_half_LE (m:word32 -> word8) a = (m (a + 1w) @@ m a) : word16
End

Definition m0_mem_word_LE_def:
  m0_mem_word_LE (m:word32 -> word8) a =
     (m (a + 3w) @@ ((m (a + 2w) @@ ((m (a + 1w) @@ m a):word16)):word24)) : word32
End

Definition m0_mem_half_BE_def:
  m0_mem_half_BE (m:word32 -> word8) a = (m a @@ m (a+1w)) : word16
End

Definition m0_mem_word_BE_def:
  m0_mem_word_BE (m:word32 -> word8) a =
     (m a @@ ((m (a + 1w) @@ ((m (a + 2w) @@ m (a + 3w)):word16)):word24)) : word32
End

Theorem m0_LIFT_LOAD_WORD_LE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit32)
       (Imm32 (m0_mem_word_LE ms.MEM va))
Proof
SIMP_TAC std_ss [m0_mem_word_LE_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED

Theorem m0_LIFT_LOAD_WORD_BE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_BigEndian Bit32)
       (Imm32 (m0_mem_word_BE ms.MEM va))
Proof
SIMP_TAC std_ss [m0_mem_word_BE_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED


Theorem m0_LIFT_LOAD_HALF_LE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit16)
       (Imm16 (m0_mem_half_LE ms.MEM va))
Proof
SIMP_TAC std_ss [m0_mem_half_LE_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED


Theorem m0_LIFT_LOAD_HALF_BE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_BigEndian Bit16)
       (Imm16 (m0_mem_half_BE ms.MEM va))
Proof
SIMP_TAC std_ss [m0_mem_half_BE_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED


Theorem m0_LIFT_LOAD_BYTE_BE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_BigEndian Bit8)
       (Imm8 (ms.MEM va))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_is_lifted_imm_exp_LOAD_NO_ENDIAN]
QED


Theorem m0_LIFT_LOAD_BYTE_LE:
  !env em ea va (ms:m0_state).
     bir_is_lifted_mem_exp env em ms.MEM ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit8)
       (Imm8 (ms.MEM va))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_is_lifted_imm_exp_LOAD_NO_ENDIAN]
QED


Theorem aligned_1_m0_mem_word:
  (!addr ms. aligned 1 (m0_mem_word_LE ms.MEM addr) = aligned 1 (ms.MEM addr)) /\
  (!addr ms. aligned 1 (m0_mem_half_LE ms.MEM addr) = aligned 1 (ms.MEM addr)) /\
  (!addr ms. aligned 1 (m0_mem_word_BE ms.MEM addr) = aligned 1 (ms.MEM (addr + 3w))) /\
  (!addr ms. aligned 1 (m0_mem_half_BE ms.MEM addr) = aligned 1 (ms.MEM (addr + 1w)))
Proof
`!n:num. (n < 1) <=> (n = 0)` by DECIDE_TAC >>
ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [alignmentTheory.aligned_bit_count_upto,
    bit_count_upto_is_zero, word_bit_def, m0_mem_half_BE_def, m0_mem_word_BE_def,
    m0_mem_half_LE_def, m0_mem_word_LE_def, word_concat_def, word_join_index, w2w]
QED


Theorem aligned_2_m0_mem_word:
  (!addr ms. aligned 2 (m0_mem_word_LE ms.MEM addr) = aligned 2 (ms.MEM addr)) /\
  (!addr ms. aligned 2 (m0_mem_half_LE ms.MEM addr) = aligned 2 (ms.MEM addr)) /\
  (!addr ms. aligned 2 (m0_mem_word_BE ms.MEM addr) = aligned 2 (ms.MEM (addr + 3w))) /\
  (!addr ms. aligned 2 (m0_mem_half_BE ms.MEM addr) = aligned 2 (ms.MEM (addr + 1w)))
Proof
`!n:num. (n < 2) <=> ((n = 0) \/ (n = 1))` by DECIDE_TAC >>
ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [alignmentTheory.aligned_bit_count_upto,
    bit_count_upto_is_zero, word_bit_def, m0_mem_half_BE_def, m0_mem_word_BE_def,
    m0_mem_half_LE_def, m0_mem_word_LE_def, word_concat_def, word_join_index, w2w,
    LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM]
QED


(******************)
(* Store for arm8 *)
(******************)

Definition m0_mem_store_word_LE_def:
  m0_mem_store_word_LE (a:word32) (w:word32) (mmap : (word32 -> word8)) =
   (a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a      =+ (7  >< 0)  w) mmap)))
End

Definition m0_mem_store_word_BE_def:
  m0_mem_store_word_BE (a:word32) (w:word32) (mmap : (word32 -> word8)) =
   (a + 3w =+ ( 7 ><  0) w)
  ((a + 2w =+ (15 ><  8) w)
  ((a + 1w =+ (23 >< 16)  w)
  ((a      =+ (31 >< 24)  w) mmap)))
End

Definition m0_mem_store_half_LE_def:
  m0_mem_store_half_LE (a:word32) (w:word16) (mmap : (word32 -> word8)) =
   (a + 1w =+ (15 >< 8)  w)
  ((a      =+ (7  >< 0)  w) mmap)
End

Definition m0_mem_store_half_BE_def:
  m0_mem_store_half_BE (a:word32) (w:word16) (mmap : (word32 -> word8)) =
   (a + 1w =+ ( 7 >< 0)  w)
  ((a      =+ (15 >< 8)  w) mmap)
End

Definition m0_mem_store_byte_def:
  m0_mem_store_byte (a:word32) (w:word8) (mmap : (word32 -> word8)) =
  ((a      =+ w) mmap)
End


Theorem m0_mem_store_half_BE_32:
  !(a :word32) (w :word32) (mmap :word32 -> word8).
     (a + (1w :word32) =+ (((7 :num) >< (0 :num)) w :word8))
       ((a =+ (((15 :num) >< (8 :num)) w :word8)) mmap) =
     m0_mem_store_half_BE a (w2w w) mmap
Proof
SIMP_TAC (std_ss++wordsLib.SIZES_ss) [m0_mem_store_half_BE_def,
  wordsTheory.word_bits_w2w, holba_auxiliaryTheory.word_extract_bits_w2w,
  w2w_REMOVE_FOLDS]
QED


Theorem m0_mem_store_half_LE_32:
  !(a :word32) (w :word32) (mmap :word32 -> word8).
     (a + (1w :word32) =+ (((15 :num) >< (8 :num)) w :word8))
       ((a =+ (((7 :num) >< (0 :num)) w :word8)) mmap) =
     m0_mem_store_half_LE a (w2w w) mmap
Proof
SIMP_TAC (std_ss++wordsLib.SIZES_ss) [m0_mem_store_half_LE_def,
  wordsTheory.word_bits_w2w, holba_auxiliaryTheory.word_extract_bits_w2w,
  w2w_REMOVE_FOLDS]
QED



val m0_mem_store_LE_FOLDS = save_thm ("m0_mem_store_LE_FOLDS",
let
  val half_THM = REWRITE_RULE [GSYM m0_mem_store_byte_def] m0_mem_store_half_LE_32
  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM m0_mem_store_byte_def, half_THM] (GSYM thm)

  val def_THMS = LIST_CONJ [GSYM m0_mem_store_byte_def, half_THM,
     mk_thm_GEN m0_mem_store_half_LE_def,
     mk_thm_GEN m0_mem_store_word_LE_def]

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM m0_mem_store_byte_def] tm))

  val zero_THM0 = mk_zero_thm m0_mem_store_half_LE_def ``m0_mem_store_half_LE a 0w mmap``;
  val zero_THM1 = REWRITE_RULE [zero_THM0] (mk_zero_thm m0_mem_store_word_LE_def ``m0_mem_store_word_LE a 0w mmap``);

in LIST_CONJ [def_THMS, zero_THM0, zero_THM1] end);


val m0_mem_store_BE_FOLDS = save_thm ("m0_mem_store_BE_FOLDS",
let
  val half_THM = REWRITE_RULE [GSYM m0_mem_store_byte_def] m0_mem_store_half_BE_32
  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM m0_mem_store_byte_def, half_THM] (GSYM thm)

  val def_THMS = LIST_CONJ [GSYM m0_mem_store_byte_def,
     half_THM,
     mk_thm_GEN m0_mem_store_half_BE_def,
     mk_thm_GEN m0_mem_store_word_BE_def]

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM m0_mem_store_byte_def] tm))

  val zero_THM0 = mk_zero_thm m0_mem_store_half_BE_def ``m0_mem_store_half_BE a 0w mmap``;
  val zero_THM1 = REWRITE_RULE [zero_THM0] (mk_zero_thm m0_mem_store_word_BE_def ``m0_mem_store_word_BE a 0w mmap``);

in LIST_CONJ [def_THMS, zero_THM0, zero_THM1] end);



Theorem m0_LIFT_STORE_WORD_LE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (m0_mem_store_word_LE va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_word_LE_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
QED


Theorem m0_LIFT_STORE_WORD_BE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_BigEndian ev)
       (m0_mem_store_word_BE va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_word_BE_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
QED


Theorem m0_LIFT_STORE_HALF_LE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (m0_mem_store_half_LE va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_half_LE_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
QED


Theorem m0_LIFT_STORE_HALF_BE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_BigEndian ev)
       (m0_mem_store_half_BE va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_half_BE_def, bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
QED


Theorem m0_LIFT_STORE_BYTE_LE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
       (m0_mem_store_byte va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_byte_def, bir_is_lifted_mem_exp_STORE_NO_ENDIAN]
QED


Theorem m0_LIFT_STORE_BYTE_BE:
  !env em ea va ev vv ms mem_f.
     bir_is_lifted_mem_exp env em mem_f ==>
     bir_is_lifted_imm_exp env ea (Imm32 va) ==>
     bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
     bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_BigEndian ev)
       (m0_mem_store_byte va vv mem_f)
Proof
SIMP_TAC std_ss [m0_mem_store_byte_def, bir_is_lifted_mem_exp_STORE_NO_ENDIAN]
QED


Theorem m0_LIFT_STORE_WORD_LE_CHANGE_INTERVAL:
  !va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 4 (m0_mem_store_word_LE va vv mem_f) mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss) [m0_mem_store_word_LE_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]
QED


Theorem m0_LIFT_STORE_WORD_BE_CHANGE_INTERVAL:
  !va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 4 (m0_mem_store_word_BE va vv mem_f) mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss) [m0_mem_store_word_BE_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]
QED


Theorem m0_LIFT_STORE_HALF_LE_CHANGE_INTERVAL:
  !va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 2 (m0_mem_store_half_LE va vv mem_f) mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss) [m0_mem_store_half_LE_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]
QED


Theorem m0_LIFT_STORE_HALF_BE_CHANGE_INTERVAL:
  !va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 2 (m0_mem_store_half_BE va vv mem_f) mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss) [m0_mem_store_half_BE_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]
QED


Theorem m0_LIFT_STORE_BYTE_CHANGE_INTERVAL:
  !va vv mem_f. FUNS_EQ_OUTSIDE_WI_size va 1 (m0_mem_store_byte va vv mem_f) mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss) [m0_mem_store_byte_def, WI_MEM_WI_size, WI_ELEM_LIST_compute, w2n_n2w, updateTheory.APPLY_UPDATE_THM, FUNS_EQ_OUTSIDE_WI_size_def]
QED



(********)
(* Misc *)
(********)

Theorem Mode_Handler_INTRO:
  !m. (m = Mode_Thread) <=> (m <> Mode_Handler)
Proof
Cases_on `m` >> SIMP_TAC std_ss [m0Theory.Mode_distinct]
QED

Theorem m0_ror_w2w_remove:
  !w1:word32 w2:word32. 
    (w1 #>> w2n ((w2w w2):word8)) = (w1 #>> w2n w2)
Proof
ONCE_REWRITE_TAC [GSYM ROR_MOD] >>
MP_TAC (Q.SPECL [`8`, `32`] arithmeticTheory.MOD_MULT_MOD) >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [w2w_def, w2n_n2w]
QED


Theorem m0_word_bit_0_ms_aligned:
  !ms:m0_state addr. word_bit 0 (ms.MEM addr) =
                     ~(aligned 1 (ms.MEM addr))
Proof
REPEAT STRIP_TAC >>
`!n:num. (n < 1) <=> (n = 0)` by DECIDE_TAC >>
ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [alignmentTheory.aligned_bit_count_upto,
  bit_count_upto_is_zero, word_bit_def]
QED


Theorem m0_extract_byte:
  !a w mmap.
  ((7 >< 0) (w:word32)):word8 =
  (w2w w)
Proof
MP_TAC (INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:8``, ``:'c`` |-> ``:8``]
   (GSYM wordsTheory.w2w_w2w)) >>
ASM_SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.word_extract_def, w2w_id]
QED

Theorem m0_extract_half:
  !a w mmap.
  ((15 >< 0) (w:word32)):word16 =
  (w2w w)
Proof
MP_TAC (INST_TYPE [``:'a`` |-> ``:32``, ``:'b`` |-> ``:16``, ``:'c`` |-> ``:16``]
   (GSYM wordsTheory.w2w_w2w)) >>
ASM_SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.word_extract_def, w2w_id]
QED


Theorem m0_Shift_C:
  !n w:word32. (0 < n) /\ (n <= 32) ==>
    (((((w2w w):33 word) << n) ' 32) = word_bit (32 - n) w)
Proof
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [word_lsl_def,
  fcpTheory.FCP_BETA, w2w, word_bit_def]
QED


Theorem m0_Shift_N_aux[local]:
  !m n w:'a word.  (m <= dimindex (:'a) - 1) /\ (n <= m) ==>
    (word_bit m (w << n) = word_bit (m - n) w)
Proof
SIMP_TAC (arith_ss++wordsLib.SIZES_ss++boolSimps.CONJ_ss) [word_lsl_def,
  fcpTheory.FCP_BETA, w2w, word_bit_def]
QED

val m0_Shift_N = save_thm ("m0_Shift_N", let
  val thm0 = SPEC ``31:num`` (INST_TYPE [``:'a`` |-> ``:32``] m0_Shift_N_aux)
  val thm1 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm0
in
  thm1
end);


Theorem m0_mask_last_bit_REWR_aux[local]:
  !w. (((31 >< 1) w): (31 word) @@ (0w:word1)):word32 =
      w && ~(1w)
Proof
Cases >>
REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
FULL_SIMP_TAC (arith_ss++boolSimps.EQUIV_EXTRACT_ss++wordsLib.SIZES_ss) [
  word_and_def, fcpTheory.FCP_BETA,
  dimindex_lt_dimword, word_concat_def, w2w,
  word_join_index, word_0, holba_auxiliaryTheory.word_extract_bits_w2w,
  word_bits_def, word_1comp_def, word_index] >>
REPEAT STRIP_TAC >>
`BIT i 1 = (0 = i)` by (
  Q.SUBGOAL_THEN `(1:num) = (2:num) ** 0` SUBST1_TAC >- SIMP_TAC arith_ss [] >>
  REWRITE_TAC [bitTheory.BIT_TWO_POW]
) >>
Cases_on `i` >> FULL_SIMP_TAC arith_ss []
QED


Theorem m0_mask_last_bit_REWR = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_1comp_n2w] m0_mask_last_bit_REWR_aux




Theorem LowestSetBit_ALT_DEF:
  !w. m0$LowestSetBit (w:'a word) = if (w = 0w) then dimindex (:'a) else LEAST i. w ' i
Proof
SIMP_TAC std_ss [LowestSetBit_def, CountLeadingZeroBits_def,
  HighestSetBit_def, word_len_def, word_reverse_thm] >>
GEN_TAC >>
Cases_on `w = 0w` >> (
  ASM_SIMP_TAC intLib.int_ss []
) >>
ASM_SIMP_TAC std_ss [wordsTheory.word_log2_def,
  wordsTheory.LOG2_w2n, word_reverse_thm] >>

Q.ABBREV_TAC `m = LEAST i. word_reverse (w:'a word) ' (dimindex (:'a) - 1 - i)` >>
`dimindex (:'a) - 1 - m < INT_MIN (:'a)` by (
   `dimindex (:'a) <= 2 ** (dimindex (:'a) - 1)` by (
     `dimindex (:'a) - 1 < 2 ** (dimindex (:'a) - 1)` by (
        REWRITE_TAC [arithmeticTheory.X_LT_EXP_X_IFF] >>
        SIMP_TAC std_ss []
     ) >>
     `0 < dimindex (:'a)` by METIS_TAC[DIMINDEX_GT_0] >>
     DECIDE_TAC
   ) >>
   ASM_SIMP_TAC arith_ss [bitTheory.ZERO_LT_TWOEXP, arithmeticTheory.ZERO_LESS_ADD,
     INT_MIN_def]
) >>

ASM_SIMP_TAC std_ss [integer_wordTheory.w2i_n2w_pos] >>

`m = LEAST i. w ' i` by (
  Q.UNABBREV_TAC `m` >>
  ASM_SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [fcpTheory.FCP_BETA, word_reverse_def] >>
  Q.SUBGOAL_THEN `!i. dimindex (:'a) - (dimindex (:'a) - ((i:num) + 1) + 1) =
       if (i <= dimindex (:'a) - 1) then i else dimindex (:'a) - 1` (fn thm => SIMP_TAC std_ss [thm]) >- DECIDE_TAC >>

  `?i. i < dimindex (:'a) /\ w ' i` by (
     FULL_SIMP_TAC std_ss [word_eq_0] >>
     METIS_TAC[]
  ) >>
  Q.ABBREV_TAC `m = LEAST i. w ' i` >>
  `w ' m /\ (!i. i < m ==> ~(w ' i))` by METIS_TAC[whileTheory.LEAST_EXISTS_IMP] >>
  `m < dimindex (:'a)` by (
     `~(i < m)` by METIS_TAC[] >>
     DECIDE_TAC
  ) >>
  numLib.LEAST_ELIM_TAC >>
  CONJ_TAC >- (
    Q.EXISTS_TAC `m` >>
    ASM_SIMP_TAC arith_ss []
  ) >>
  REPEAT STRIP_TAC >>
  rename1 `nn <= dimindex _ - 1` >>
  Cases_on `nn <= dimindex (:'a) - 1` >- (
    FULL_SIMP_TAC arith_ss [] >>
    `~(nn < m) /\ ~(m < nn)` by METIS_TAC[] >>
    DECIDE_TAC
  ) >- (
    Q.PAT_X_ASSUM `!m. _` (MP_TAC o Q.SPEC `dimindex (:'a) - 1`) >>
    FULL_SIMP_TAC arith_ss []
  )
) >>

`m < dimindex (:'a)` by (
  ASM_SIMP_TAC arith_ss [wordsTheory.LEAST_BIT_LT]
) >>
Q.SUBGOAL_THEN `(&dimindex (:'a) - (1:int) - &(dimindex (:'a) - (1:num) - m)) = &m` SUBST1_TAC >- (
  ASM_SIMP_TAC intLib.int_ss [int_arithTheory.INT_NUM_SUB, GSYM integerTheory.INT_ADD]
) >>

ASM_SIMP_TAC intLib.int_ss []
QED



Theorem LowestSetBit_n2w:
  !n. m0$LowestSetBit ((n2w n):'a word) =
      (if (n MOD dimword (:'a) = 0) then dimindex (:'a) else LOWEST_SET_BIT n)
Proof
GEN_TAC >>
Q.SUBGOAL_THEN `(n MOD dimword (:'a) = 0) = (n2w n = (0w:'a word))` SUBST1_TAC >- (
  SIMP_TAC arith_ss [LowestSetBit_ALT_DEF, n2w_11, ZERO_LT_dimword]
) >>
Cases_on `n2w n = (0w:'a word)` >> ASM_SIMP_TAC std_ss [LowestSetBit_ALT_DEF] >>
FULL_SIMP_TAC std_ss [word_eq_0] >>
Q.ABBREV_TAC `m = LEAST i. (n2w n) ' i` >>
`((n2w n):'a word) ' m /\ (!i. i < m ==> ~(((n2w n):'a word) ' i))` by METIS_TAC[whileTheory.LEAST_EXISTS_IMP] >>
`m < dimindex (:'a)` by (
   `~(i < m)` by METIS_TAC[] >>
   DECIDE_TAC
) >>
SIMP_TAC std_ss [bitTheory.LOWEST_SET_BIT_def] >>
numLib.LEAST_ELIM_TAC >>
`BIT m n` by METIS_TAC[word_index] >>
CONJ_TAC >- (
  Q.EXISTS_TAC `m` >>
  ASM_SIMP_TAC std_ss []
) >>
REPEAT STRIP_TAC >>
rename1 `BIT ii n` >>
`~(m < ii)` by METIS_TAC[] >>
`~(ii < m)` suffices_by DECIDE_TAC >>
STRIP_TAC >>
`ii < dimindex (:'a)` by DECIDE_TAC >>
METIS_TAC[word_index]
QED




Theorem m0_rev_folds:
  (!(w :word32).
      (((((23 :num) >< (16 :num)) w :word8) @@
        (((((31 :num) >< (24 :num)) w :word8) @@
         (((((7 :num) >< (0 :num)) w :word8) @@
          (((15 :num) >< (8 :num)) w :word8))
            :word16))
           :word24))
         :word32) =
      word_reverse_16_32 (word_reverse_8_32 w))
Proof
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_reverse_REWRS, word_concat_def, word_join_index, word_extract_def,
  w2w, word_bits_def, fcpTheory.FCP_BETA] >>
SIMP_TAC (arith_ss++ boolSimps.LIFT_COND_ss) []
QED


Theorem m0_revs_folds:
  !w:word32.
    (((sw2sw (w2w (w :word32) :word8) :word24) @@
       (((15 :num) >< (8 :num)) (w :word32) :
           word8))
        :word32) = sw2sw (word_reverse_8_16 (w2w w))
Proof
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
SIMP_TAC (arith_ss++wordsLib.SIZES_ss) [
  word_reverse_REWRS, word_concat_def, word_join_index, word_extract_def,
  w2w, sw2sw, word_bits_def, fcpTheory.FCP_BETA, word_msb_def] >>
SIMP_TAC (arith_ss++ boolSimps.LIFT_COND_ss) []
QED



(****************)
(* Combinations *)
(****************)

Theorem m0_extra_LIFTS_LE = LIST_CONJ [
    m0_LIFT_LOAD_BYTE_LE,
    m0_LIFT_LOAD_HALF_LE,
    m0_LIFT_LOAD_WORD_LE,
    m0_LIFT_STORE_BYTE_LE,
    m0_LIFT_STORE_HALF_LE,
    m0_LIFT_STORE_WORD_LE
]



Theorem m0_extra_LIFTS_BE = LIST_CONJ [
    m0_LIFT_LOAD_BYTE_BE,
    m0_LIFT_LOAD_HALF_BE,
    m0_LIFT_LOAD_WORD_BE,
    m0_LIFT_STORE_BYTE_BE,
    m0_LIFT_STORE_HALF_BE,
    m0_LIFT_STORE_WORD_BE
]



Theorem m0_CHANGE_INTERVAL_THMS = LIST_CONJ [
    m0_LIFT_STORE_WORD_LE_CHANGE_INTERVAL,
    m0_LIFT_STORE_WORD_BE_CHANGE_INTERVAL,
    m0_LIFT_STORE_HALF_LE_CHANGE_INTERVAL,
    m0_LIFT_STORE_HALF_BE_CHANGE_INTERVAL,
    m0_LIFT_STORE_BYTE_CHANGE_INTERVAL]



val extract_byte_RULE = SIMP_RULE std_ss [m0_extract_byte, m0_extract_half];


Theorem m0_extra_FOLDS_GEN = LIST_CONJ [GSYM m0_mem_word_LE_def, GSYM m0_mem_half_LE_def,
             GSYM m0_mem_word_BE_def, GSYM m0_mem_half_BE_def,
             m0_extract_byte, m0_extract_half, m0_mask_last_bit_REWR, m0_Shift_C, m0_Shift_N,
             GSYM word_reverse_REWRS, align_AND_INTROS, m0_word_bit_0_ms_aligned,
             m0_rev_folds, m0_revs_folds, m0_ror_w2w_remove]


Theorem m0_extra_FOLDS_LE = extract_byte_RULE (
  LIST_CONJ [m0_mem_store_LE_FOLDS])


Theorem m0_extra_FOLDS_BE = extract_byte_RULE (
  (LIST_CONJ [m0_mem_store_BE_FOLDS]))



val _ = export_theory();
