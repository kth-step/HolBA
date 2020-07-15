open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_exp_liftingTheory
open riscv_stepTheory
open bir_lifter_general_auxTheory;
open bir_lifting_machinesTheory;
open bir_interval_expTheory bir_extra_expsTheory
open bitstringTheory

(* TODO: This file is still entirely WIP. Draw inspiration from
 *       the corresponding ARM8 and M0 files. *)

(* In order to produce decent BIR code from step theorems,
 * the concepts described by the step theorems need to be
 * made very explicit. This is mostly due to the fact that
 * the step theorems result from partially evaluating the
 * machine definitions. However, translating a partial evaluation
 * literally is often more cumbersome that translating the abstract
 * concept. *)

val _ = new_theory "bir_riscv_extras";

(**********)
(* Store  *)
(**********)
val rv_mem_store_dword_def = Define `
  rv_mem_store_dword (a:word64) (w:word64) (mmap : (word64 -> word8)) =
    (a + 0w =+ (7 >< 0) w)
   ((a + 1w =+ (15 >< 8) w)
   ((a + 2w =+ (23 >< 16) w)
   ((a + 3w =+ (31 >< 24) w)
   ((a + 4w =+ (39 >< 32) w)
   ((a + 5w =+ (47 >< 40) w)
   ((a + 6w =+ (55 >< 48)  w)
   ((a + 7w  =+ (63  >< 56)  w) mmap)))))))`;

val rv_mem_store_word_def = Define `
  rv_mem_store_word (a:word64) (w:word32) (mmap : (word64 -> word8)) =
    (a + 0w =+ (7 >< 0) w)
   ((a + 1w =+ (15 >< 8) w)
   ((a + 2w =+ (23 >< 16)  w)
   ((a + 3w =+ (31  >< 24)  w) mmap)))
`;

val rv_mem_store_half_def = Define `
  rv_mem_store_half (a:word64) (w:word16) (mmap : (word64 -> word8)) =
    (a + 0w =+ (7 >< 0)  w)
   ((a + 1w =+ (15  >< 8)  w) mmap)
`;

val rv_mem_store_byte_def = Define `
  rv_mem_store_byte (a:word64) (w:word8) (mmap : (word64 -> word8)) =
    ((a      =+ w) mmap)
`;

val elim_zero_for_def_thm =
  GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``a + 0w  =+ w``);

val riscv_LIFT_STORE_DWORD = store_thm ("riscv_LIFT_STORE_DWORD",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env
      (BExp_Store em ea BEnd_LittleEndian ev)
      (rv_mem_store_dword va vv mem_f)
``,

SIMP_TAC std_ss [rv_mem_store_dword_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

val riscv_LIFT_STORE_WORD = store_thm ("riscv_LIFT_STORE_WORD",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (rv_mem_store_word va vv mem_f)
``,

SIMP_TAC std_ss [rv_mem_store_word_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

val riscv_LIFT_STORE_HALF = store_thm ("riscv_LIFT_STORE_HALF",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (rv_mem_store_half va vv mem_f)
``,

SIMP_TAC std_ss [rv_mem_store_half_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

val riscv_LIFT_STORE_BYTE = store_thm ("riscv_LIFT_STORE_BYTE",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (rv_mem_store_byte va vv mem_f)``,

SIMP_TAC std_ss [rv_mem_store_byte_def,
                 bir_is_lifted_mem_exp_STORE_NO_ENDIAN]
);

val riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 8 (rv_mem_store_dword va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [rv_mem_store_dword_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_WORD_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_WORD_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 4 (rv_mem_store_word va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [rv_mem_store_word_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_HALF_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_HALF_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 2 (rv_mem_store_half va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [rv_mem_store_half_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 1 (rv_mem_store_byte va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [rv_mem_store_byte_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

(****************)
(* Add to sub   *)
(****************)

val word_add_to_sub_GEN = store_thm ("word_add_to_sub_GEN",
``!w:'a word n.

   INT_MAX (:'a) < n /\ n < dimword (:'a) ==>
   (w + n2w n = w - n2w (dimword (:'a) - n))``,

REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [wordsTheory.word_sub_def,
  wordsTheory.word_2comp_n2w]);

val word_add_to_sub_TYPES = save_thm ("word_add_to_sub_TYPES",
let
  fun inst wty =
    INST_TYPE [``:'a`` |-> wty] word_add_to_sub_GEN;

  val thm1 = LIST_CONJ ([inst ``:32``, inst ``:64``, inst ``:16``, inst ``:8``])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm1
in
  thm2
end)

(****************)
(* Combinations *)
(****************)

val riscv_extra_LIFTS = save_thm ("riscv_extra_LIFTS",
  LIST_CONJ [TRUTH] (* TODO: What should be here? *)
);

(* TODO: What should be here? *)
val riscv_CHANGE_INTERVAL_THMS =
  save_thm ("riscv_CHANGE_INTERVAL_THMS",
  LIST_CONJ [riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL,
             riscv_LIFT_STORE_WORD_CHANGE_INTERVAL,
             riscv_LIFT_STORE_HALF_CHANGE_INTERVAL,
             riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL]
);

val riscv_extra_FOLDS = save_thm ("riscv_extra_FOLDS",
  LIST_CONJ [w2w_REMOVE_FOLDS, GSYM word_reverse_REWRS,
             word_shift_extract_ID]
);

val _ = export_theory();
