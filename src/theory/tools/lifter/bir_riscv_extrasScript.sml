open HolKernel Parse boolLib bossLib;
open wordsTheory
open bir_exp_liftingTheory
open riscv_stepTheory
open bir_lifter_general_auxTheory;
open bir_lifting_machinesTheory;
open bir_interval_expTheory bir_extra_expsTheory
open bir_arm8_extrasTheory
open bitstringTheory
open combinTheory

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

val riscv_mem_store_dword_def = Define `riscv_mem_store_dword (a:word64) w (mmap : (word64 -> word8)) =
   (a + 7w =+ (63 >< 56) w)
  ((a + 6w =+ (55 >< 48) w)
  ((a + 5w =+ (47 >< 40) w)
  ((a + 4w =+ (39 >< 32) w)
  ((a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w  =+ (7  >< 0)  w) mmap)))))))`;

val riscv_mem_store_word_def = Define `riscv_mem_store_word (a:word64) w (mmap : (word64 -> word8)) =
   (a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)))`;

val riscv_mem_store_half_def = Define `riscv_mem_store_half (a:word64) w (mmap : (word64 -> word8)) =
   (a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)`;


(* The below theorem are for rewriting the memory representations
 * in the step theorem produced by the lifter.
 * Note that RISC-V is little-endian, although the order of the
 * finite map updates is the reverse of that in ARMv8 lifter output
 * due to differences in the models. *)

val mem_half_word_rev = store_thm("mem_half_word_rev",
``!(a:word64) w (mmap:(word64 -> word8)).
  (a  + 0w =+ (7 >< 0)  w)
  ((a + 1w =+ (15  >< 8)  w) mmap) =
    (a + 1w =+ (15 >< 8)  w)
    ((a + 0w =+ (7  >< 0)  w) mmap)``,

REPEAT STRIP_TAC >>
irule UPDATE_COMMUTES >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) []
);

val mem_half_word_rev_simp = SIMP_RULE (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) [] mem_half_word_rev;

fun prove_word_assum_contr tm1 tm2 =
  let
    val conj = mk_conj (tm1, tm2)
    val contr = mk_eq (conj, F)
  in
    prove(contr, blastLib.FULL_BBLAST_TAC)
  end
;

(* Tactic for proving contradictions between two assumptions on
 * word arithmetic using incremental reasoning, currently not
 * generalised beyond the context of preventing timeouts in proof
 * of mem_dword_rev *)
val WORD_CONTR_TAC =
  REPEAT (
    NTAC 2 CASE_TAC >> (
      TRY (
	Q.PAT_ASSUM `a + b = c`
	  (fn thm1 =>
	    FIRST_ASSUM
	      (fn thm2 =>
		let
		  val tm1 = concl thm1
		  val tm2 = concl thm2
		in
		  if is_neg tm2
		  then FAIL_TAC ""
		  else if term_eq tm1 tm2
		  then FAIL_TAC ""
		  else ASSUME_TAC (prove_word_assum_contr tm1 tm2)
		end
	      )
	  ) >>
	REV_FULL_SIMP_TAC std_ss []
      )
    )
  );

val mem_word_rev = store_thm("mem_word_rev",
``!(a:word64) w (mmap:(word64 -> word8)).
  (a  + 0w =+ (7 >< 0) w)
  ((a + 1w =+ (15 >< 8) w)
  ((a + 2w =+ (23 >< 16)  w)
  ((a + 3w =+ (31  >< 24)  w) mmap))) =
    (a + 3w =+ (31 >< 24) w)
    ((a + 2w =+ (23 >< 16) w)
    ((a + 1w =+ (15 >< 8)  w)
    ((a + 0w =+ (7  >< 0)  w) mmap)))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [UPDATE_def] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
STRIP_TAC >>
WORD_CONTR_TAC
);

val mem_word_rev_simp = SIMP_RULE (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) [] mem_word_rev;

val mem_dword_rev = store_thm("mem_dword_rev",
``!(a:word64) w (mmap:(word64 -> word8)).
  (a  + 0w =+ (7 >< 0) w)
  ((a + 1w =+ (15 >< 8) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 3w =+ (31 >< 24) w)
  ((a + 4w =+ (39 >< 32) w)
  ((a + 5w =+ (47 >< 40) w)
  ((a + 6w =+ (55 >< 48)  w)
  ((a + 7w  =+ (63  >< 56)  w) mmap))))))) =
    (a + 7w =+ (63 >< 56) w)
    ((a + 6w =+ (55 >< 48) w)
    ((a + 5w =+ (47 >< 40) w)
    ((a + 4w =+ (39 >< 32) w)
    ((a + 3w =+ (31 >< 24) w)
    ((a + 2w =+ (23 >< 16) w)
    ((a + 1w =+ (15 >< 8)  w)
    ((a + 0w =+ (7  >< 0)  w) mmap)))))))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [UPDATE_def] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
STRIP_TAC >>
WORD_CONTR_TAC
);

val mem_dword_rev_simp = SIMP_RULE (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) [] mem_dword_rev;

val elim_zero_for_def_thm =
  GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``a + 0w  =+ w``);

(* Essentially copied from ARMv8... *)
val riscv_mem_store_FOLDS = save_thm ("riscv_mem_store_FOLDS",
let
  val mem_rev_simp_FOLDS = LIST_CONJ [
    mem_half_word_rev_simp,
    mem_word_rev_simp,
    mem_dword_rev_simp];

  val thm0 = GSYM mem_store_byte_def
  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM mem_store_byte_def] (GSYM thm)

  val def_THMS_apz = LIST_CONJ [mk_thm_GEN riscv_mem_store_dword_def,
    mk_thm_GEN riscv_mem_store_word_def,
    mk_thm_GEN riscv_mem_store_half_def,
    GSYM mem_store_byte_def
  ];

  val elim_zero_thm =
    GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``mem_store_byte (a+0w) w mmap``);
  val def_THMS = REWRITE_RULE [elim_zero_thm] def_THMS_apz;

  (* These theorems come into play when, for example, half of a word store has been recognized as
   * a half-word store. *)
  fun mk_partial_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM mem_store_byte_def] tm))
  val THM0 = mk_partial_thm riscv_mem_store_half_def ``riscv_mem_store_half a w mmap``;
  val THM1 = REWRITE_RULE [THM0] (mk_partial_thm riscv_mem_store_word_def ``riscv_mem_store_word a w mmap``);
  val THM2 = REWRITE_RULE [THM1, THM0] (
     mk_partial_thm riscv_mem_store_dword_def ``riscv_mem_store_dword a w mmap``);

in LIST_CONJ [mem_rev_simp_FOLDS, def_THMS_apz, def_THMS, THM0, THM1, THM2] end);

val riscv_LIFT_STORE_DWORD = store_thm ("riscv_LIFT_STORE_DWORD",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env
      (BExp_Store em ea BEnd_LittleEndian ev)
      (riscv_mem_store_dword va vv mem_f)
``,

SIMP_TAC std_ss [riscv_mem_store_dword_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

val riscv_LIFT_STORE_WORD = store_thm ("riscv_LIFT_STORE_WORD",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm32 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (riscv_mem_store_word va vv mem_f)
``,

SIMP_TAC std_ss [riscv_mem_store_word_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

(*
(* It seems theorems like this are needed since you can (partially) store longer words using
 * instructions for storing smaller ones. *)
val riscv_LIFT_STORE_WORD_64 = store_thm ("riscv_LIFT_STORE_WORD_64",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (riscv_mem_store_word va vv mem_f)
``,

SIMP_TAC std_ss [riscv_mem_store_word_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);
*)

val riscv_LIFT_STORE_HALF = store_thm ("riscv_LIFT_STORE_HALF",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm16 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (riscv_mem_store_half va vv mem_f)
``,

SIMP_TAC std_ss [riscv_mem_store_half_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
);

val riscv_LIFT_STORE_BYTE = store_thm ("riscv_LIFT_STORE_BYTE",
``!env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (mem_store_byte va vv mem_f)``,

SIMP_TAC std_ss [mem_store_byte_def,
                 bir_is_lifted_mem_exp_STORE_NO_ENDIAN]
);

val riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 8 (riscv_mem_store_dword va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_dword_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_WORD_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_WORD_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 4 (riscv_mem_store_word va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_word_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_HALF_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_HALF_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 2 (riscv_mem_store_half va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_half_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
);

val riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL =
  store_thm ("riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL",
``!va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 1 (mem_store_byte va vv mem_f)
                            mem_f
``,

SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [mem_store_byte_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
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
  LIST_CONJ [(*riscv_LIFT_LOAD_BYTE,
    riscv_LIFT_LOAD_HALF,
    riscv_LIFT_LOAD_WORD,
    riscv_LIFT_LOAD_DWORD,*)
    riscv_LIFT_STORE_BYTE,
    riscv_LIFT_STORE_HALF,
    riscv_LIFT_STORE_WORD,
    riscv_LIFT_STORE_DWORD]
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
  LIST_CONJ [riscv_mem_store_FOLDS, w2w_REMOVE_FOLDS, GSYM word_reverse_REWRS,
             word_shift_extract_ID]
);

val _ = export_theory();
(*


             mem_store_byte (ms.c_gpr ms.procID (2w :word5) + (11w :word64))
               (((31 :num) >< (24 :num)) (ms.c_gpr ms.procID (14w :word5)) :
                word8)
               (mem_store_byte
                  (ms.c_gpr ms.procID (2w :word5) + (10w :word64))
                  (((23 :num) >< (16 :num))
                     (ms.c_gpr ms.procID (14w :word5)) :word8)
                  (riscv_mem_store_half
                     (ms.c_gpr ms.procID (2w :word5) + (8w :word64))
                     (ms.c_gpr ms.procID (14w :word5)) ms.MEM8));*)
