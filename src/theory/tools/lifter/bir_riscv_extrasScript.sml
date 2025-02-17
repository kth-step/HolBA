open HolKernel Parse boolLib bossLib;
open wordsTheory
open HolBACoreSimps
open bir_immSyntax
open bir_exp_immTheory
open bir_immTheory
open bir_valuesTheory
open bir_exp_liftingTheory
open riscv_stepTheory
open bir_lifter_general_auxTheory;
open bir_lifting_machinesTheory;
open bir_interval_expTheory bir_extra_expsTheory
open bir_arm8_extrasTheory
open bitstringTheory
open combinTheory
open bir_expTheory;
open bir_exp_memTheory;
open bir_bool_expTheory;
open holba_auxiliaryTheory;

(* In order to produce decent BIR code from step theorems,
 * the concepts described by the step theorems need to be
 * made very explicit. This is mostly due to the fact that
 * the step theorems result from partially evaluating the
 * machine definitions. However, translating a partial evaluation
 * literally is often more cumbersome that translating the abstract
 * concept. *)

val _ = new_theory "bir_riscv_extras";

val _ = wordsLib.guess_lengths()

(********)
(* Load *)
(********)

Definition riscv_mem_load_half_def:
  riscv_mem_load_half (m : (word64 -> word8)) (a:word64) =
  ((m (a + 1w) @@ m a):word16)
End

Definition riscv_mem_load_word_def:
  riscv_mem_load_word (m : word64 -> word8) a =
    (m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a) : word32
End

Definition riscv_mem_load_dword_def:
  riscv_mem_load_dword (m : (word64 -> word8)) (a:word64) =
  (m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
      m (a + 3w) @@ m (a + 2w) @@ m (a + 1w) @@ m a) : word64
End


Theorem riscv_mem_load_word_half:
  !m a. riscv_mem_load_word m a = (m (a + 3w) @@ m (a + 2w) @@ (riscv_mem_load_half m a))
Proof
SIMP_TAC std_ss [riscv_mem_load_half_def, riscv_mem_load_word_def]
QED

Theorem riscv_mem_load_dword_half:
  !m a. riscv_mem_load_dword m a = (m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
      m (a + 3w) @@ m (a + 2w) @@ (riscv_mem_load_half m a))
Proof
SIMP_TAC std_ss [riscv_mem_load_half_def, riscv_mem_load_dword_def]
QED

Theorem riscv_mem_load_dword_word:
  !m a. riscv_mem_load_dword m a = (m (a + 7w) @@ m (a + 6w) @@ m (a + 5w) @@ m (a + 4w) @@
      (riscv_mem_load_word m a))
Proof
SIMP_TAC std_ss [riscv_mem_load_word_def, riscv_mem_load_dword_def]
QED

Theorem riscv_LIFT_LOAD_DWORD:
  !env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM8 ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit64)
       (Imm64 (riscv_mem_load_dword ms.MEM8 va))
Proof
SIMP_TAC std_ss [riscv_mem_load_dword_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED

Theorem riscv_LIFT_LOAD_WORD:
  !env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM8 ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit32)
       (Imm32 (riscv_mem_load_word ms.MEM8 va))
Proof
SIMP_TAC std_ss [riscv_mem_load_word_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED

Theorem riscv_LIFT_LOAD_HALF:
  !env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM8 ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit16)
       (Imm16 (riscv_mem_load_half ms.MEM8 va))
Proof
SIMP_TAC std_ss [riscv_mem_load_half_def, bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE]
QED

Theorem riscv_LIFT_LOAD_BYTE:
  !env em ea va ms.
     bir_is_lifted_mem_exp env em ms.MEM8 ==>
     bir_is_lifted_imm_exp env ea (Imm64 va) ==>
     bir_is_lifted_imm_exp env (BExp_Load em ea BEnd_LittleEndian Bit8)
       (Imm8 (ms.MEM8 va))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_is_lifted_imm_exp_LOAD_NO_ENDIAN]
QED

(* TODO: Make riscv_mem_load_FOLDS with riscv_mem_half_def et.c. *)


(**********)
(* Store  *)
(**********)

Definition riscv_mem_store_dword_def:
  riscv_mem_store_dword (a:word64) (w:word64) (mmap : (word64 -> word8)) =
   (a + 7w =+ (63 >< 56) w)
  ((a + 6w =+ (55 >< 48) w)
  ((a + 5w =+ (47 >< 40) w)
  ((a + 4w =+ (39 >< 32) w)
  ((a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w  =+ (7  >< 0)  w) mmap)))))))
End

Definition riscv_mem_store_word_def:
  riscv_mem_store_word (a:word64) (w:word64) (mmap : (word64 -> word8)) =
   (a + 3w =+ (31 >< 24) w)
  ((a + 2w =+ (23 >< 16) w)
  ((a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)))
End

Definition riscv_mem_store_half_def:
  riscv_mem_store_half (a:word64) (w:word64) (mmap : (word64 -> word8)) =
   (a + 1w =+ (15 >< 8)  w)
  ((a + 0w =+ (7  >< 0)  w) mmap)
End

(* The below theorem are for rewriting the memory representations
 * in the step theorem produced by the lifter.
 * Note that RISC-V is little-endian, although the order of the
 * finite map updates is the reverse of that in ARMv8 lifter output
 * due to differences in the models. *)

Theorem mem_half_word_rev:
  !(a:word64) (w:word64) (mmap:(word64 -> word8)).
  (a  + 0w =+ (7 >< 0)  w)
  ((a + 1w =+ (15  >< 8)  w) mmap) =
    (a + 1w =+ (15 >< 8)  w)
    ((a + 0w =+ (7  >< 0)  w) mmap)
Proof
REPEAT STRIP_TAC >>
irule UPDATE_COMMUTES >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) []
QED

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

Theorem mem_word_rev:
  !(a:word64) (w:word64) (mmap:(word64 -> word8)).
  (a  + 0w =+ (7 >< 0) w)
  ((a + 1w =+ (15 >< 8) w)
  ((a + 2w =+ (23 >< 16)  w)
  ((a + 3w =+ (31  >< 24)  w) mmap))) =
    (a + 3w =+ (31 >< 24) w)
    ((a + 2w =+ (23 >< 16) w)
    ((a + 1w =+ (15 >< 8)  w)
    ((a + 0w =+ (7  >< 0)  w) mmap)))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [UPDATE_def] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
STRIP_TAC >>
WORD_CONTR_TAC
QED

val mem_word_rev_simp = SIMP_RULE (std_ss++wordsLib.WORD_ss++wordsLib.WORD_ARITH_EQ_ss) [] mem_word_rev;

Theorem mem_dword_rev:
  !(a:word64) (w:word64) (mmap:(word64 -> word8)).
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
    ((a + 0w =+ (7  >< 0)  w) mmap)))))))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [UPDATE_def] >>
FULL_SIMP_TAC std_ss [FUN_EQ_THM] >>
STRIP_TAC >>
WORD_CONTR_TAC
QED

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

  val mem_rev_simp_zero_FOLDS = LIST_CONJ 
    (map (GEN_ALL o (SIMP_RULE (std_ss++wordsLib.WORD_ss) []) o (SPECL [``a:word64``, ``0w:word64``]))
    [mem_half_word_rev_simp,
     mem_word_rev_simp,
     mem_dword_rev_simp]);

  fun mk_thm_GEN thm =
    REWRITE_RULE [GSYM mem_store_byte_def] (GSYM thm)

  val def_THMS_apz = LIST_CONJ [GSYM mem_store_byte_def,
    mk_thm_GEN riscv_mem_store_dword_def,
    mk_thm_GEN riscv_mem_store_word_def,
    mk_thm_GEN riscv_mem_store_half_def
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

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm,
        GSYM mem_store_byte_def] tm))

  val word_add1_neq = prove(``a + 1w <> a``, blastLib.BBLAST_TAC >> fs[word1_distinct])
  val upd_add1_comm = GEN_ALL (HO_MATCH_MP UPDATE_COMMUTES word_add1_neq )

  fun mk_zero_thm def_thm tm = GEN_ALL (GSYM (
     SIMP_CONV (std_ss++wordsLib.WORD_ss) [def_thm, upd_add1_comm, GSYM mem_store_byte_def] tm))

  val zero_THM0 = mk_zero_thm riscv_mem_store_half_def ``riscv_mem_store_half a 0w mmap``;

  val zero_THM1 = REWRITE_RULE [zero_THM0] (mk_zero_thm riscv_mem_store_word_def ``riscv_mem_store_word a 0w mmap``);
  val zero_THM2 = REWRITE_RULE [zero_THM1, zero_THM0] (
     mk_zero_thm riscv_mem_store_dword_def ``riscv_mem_store_dword a 0w mmap``);

in LIST_CONJ [mem_rev_simp_FOLDS, mem_rev_simp_zero_FOLDS, def_THMS_apz, def_THMS, THM0, THM1, THM2, zero_THM0, zero_THM1, zero_THM2] end);

Theorem riscv_LIFT_STORE_DWORD:
  !env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env
      (BExp_Store em ea BEnd_LittleEndian ev)
      (riscv_mem_store_dword va vv mem_f)
Proof
SIMP_TAC std_ss [riscv_mem_store_dword_def, elim_zero_for_def_thm,
                 bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE]
QED

(* TODO: For generalizing...
Theorem bir_is_lifted_mem_exp_STORE0_RISCV[local]:
  !guard sr env em ea (va :word64) er (vr : word64) mem_f.
    (size_of_bir_immtype sr = (dimindex (:'r))) ==>
    guard sr ==>
    bir_is_lifted_mem_exp env em (mem_f : word64 -> word8) ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env er (Imm64 vr) ==>
    (!r.
    (bir_store_in_mem_words Bit8 Bit64 (w2bs ((w2w vr):'r word) sr) mem_f BEnd_LittleEndian va = SOME r) ==>
    (bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er sr)) r))
Proof
(* TODO: Rewrite this mess of a proof... *)
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_is_lifted_mem_exp_def, PULL_EXISTS,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_eval_store_BASIC_REWR] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [] >>
`sa = Bit64` by METIS_TAC[(ISPECL [``sa:bir_immtype_t``, ``Bit64``] size_of_bir_immtype_INJ), bir_immTheory.size_of_bir_immtype_def] >>
`sb = Bit8` by METIS_TAC[(ISPECL [``sb:bir_immtype_t``, ``Bit8``] size_of_bir_immtype_INJ), bir_immTheory.size_of_bir_immtype_def] >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>
Cases_on `sr` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [w2n_n2w, w2bs_def, b2n_n2bs, bitTheory.MOD_2EXP_def,
    GSYM dimword_def, w2n_lt] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_store_in_mem_words_def, LET_DEF,
    bir_store_in_mem_def]
) >>
(*
Cases_on `bir_number_of_mem_splits Bit8 sr Bit64` >> FULL_SIMP_TAC std_ss [] >>
rename1 `_ = SOME n` >>
Cases_on `sr` >> (
*)
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
REPEAT BasicProvers.VAR_EQ_TAC >>

  Q.PAT_X_ASSUM `_ = dimindex (:'r)` (fn thm => ASSUME_TAC (GSYM thm)) >>
SIMP_TAC std_ss [bir_load_mmap_w_bir_mmap_n2w_thm, FUN_EQ_THM] >>
subgoal `size_of_bir_immtype Bit64 = dimindex (:64)` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [wordsTheory.dimindex_64]
) >>
STRIP_TAC >>
FULL_SIMP_TAC (std_ss++boolSimps.ETA_ss++wordsLib.WORD_ss) [bir_update_mmap_words_INTRO_w2n, n2w_w2n, w2w_w2w] >>
cheat
QED
*)

val riscv_is_lifted_mem_exp_STORE0_LSB_TAC =
(* TODO: generalize this mess properly... *)
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_is_lifted_mem_exp_def, PULL_EXISTS,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_eval_store_BASIC_REWR] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
FULL_SIMP_TAC std_ss [] >>
`sa = Bit64` by METIS_TAC[(ISPECL [``sa:bir_immtype_t``, ``Bit64``] size_of_bir_immtype_INJ), bir_immTheory.size_of_bir_immtype_def] >>
`sb = Bit8` by METIS_TAC[(ISPECL [``sb:bir_immtype_t``, ``Bit8``] size_of_bir_immtype_INJ), bir_immTheory.size_of_bir_immtype_def] >>
REPEAT (BasicProvers.VAR_EQ_TAC) >>

FULL_SIMP_TAC (std_ss++holBACore_ss) [w2n_n2w, w2bs_def, b2n_n2bs, bitTheory.MOD_2EXP_def,
  GSYM dimword_def, w2n_lt] >>

FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_store_in_mem_words_def, LET_DEF,
  bir_store_in_mem_def] >>

Cases_on `bir_number_of_mem_splits Bit8 Bit32 Bit64` >> FULL_SIMP_TAC std_ss [] >>
rename1 `_ = SOME n` >>

FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
REPEAT BasicProvers.VAR_EQ_TAC >>

SIMP_TAC std_ss [bir_load_mmap_w_bir_mmap_n2w_thm, FUN_EQ_THM] >>
STRIP_TAC >>
FULL_SIMP_TAC (std_ss++boolSimps.ETA_ss++wordsLib.WORD_ss) [bir_update_mmap_words_INTRO_w2n, n2w_w2n, w2w_w2w] >>
subgoal `(63 -- 0) vr = vr` >- (
  SIMP_TAC std_ss [wordsTheory.WORD_BITS_EXTRACT] >>
  irule wordsTheory.WORD_EXTRACT_ID >>
  ASSUME_TAC (ISPEC ``vr:word64`` wordsTheory.w2n_lt) >>
  FULL_SIMP_TAC (arith_ss++wordsLib.WORD_ss) []
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

subgoal `size_of_bir_immtype Bit64 = dimindex (:64)` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [wordsTheory.dimindex_64]

) >>
FULL_SIMP_TAC (std_ss++boolSimps.ETA_ss++wordsLib.WORD_ss) [bir_update_mmap_words_INTRO_w2n, n2w_w2n, w2w_w2w, w2w_id]
;

Theorem riscv_is_lifted_mem_exp_STORE0_8LSB[local]:
  !env em ea (va :word64) er (vr : word64) mem_f.
    bir_is_lifted_mem_exp env em (mem_f : word64 -> word8) ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env er (Imm64 vr) ==>
    (!r.
    (bir_store_in_mem_words Bit8 Bit64 (Imm8 (w2w vr)) mem_f BEnd_LittleEndian va = SOME r) ==>
    (bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit8)) r))
Proof
riscv_is_lifted_mem_exp_STORE0_LSB_TAC
QED

Theorem riscv_is_lifted_mem_exp_STORE0_16LSB[local]:
  !env em ea (va :word64) er (vr : word64) mem_f.
    bir_is_lifted_mem_exp env em (mem_f : word64 -> word8) ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env er (Imm64 vr) ==>
    (!r.
    (bir_store_in_mem_words Bit8 Bit64 (Imm16 (w2w vr)) mem_f BEnd_LittleEndian va = SOME r) ==>
    (bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit16)) r))
Proof
riscv_is_lifted_mem_exp_STORE0_LSB_TAC
QED

Theorem riscv_is_lifted_mem_exp_STORE0_32LSB[local]:
  !env em ea (va :word64) er (vr : word64) mem_f.
    bir_is_lifted_mem_exp env em (mem_f : word64 -> word8) ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env er (Imm64 vr) ==>
    (!r.
    (bir_store_in_mem_words Bit8 Bit64 (Imm32 (w2w vr)) mem_f BEnd_LittleEndian va = SOME r) ==>
    (bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit32)) r))
Proof
riscv_is_lifted_mem_exp_STORE0_LSB_TAC
QED


val STORE_SIMP_RULE = SIMP_RULE std_ss [bir_store_in_mem_words_REWRS];

val riscv_is_lifted_mem_exp_STORE0_8LSB_SIMP =
  STORE_SIMP_RULE riscv_is_lifted_mem_exp_STORE0_8LSB

val riscv_is_lifted_mem_exp_STORE0_16LSB_SIMP =
  STORE_SIMP_RULE riscv_is_lifted_mem_exp_STORE0_16LSB

val riscv_is_lifted_mem_exp_STORE0_32LSB_SIMP =
  STORE_SIMP_RULE riscv_is_lifted_mem_exp_STORE0_32LSB

(* Specialised versions of bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE *)

Theorem riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_8LSB:
  (!env em ea va er vr mem_f.
 bir_is_lifted_mem_exp env em mem_f ==>
 bir_is_lifted_imm_exp env ea (Imm64 va) ==>
 bir_is_lifted_imm_exp env er (Imm64 vr) ==>
 bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit8))
   mem_f(|
     va |-> (7 >< 0) vr
   |))
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC riscv_is_lifted_mem_exp_STORE0_8LSB_SIMP >>
subgoal `((w2w vr):word8) = (7 >< 0) vr` >- (
  blastLib.BBLAST_TAC
) >>
FULL_SIMP_TAC std_ss []
QED

Theorem riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_8LSB_alt:
  (!env em ea va er vr mem_f.
 bir_is_lifted_mem_exp env em mem_f ==>
 bir_is_lifted_imm_exp env ea (Imm64 va) ==>
 bir_is_lifted_imm_exp env er (Imm8 vr) ==>
 bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian er)
   mem_f(| va |-> vr |))
Proof
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_is_lifted_mem_exp_def, PULL_EXISTS,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_eval_store_BASIC_REWR] >>
rpt strip_tac >>
`sa = Bit64` by metis_tac[size_of_bir_immtype_INJ, size_of_bir_immtype_def] >>
`sb = Bit8` by metis_tac[size_of_bir_immtype_INJ, size_of_bir_immtype_def] >>
gs[bir_store_in_mem_def] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_load_mmap_w_bir_mmap_n2w_thm, FUN_EQ_THM] >>
subgoal `size_of_bir_immtype Bit64 = dimindex (:64)` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [dimindex_64]
) >>
gs[bir_update_mmap_words_INTRO_w2n, bitstring_split_SINGLE, bir_update_mmap_words_def]
QED

Theorem riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_16LSB:
  (!env em ea va er vr mem_f.
 bir_is_lifted_mem_exp env em mem_f ==>
 bir_is_lifted_imm_exp env ea (Imm64 va) ==>
 bir_is_lifted_imm_exp env er (Imm64 vr) ==>
 bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit16))
   mem_f(|
     va + 1w |->(15 >< 8) vr; va |-> (7 >< 0) vr
   |))
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC riscv_is_lifted_mem_exp_STORE0_16LSB_SIMP >>
subgoal `(15 >< 8) ((w2w vr):word16) = (15 >< 8) vr` >- (
  blastLib.BBLAST_TAC
) >>
subgoal `(7 >< 0) ((w2w vr):word16) = (7 >< 0) vr` >- (
  blastLib.BBLAST_TAC
) >>
FULL_SIMP_TAC std_ss []
QED

Theorem riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_32LSB:
  (!env em ea va er vr mem_f.
 bir_is_lifted_mem_exp env em mem_f ==>
 bir_is_lifted_imm_exp env ea (Imm64 va) ==>
 bir_is_lifted_imm_exp env er (Imm64 vr) ==>
 bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast er Bit32))
   mem_f(|
     va + 3w |-> (31 >< 24) vr; va + 2w |-> (23 >< 16) vr;
     va + 1w |->(15 >< 8) vr; va |-> (7 >< 0) vr
   |))
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC riscv_is_lifted_mem_exp_STORE0_32LSB_SIMP >>
subgoal `(31 >< 24) ((w2w vr):word32) = (31 >< 24) vr` >- (
  blastLib.BBLAST_TAC
) >>
subgoal `(23 >< 16) ((w2w vr):word32) = (23 >< 16) vr` >- (
  blastLib.BBLAST_TAC
) >>
subgoal `(15 >< 8) ((w2w vr):word32) = (15 >< 8) vr` >- (
  blastLib.BBLAST_TAC
) >>
subgoal `(7 >< 0) ((w2w vr):word32) = (7 >< 0) vr` >- (
  blastLib.BBLAST_TAC
) >>
FULL_SIMP_TAC std_ss []
QED


Theorem riscv_LIFT_STORE_WORD:
  !env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast ev Bit32))
      (riscv_mem_store_word va (vv:word64) mem_f)
Proof
SIMP_TAC std_ss [riscv_mem_store_word_def, elim_zero_for_def_thm,
                 riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_32LSB]
QED

Theorem riscv_LIFT_STORE_HALF:
  !env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast ev Bit16))
      (riscv_mem_store_half va vv mem_f)
Proof
SIMP_TAC std_ss [riscv_mem_store_half_def, elim_zero_for_def_thm,
                 riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_16LSB]
QED

Theorem riscv_LIFT_STORE_BYTE:
  !env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm64 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian (BExp_Cast BIExp_LowCast ev Bit8))
      (mem_store_byte va ((7 >< 0) vv) mem_f)
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_8LSB >>
Q.SUBGOAL_THEN `(7 >< 0) (vv:word64) = ((w2w vv):word8)` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  blastLib.BBLAST_TAC
) >>
FULL_SIMP_TAC std_ss [mem_store_byte_def]
QED

Theorem riscv_LIFT_STORE_BYTE_alt:
  !env em ea va ev vv ms mem_f.
    bir_is_lifted_mem_exp env em mem_f ==>
    bir_is_lifted_imm_exp env ea (Imm64 va) ==>
    bir_is_lifted_imm_exp env ev (Imm8 vv) ==>
    bir_is_lifted_mem_exp env (BExp_Store em ea BEnd_LittleEndian ev)
      (mem_store_byte va vv mem_f)
Proof
SIMP_TAC std_ss [mem_store_byte_def, elim_zero_for_def_thm,
                 riscv_is_lifted_mem_exp_STORE_ENDIAN_BYTE_8LSB_alt]
QED

Theorem riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL:
  !va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 8 (riscv_mem_store_dword va vv mem_f)
                            mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_dword_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
QED

Theorem riscv_LIFT_STORE_WORD_CHANGE_INTERVAL:
  !va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 4 (riscv_mem_store_word va vv mem_f)
                            mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_word_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
QED

Theorem riscv_LIFT_STORE_HALF_CHANGE_INTERVAL:
  !va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 2 (riscv_mem_store_half va vv mem_f)
                            mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [riscv_mem_store_half_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
QED

Theorem riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL:
  !va vv mem_f.
    FUNS_EQ_OUTSIDE_WI_size va 1 (mem_store_byte va vv mem_f)
                            mem_f
Proof
SIMP_TAC (list_ss++wordsLib.WORD_ss)
         [mem_store_byte_def, WI_MEM_WI_size, WI_ELEM_LIST_compute,
          w2n_n2w, updateTheory.APPLY_UPDATE_THM,
          FUNS_EQ_OUTSIDE_WI_size_def]
QED

(**************************************)
(* 6 LSBs - for RV64I SLL, SRL, et.c. *)
(**************************************)

local
  fun power b e =
    if e = 0
    then 1
    else b * power b (e-1);
in
fun get_bitmask_word final_bit size =
  wordsSyntax.mk_wordii ((power 2 final_bit) - 1, size)
end
;

val thm_t =
``!env w e.
  bir_is_lifted_imm_exp env e (Imm64 w) ==>
  bir_is_lifted_imm_exp env (BExp_BinExp BIExp_And (BExp_Const (Imm64 (^(get_bitmask_word 6 64)))) e)
    (Imm64 ((w2w (((5 >< 0) w):word6)):word64))``;

Theorem riscv_is_lifted_imm_exp_6LSBs[local]:
  ^thm_t
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
   bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
   bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY] >>
blastLib.BBLAST_TAC
QED

(*************************************************)
(* 5 LSBs (32-bit) - for RV64I SLLW, SRLW, et.c. *)
(*************************************************)

Theorem riscv_is_lifted_imm_exp_5LSBs[local]:
  !env w e.
  bir_is_lifted_imm_exp env e (Imm64 w) ==>
  bir_is_lifted_imm_exp env (BExp_BinExp BIExp_And (BExp_Const (Imm32 (^(get_bitmask_word 5 32)))) (BExp_Cast BIExp_LowCast e Bit32))
    (Imm32 ((w2w (((4 >< 0) w):word5)):word32))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
   bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
   bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY] >>
blastLib.BBLAST_TAC
QED

(*************************************************)
(* 8 LSBs (8-bit) - for SB                       *)
(*************************************************)

Theorem riscv_is_lifted_imm_exp_8LSBs[local]:
  !env w e.
  bir_is_lifted_imm_exp env e (Imm64 w) ==>
  bir_is_lifted_imm_exp env (BExp_Cast BIExp_LowCast e Bit8)
    (Imm8 ((7 >< 0) w))
Proof
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
   bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
blastLib.BBLAST_TAC
QED

(********************************************************************)
(* 32 LSBs - for 32-bit instructions (ending in "W") of RV64I       *)
(********************************************************************)

Theorem riscv_is_lifted_imm_exp_32LSBsLC[local]:
  !env w e.
  bir_is_lifted_imm_exp env e (Imm64 w) ==>
  bir_is_lifted_imm_exp env (BExp_Cast BIExp_LowCast e Bit32)
    (Imm32 ((31 >< 0) w))
Proof
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
   bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
blastLib.BBLAST_TAC
QED

(*************************************************************************)
(* 64 MSBs (of 128-bit) - for multiplication instructions in RV64M       *)
(*************************************************************************)

Theorem riscv_is_lifted_imm_exp_64MSBs[local]:
  !env w e.
  bir_is_lifted_imm_exp env e (Imm128 w) ==>
  bir_is_lifted_imm_exp env (BExp_Cast BIExp_HighCast e Bit64)
    (Imm64 ((127 >< 64) w))
Proof
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
   bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2wh_def]
QED

(*******************************)
(* Greater-than-or-equal       *)
(*******************************)

Theorem riscv_is_lifted_imm_exp_GE:
  !env w1 w2 e1 e2.
      bir_is_lifted_imm_exp env e1 (Imm64 w1) ==>
      bir_is_lifted_imm_exp env e2 (Imm64 w2) ==>
      bir_is_lifted_imm_exp env (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_SignedLessThan e1 e2))
        (bool2b (w1 >= w2))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  bir_unary_exp_BOOL_OPER_EVAL, WORD_NOT_LESS,
                      WORD_GREATER_EQ]
QED

(****************************************)
(* Unsigned greater-than-or-equal       *)
(****************************************)

Theorem riscv_is_lifted_imm_exp_GEU:
  !env w1 w2 e1 e2.
      bir_is_lifted_imm_exp env e1 (Imm64 w1) ==>
      bir_is_lifted_imm_exp env e2 (Imm64 w2) ==>
      bir_is_lifted_imm_exp env (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_LessThan e1 e2))
        (bool2b (w1 >=+ w2))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  bir_unary_exp_BOOL_OPER_EVAL, GSYM WORD_NOT_LOWER_EQUAL, GSYM WORD_HIGHER_EQ]
QED


(****************)
(* Add to sub   *)
(****************)

Theorem word_add_to_sub_GEN:
  !w:'a word n.
   INT_MAX (:'a) < n /\ n < dimword (:'a) ==>
   (w + n2w n = w - n2w (dimword (:'a) - n))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [word_sub_def,
  word_2comp_n2w]
QED

val word_add_to_sub_TYPES = save_thm ("word_add_to_sub_TYPES",
let
  fun inst wty =
    INST_TYPE [``:'a`` |-> wty] word_add_to_sub_GEN;

  val thm1 = LIST_CONJ ([inst ``:32``, inst ``:64``, inst ``:16``, inst ``:8``])
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] thm1
in
  thm2
end)

(****************************************)
(* Lifting 2-word predicates            *)
(* (related to system register entries) *)
(****************************************)
(* This is a very ugly solution, since we don't have 2-bit
 * immediates... *)
(* TODO: Do the same for 5-bit immediates (mstatus.VM) *)

(* For specialisation of theorem with concrete values.
 * Apparently it doesn't work with an abstract :word2... *)
local
  fun power b e =
    if e = 0
    then 1
    else b * power b (e-1);

  fun specialise_word' word_size thm 0     thm_acc =
    let
      val word = wordsSyntax.mk_wordii(0, word_size)
      val new_thm =
        SPEC word thm
    in
      (new_thm::thm_acc)
    end
    | specialise_word' word_size thm value thm_acc =
    let
      val word = wordsSyntax.mk_wordii(value, word_size)
      val new_thm =
        SPEC word thm
    in
      specialise_word' word_size thm (value-1) (new_thm::thm_acc)
    end

in
fun specialise_word thm =
  let
    val word_size =
      (Arbnum.toInt o wordsSyntax.size_of o fst o
         dest_forall o concl) thm
    val max_val = (power 2 word_size) - 1
  in
    LIST_CONJ (specialise_word' word_size thm max_val [])
  end
end;

val riscv_is_lifted_imm_exp_2EQ_GEN =
  store_thm ("riscv_is_lifted_imm_exp_2EQ_GEN",
  ``!w2 env w1 e1 e2.
      bir_is_lifted_imm_exp env e1 (Imm8 (w2w w1)) ==>
      bir_is_lifted_imm_exp env e2 (Imm8 (w2w w2)) ==>
      bir_is_lifted_imm_exp env (BExp_BinPred BIExp_Equal e1 e2)
        (bool2b (w1 = (w2:word2)))``,

wordsLib.Cases_word_value >> (
  SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
    bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
    BType_Bool_def] >>
  blastLib.BBLAST_TAC
)
);

val riscv_is_lifted_imm_exp_2EQ = 
  SIMP_RULE (std_ss++wordsLib.WORD_ss) [] (specialise_word riscv_is_lifted_imm_exp_2EQ_GEN);

(* 0 -> 31 *)
val riscv_is_lifted_imm_exp_5EQ_GEN =
  store_thm ("riscv_is_lifted_imm_exp_5EQ_GEN",
  ``!w2 env w1 e1 e2.
      bir_is_lifted_imm_exp env e1 (Imm8 (w2w w1)) ==>
      bir_is_lifted_imm_exp env e2 (Imm8 (w2w w2)) ==>
      bir_is_lifted_imm_exp env (BExp_BinPred BIExp_Equal e1 e2)
        (bool2b (w1 = (w2:word5)))``,

wordsLib.Cases_word_value >> (
  SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
    bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
    BType_Bool_def] >>
  blastLib.BBLAST_TAC
)
);

val riscv_is_lifted_imm_exp_5EQ = 
  SIMP_RULE (std_ss++wordsLib.WORD_ss) [] (specialise_word riscv_is_lifted_imm_exp_5EQ_GEN);

(*******************************************************)
(* RISC-V predicates are usually cast to 64-bit format *)
(*******************************************************)
(* TODO: Check that this cannot also be solved by some
 * simple rewriting to a format compatible with existing
 * lifting theorems. *)
(* TODO: Move to auxiliary *)
Theorem v2w_ground1:
  (v2w [T] = 1w) /\ (v2w [F] = 0w)
Proof
SIMP_TAC (std_ss++bitstringLib.v2w_n2w_ss) []
QED


val thm_t = build_immtype_t_conj
``!s bo env (w1:'a word) (w2 :'a word) e1 e2.
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_UnsignedCast (BExp_BinPred bo e1 e2) Bit64)
        (Imm64 (v2w [bir_bin_pred_GET_OPER bo w1 w2]))``;

Theorem riscv_is_lifted_imm_exp_BIN_PRED0[local]:
  ^thm_t
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  bool2b_def] >>
REPEAT STRIP_TAC >> (
  Cases_on `bir_bin_pred_GET_OPER bo w1 w2` >> (
    FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [bool2w_def, v2w_ground1]
  )
)
QED


val riscv_is_lifted_imm_exp_BIN_PRED = save_thm ("riscv_is_lifted_imm_exp_BIN_PRED",
let
  val thm0 = riscv_is_lifted_imm_exp_BIN_PRED0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);

(****************)
(* Combinations *)
(****************)

Theorem riscv_extra_LIFTS = LIST_CONJ [
    riscv_LIFT_LOAD_DWORD,
    riscv_LIFT_LOAD_WORD,
    riscv_LIFT_LOAD_HALF,
    riscv_LIFT_LOAD_BYTE,
    riscv_LIFT_STORE_BYTE,
    riscv_LIFT_STORE_BYTE_alt,
    riscv_LIFT_STORE_HALF,
    riscv_LIFT_STORE_WORD,
    riscv_LIFT_STORE_DWORD,
    riscv_is_lifted_imm_exp_BIN_PRED,
    riscv_is_lifted_imm_exp_6LSBs,
    riscv_is_lifted_imm_exp_5LSBs,
    riscv_is_lifted_imm_exp_8LSBs,
    riscv_is_lifted_imm_exp_32LSBsLC,
    riscv_is_lifted_imm_exp_64MSBs,
    riscv_is_lifted_imm_exp_GE,
    riscv_is_lifted_imm_exp_GEU,
    (* CSR stuff *)
    riscv_is_lifted_imm_exp_2EQ,
    riscv_is_lifted_imm_exp_5EQ]


Theorem riscv_CHANGE_INTERVAL_THMS = LIST_CONJ [riscv_LIFT_STORE_DWORD_CHANGE_INTERVAL,
             riscv_LIFT_STORE_WORD_CHANGE_INTERVAL,
             riscv_LIFT_STORE_HALF_CHANGE_INTERVAL,
             riscv_LIFT_STORE_BYTE_CHANGE_INTERVAL]


Theorem riscv_extra_FOLDS = LIST_CONJ [GSYM riscv_mem_load_dword_def,
             GSYM riscv_mem_load_word_def,
             GSYM riscv_mem_load_half_def,
             GSYM riscv_mem_load_word_half,
             GSYM riscv_mem_load_dword_half,
             GSYM riscv_mem_load_dword_word,
             riscv_mem_store_FOLDS, w2w_REMOVE_FOLDS, GSYM word_reverse_REWRS,
             word_shift_extract_ID,
             (* For REM and REMW instructions *)
             word_rem_def]

Theorem bir_load_from_mem_riscv_mem_load_dword:
 !b f b1 ms map w_ref w_deref.
  ms.MEM8 = (\a. n2w (bir_load_mmap map (w2n a))) /\
  bir_load_from_mem Bit8 Bit64 Bit64 map BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref) ==>
  riscv_mem_load_dword ms.MEM8 w_ref = w_deref
Proof
 rw [riscv_mem_load_dword_def] >>
 fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
 `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def
 ]
QED

Theorem riscv_mem_load_dword_bir_load_from_mem:
 !ms f mm w_ref w_deref.
 riscv_mem_load_dword ms.MEM8 w_ref = w_deref /\
 ms.MEM8 = (\a. n2w (bir_load_mmap mm (w2n a))) ==>
 bir_load_from_mem Bit8 Bit64 Bit64 mm BEnd_LittleEndian (w2n w_ref) = SOME (Imm64 w_deref)
Proof
 rw [riscv_mem_load_dword_def] >>
 fs [bir_exp_memTheory.bir_load_from_mem_REWRS] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n_add_SIZES] >>
 `size_of_bir_immtype Bit64 = dimindex(:64)` by rw [size_of_bir_immtype_def] >>
 fs [bir_exp_memTheory.bir_mem_addr_w2n] >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def
 ]
QED

val _ = export_theory();
