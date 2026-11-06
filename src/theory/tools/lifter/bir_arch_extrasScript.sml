open HolKernel Parse boolLib bossLib;
open wordsTheory

(* Definitions and theorems used by the lifting extras of several
   architectures (bir_arm8_extras, bir_riscv_extras). *)

val _ = new_theory "bir_arch_extras";


(****************)
(* Store a byte *)
(****************)

Definition mem_store_byte_def:
  mem_store_byte (a:word64) (w:word8) (mmap : (word64 -> word8)) =
  ((a      =+ w) mmap)
End

Theorem elim_zero_for_def_thm =
  GEN_ALL (SIMP_CONV (std_ss++wordsLib.WORD_ss) [] ``a + 0w  =+ w``);


(****************)
(* Add to sub   *)
(****************)

Theorem word_add_to_sub_GEN:
  !w:'a word n.
   INT_MAX (:'a) < n /\ n < dimword (:'a) ==>
   (w + n2w n = w - n2w (dimword (:'a) - n))
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC arith_ss [wordsTheory.word_sub_def,
  wordsTheory.word_2comp_n2w]
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


val _ = export_theory();
