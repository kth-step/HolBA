open HolKernel boolLib Parse bossLib;

open BasicProvers simpLib metisLib;

open numTheory arithmeticTheory int_bitwiseTheory pairTheory combinTheory wordsTheory;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;

open bir_programSyntax bir_program_labelsTheory bir_immTheory;

open mod2Theory;

val _ = new_theory "mod2_prop";

(* top-level relation between pre and post RISC-V states *)
Definition mod2_spec_def:
 mod2_spec_def ms ms' : bool =
  let input = ms.c_gpr ms.procID 0w in
  let output = ms'.c_gpr ms'.procID 0w in
  (w2n output) = (w2n input) MOD 2
End

val _ = export_theory ();
