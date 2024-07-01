open HolKernel Parse boolLib bossLib;

open wordsLib wordsSyntax;

open cv_transLib cv_primTheory cv_stdTheory;
open cv_computeLib cv_stdTheory;

val _ = new_theory "cv_word";

Definition cv_word64_add_def:
  (* cv_word64_add (x:cv) (y:cv) = cv_mod (cv_add x y) (Num (dimword(:word64))) *)
  cv_word64_add (x:cv) (y:cv) = cv_mod (cv_add x y) (Num (0x10000000000000000))
End

val _ = export_theory();
