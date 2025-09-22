structure tinyLib =
struct

local

open HolKernel Parse boolLib bossLib;

open tinyTheory;

in

(* ------------------------------------- *)
(* relevant theorems and definitions     *)
(* ------------------------------------- *)
val lift_thm      = bir_tiny_cm0_mod_lift_THM;
val prog_def      = bir_tiny_prog_def;
val birenvtyl_def = tiny_birenvtyl_def;

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)
val _ = birs_auxLib.prepare_program_lookups lift_thm;

end
end (* struct *)
