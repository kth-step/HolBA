structure modexp_asmLib =
struct

local

open HolKernel Parse boolLib bossLib;

open modexpTheory;

in

(* ------------------------------------- *)
(* relevant theorems and definitions     *)
(* ------------------------------------- *)
val lift_thm      = bir_asm_modexp_cm0_mod_lift_THM;
val prog_def      = bir_asm_modexp_prog_def;
val birenvtyl_def = asm_modexp_birenvtyl_def;

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)
val _ = birs_auxLib.prepare_program_lookups lift_thm;

end
end (* struct *)
