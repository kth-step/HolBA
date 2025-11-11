structure aes_o0Lib =
struct

local

open HolKernel Parse boolLib bossLib;

open aesTheory;

in

(* ------------------------------------- *)
(* relevant theorems and definitions     *)
(* ------------------------------------- *)
val lift_thm      = bir_o0_aes_cm0_mod_lift_THM;
val prog_def      = bir_o0_aes_prog_def;
val birenvtyl_def = o0_aes_birenvtyl_def;

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)
val _ = birs_auxLib.prepare_program_lookups lift_thm;

end
end (* struct *)
