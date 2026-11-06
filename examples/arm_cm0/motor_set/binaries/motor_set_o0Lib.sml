structure motor_set_o0Lib =
struct

local

open HolKernel Parse boolLib bossLib;

open motorTheory;

in

(* ------------------------------------- *)
(* relevant theorems and definitions     *)
(* ------------------------------------- *)
val lift_thm      = bir_o0_motor_cm0_mod_lift_THM;
val prog_def      = bir_o0_motor_prog_def;
val birenvtyl_def = o0_motor_birenvtyl_def;

end
end (* struct *)
