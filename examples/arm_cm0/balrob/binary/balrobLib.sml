structure balrobLib =
struct

local

open HolKernel Parse boolLib bossLib;

(*open bir_symbLib;*)

open balrobTheory;

in

(* ------------------------------------- *)
(* relevant theorems and definitions     *)
(* ------------------------------------- *)
val bir_lift_thm = bir_balrob_cm0_mod_lift_THM;
val bir_balrob_prog_def = bir_balrob_prog_def;
val balrob_birenvtyl_def = balrob_birenvtyl_def;

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

val birs_prog_config = ((fst o dest_eq o concl) bir_balrob_prog_def, balrob_birenvtyl_def);

end
end (* struct *)
