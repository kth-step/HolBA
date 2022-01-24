structure birs_transferLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_transferLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  open birs_stepLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open birs_composeLib;
open birs_auxTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in



end (* local *)

end (* struct *)
