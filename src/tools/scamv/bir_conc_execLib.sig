signature bir_conc_execLib = sig
  include Abbrev;

(*
  val conc_exec_program :  int -> term -> (term -> term) option -> (Arbnum.num * Arbnum.num) list * term -> term

  val conc_exec_obs_extract : int -> term -> (Arbnum.num * Arbnum.num) list * term -> (int * term) list
*)

  val conc_exec_obs_compute : int -> term -> experimentsLib.machineState -> (int * term) list * experimentsLib.machineState
  val conc_exec_obs_compare : int -> term -> experimentsLib.machineState * experimentsLib.machineState -> bool * experimentsLib.machineState list
end
