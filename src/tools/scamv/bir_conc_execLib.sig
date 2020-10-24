signature bir_conc_execLib = sig
  include Abbrev;

  val conc_exec_program :  int -> term -> (term -> term) option -> (Arbnum.num * Arbnum.num) list * term -> term
  
  val conc_exec_obs_extract : int -> term -> (Arbnum.num * Arbnum.num) list * term -> (int * term) list

  val conc_exec_obs_compute : int -> term -> bir_embexp_driverLib.machineState -> (int * term) list * bir_embexp_driverLib.machineState
  val conc_exec_obs_compare : int -> term -> bir_embexp_driverLib.machineState * bir_embexp_driverLib.machineState -> bool * bir_embexp_driverLib.machineState list
end
