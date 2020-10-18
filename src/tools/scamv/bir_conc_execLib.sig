signature bir_conc_execLib = sig
  include bir_embexp_driverLib;

  val conc_exec_program :  int -> term -> (term -> term) option -> (num * num) list * term -> term
  
  val conc_exec_obs_extract : int -> term -> (num * num) list * term -> (int * term) list

  val conc_exec_obs_compute : int -> term -> machineState -> (int * term) list * machineState
  val conc_exec_obs_compare : int -> term -> machineState * machineState -> bool * machineState list
end
