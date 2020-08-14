signature bir_conc_execLib = sig

  datatype modelValues = memT of (string * (num*num) list)
		       | regT of (string * num)
  val conc_exec_program :  int -> term -> (term -> term) option -> (num * num) list * term -> term
  
  val conc_exec_obs_extract : int -> term -> (num * num) list * term -> (int * term) list

  val conc_exec_obs_compute : int -> term -> modelValues list -> (int * term) list * modelValues list
  val conc_exec_obs_compare : int -> term -> modelValues list * modelValues list -> bool * modelValues list list
end
