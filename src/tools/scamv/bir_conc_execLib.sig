signature bir_conc_execLib = sig

  val conc_exec_program : int -> term -> (term -> term) option -> term

  val conc_exec_obs_extract : term -> term list

  val conc_exec_obs_compute : term -> (string * term) list -> term list
  val conc_exec_obs_compare : term -> (string * term) list * (string * term) list -> bool

end
