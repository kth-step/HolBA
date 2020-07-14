signature bir_conc_execLib = sig

  val conc_exec_program : int -> term -> (term -> term) option -> term

  val conc_exec_obs_extract : term -> term list

  val conc_exec_obs_compute : term -> (string * num) list -> term list
  val conc_exec_obs_compare : term -> (string * num) list * (string * num) list -> bool

end
