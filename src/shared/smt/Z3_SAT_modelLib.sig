signature Z3_SAT_modelLib =
sig

  type model = (string * Term.term) list;

  val is_configured: unit -> bool

  val Z3_GET_SAT_MODEL: Term.term -> model

end (* Z3_SAT_modelLib *)
