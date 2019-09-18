signature bir_embexp_driverLib = sig

  val bir_embexp_create : (string * (string * string)) -> string -> (((string * num) list) * ((string * num) list)) -> string
  val bir_embexp_run : string -> bool -> (bool option * string)

end
