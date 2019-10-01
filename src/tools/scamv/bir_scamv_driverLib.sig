signature bir_scamv_driverLib = sig
    include scamv_configLib

  val scamv_test_main : int -> (string * term) -> unit

  val scamv_test_mock : unit -> (bool option * string)
  val scamv_test_single_file : string -> unit;

  val scamv_run : scamv_config -> unit
  val scamv_run_with_opts : unit -> unit

end
