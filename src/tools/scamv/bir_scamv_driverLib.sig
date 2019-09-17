signature bir_scamv_driverLib = sig

  val scamv_test_main : string -> unit

  val scamv_test_mock : unit -> (bool option * string)

  val scamv_test_asmf : string -> (bool option * string)

end
