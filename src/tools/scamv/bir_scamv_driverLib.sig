signature bir_scamv_driverLib = sig

  type scamv_config = { max_iter : int, prog_size : int, max_tests : int }

  val scamv_test_main : int -> (string * term) -> unit

  val scamv_test_mock : unit -> (bool option * string)

  val scamv_run : scamv_config -> unit

end
