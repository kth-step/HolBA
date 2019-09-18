signature bir_scamv_driverLib = sig

  type scamv_config = { max_iter : int, max_tests : int }

  val scamv_test_main : int
                        -> string * bir_inst_lifting_mem_region list
                        -> unit

  val scamv_test_mock : unit -> (bool option * string)

  val scamv_test_asmf : string -> (bool option * string)

  val scamv_run : scamv_config -> unit

end
