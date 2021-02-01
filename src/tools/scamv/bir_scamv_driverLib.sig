signature bir_scamv_driverLib = sig
    include Abbrev;

    (* include bir_rel_synthLib *)
  val make_word_relation : term -> bool -> term
  val scamv_test_main : int -> (embexp_logsLib.prog_handle * term) -> unit

  val scamv_test_single_file : string -> unit;

  val scamv_run : scamv_configLib.scamv_config -> unit
  val scamv_run_with_opts : unit -> unit
			       
end
