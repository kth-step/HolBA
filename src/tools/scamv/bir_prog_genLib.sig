signature bir_prog_genLib = sig

  (* ---------------------- *)
  (* mockups for debugging  *)
  (* ---------------------- *)

  (* sets a sequence of test programs.
  *)
  val bir_prog_gen_arm8_mock_set : (string list) list -> unit

  (* propagate with sequence of test programs (input: asm filenames).
  *)
  val bir_prog_gen_arm8_mock_propagate : string list -> unit

  (* sets whether the produced sequence wraps around.
  *)
  val bir_prog_gen_arm8_mock_set_wrap_around : bool -> unit


  (* ---------------------- *)
  (* program slingers       *)
  (* ---------------------- *)

  val prog_gen_store_mock : unit -> string * term
  val prog_gen_store_fromfile : string -> unit -> string * term
  val prog_gen_store_rand : int -> unit -> string * term

end
