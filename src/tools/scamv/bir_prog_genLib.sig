signature bir_prog_genLib = sig

  (* ---------------------- *)
  (* general                *)
  (* ---------------------- *)

  val bir_prog_gen_asm_lines_to_code : string list -> string



  (* ---------------------- *)
  (* mockups for debugging  *)
  (* ---------------------- *)

  (* sets a sequence of test programs.
  *)
  val bir_prog_gen_arm8_mock_set : string list list -> unit

  (* sets whether the produced sequence wraps around.
  *)
  val bir_prog_gen_arm8_mock_set_wrap_around : bool -> unit

  (* generates a fixed sequence of pre-defined test programs.
  *)
  val bir_prog_gen_arm8_mock : unit -> string list



  (* ------------------- *)
  (* heading             *)
  (* ------------------- *)

  (* description of the function.
  *)
  val bir_prog_gen_arm8 : int -> string list

end
