signature bir_prog_slingLib = sig

  (* ---------------------- *)
  (* program slingers       *)
  (* ---------------------- *)

  val prog_gen_store_mock : unit -> string * term
  val prog_gen_store_rand : int -> unit -> string * term


end
