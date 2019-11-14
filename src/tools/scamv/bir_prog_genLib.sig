signature bir_prog_genLib = sig

  (* ---------------------- *)
  (* general functions      *)
  (* ---------------------- *)
  val process_asm_code : string -> bir_inst_lifting_mem_region list
  val lift_program_from_sections : bir_inst_lifting_mem_region list -> term

  (* ---------------------- *)
  (* program slingers       *)
  (* ---------------------- *)

  val prog_gen_store_fromfile        : string      -> unit -> string * term
  val prog_gen_store_fromlines       : string list -> unit -> string * term

  val prog_gen_store_rand            : int         -> unit -> string * term
  val prog_gen_store_a_la_qc         : int         -> unit -> string * term
  val prog_gen_store_a_la_qc_previct1: int         -> unit -> string * term
  val prog_gen_store_a_la_qc_previct2: int         -> unit -> string * term

  val prog_gen_store_rand_slice      : int         -> unit -> string * term
  val prog_gen_store_prefetch_stride : int         -> unit -> string * term

end
