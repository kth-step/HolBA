signature bir_prog_genLib = sig

  (* ---------------------- *)
  (* general functions      *)
  (* ---------------------- *)
  val lift_prog_preproc :
   (error_record -> bir_inst_lifting_mem_region list option) ->
     string list -> (int * string * bir_inst_lifting_mem_region list) option
  val lift_prog_lift :
   (unit -> 'a * term * int) ->
     int * 'a * bir_inst_lifting_mem_region list -> 'a * term * int
  val add_halt_to_prog : int -> term -> term

  val process_asm_code : string -> bir_inst_lifting_mem_region list
  val lift_program_from_sections : bir_inst_lifting_mem_region list -> term

  (* ---------------------- *)
  (* program slingers       *)
  (* ---------------------- *)

  val prog_gen_store_fromfile        : string      -> unit -> string * term
  val prog_gen_store_fromlines       : string list -> unit -> string * term
  val prog_gen_store_listfile        : string      -> unit -> string * term

  val prog_gen_store_rand            : string->int -> unit -> string * term
  val prog_gen_store_a_la_qc         : string->int -> unit -> string * term

  val prog_gen_store_rand_slice      : int         -> unit -> string * term
  val prog_gen_store_prefetch_stride : int         -> unit -> string * term

end
