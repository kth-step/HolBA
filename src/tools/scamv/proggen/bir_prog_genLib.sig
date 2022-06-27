signature bir_prog_genLib = sig

  include Abbrev;

  (* ---------------------- *)
  (* general functions      *)
  (* ---------------------- *)
  val lift_prog_preproc :
    (HolKernel.error_record ->
     bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list option) ->
    experimentsLib.experiment_prog ->
    (int * experimentsLib.experiment_prog * bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list) option
  val lift_prog_lift :
   (unit -> 'a * term * int) ->
   int * 'a * bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list ->
   'a * term * int
  val add_halt_to_prog : int -> term -> (term * Arbnum.num)

  val process_asm_code : string -> bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list
  val lift_program_from_sections : bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list -> term

  (* ---------------------- *)
  (* program slingers       *)
  (* ---------------------- *)

  val prog_gen_store_fromfile        : string      -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list
  val prog_gen_store_fromlines       : string list -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list
  val prog_gen_store_list            : string      -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

  val prog_gen_store_rand            : string->int -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list
  val prog_gen_store_a_la_qc         : string->int -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

  val prog_gen_store_rand_slice      : int         -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list
  val prog_gen_store_prefetch_stride : int         -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

  val prog_gen_store_frombinary      : string      -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

end
