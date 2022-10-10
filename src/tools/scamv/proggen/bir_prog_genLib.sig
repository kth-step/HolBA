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
  val add_halt_to_prog : int -> term -> (term * Arbnum.num * Arbnum.num)

  val process_asm_code : string -> bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list
  val lift_program_from_sections : bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list -> term

  val process_binary : string -> (string * string * Arbnum.num) list * bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list
  val define_entry_and_exits : bir_inst_liftingLibTypes.bir_inst_lifting_mem_region -> Arbnum.num * Arbnum.num list
  val get_section_by_name : string -> (string * string * Arbnum.num) list * bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list -> bir_inst_liftingLibTypes.bir_inst_lifting_mem_region option

  (* ---------------------- *)
  (* list of programs resulting from the LLVM phase *)
  (* for each program: 
      - function name
      - function description (slicing)
      - path filename of LLVM bitcode
      - path filename of binary *)
  val current_llvm_progs : ((string * string * string) * string) list option ref
  val current_llvm_prog : ((string * string * string) * string) option ref

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

  val prog_gen_store_frombinary      : string->(string * string * string) option       -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

  val prog_gen_store_fromllvm        : string      -> unit -> embexp_logsLib.prog_handle * term * string * (Arbnum.num * Arbnum.num list) list

end
