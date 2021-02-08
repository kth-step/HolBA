signature bir_inst_liftingLibTypes = sig

(* Type definitions used by bir_inst_liftingLib. For technical reasons
   they need to be in a separate file. *)

  (******************)
  (* Error messages *)
  (******************)

  (* Errors are reported via the exception bir_inst_liftingExn (hex_code, reason)
     which indicates that lifting of the given hex-code failed for the given reason. *)
  datatype bir_inst_liftingExn_data =
     BILED_msg of string
   | BILED_msg_term of string * Abbrev.term
   | BILED_lifting_failed of Abbrev.term

  exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;

  (* For debugging a printer *)
  val bir_inst_liftingExn_data_to_string : bir_inst_liftingExn_data -> string;

  (* The error report for a single instruction.
     (pc, hexcode machine readable, hexcode with human readable annotations, error reported if available) *)
  type bir_inst_error = Arbnum.num * string * string * bir_inst_liftingExn_data option;

  val bir_inst_error_to_string : bir_inst_error -> string
  val print_bir_inst_error : bir_inst_error -> unit;
  val print_bir_inst_errors : bir_inst_error list -> unit;


  (******************)
  (* Memory regions *)
  (******************)

  (* We need to encode where instructions and data are stored in memory. This is
     done via bir_inst_lifting_mem_regions. They consist of a start address followed
     by a list of annotated hex-codes. The annotation states, whether the entry is code, data
     or unknown. For code, also it's mnemonic might be provided. *)

  datatype bir_inst_lifting_mem_entry_type =
      BILME_code of string option
    | BILME_data
    | BILME_unknown

  datatype bir_inst_lifting_mem_region =
    BILMR of Arbnum.num * (string * bir_inst_lifting_mem_entry_type) list;


  (* Some convenience functions for creating regions containing data, code or unknown
     content for an intial address and a list of hex-codes. *)
  val mk_bir_inst_lifting_code_region : Arbnum.num -> string list -> bir_inst_lifting_mem_region
  val mk_bir_inst_lifting_data_region : Arbnum.num -> string list -> bir_inst_lifting_mem_region
  val mk_bir_inst_lifting_region      : Arbnum.num -> string list -> bir_inst_lifting_mem_region


  (* pretty printing *)
  val bir_inst_lifting_mem_region_to_string : bir_inst_lifting_mem_region -> string;
  val print_bir_inst_lifting_mem_regions : bir_inst_lifting_mem_region list -> unit;

  (* We can expand memory regions by computing the absolute address for each entry. For
     this we need a function that computes the number of memory addresses occupied by
     a hex-code. Since memory is usually addressed bytewise, this is usually the half the
     length of the hexcode. *)
  val expand_bir_inst_lifting_mem_region : (string -> Arbnum.num) ->
     bir_inst_lifting_mem_region -> (Arbnum.num * string * bir_inst_lifting_mem_entry_type) list

  val expand_bir_inst_lifting_mem_regions : (string -> Arbnum.num) ->
     bir_inst_lifting_mem_region list -> (Arbnum.num * string * bir_inst_lifting_mem_entry_type) list

  (* Pretty printing for these expanded memory regions *)
  val expanded_bir_inst_lifting_mem_regions_to_string :
     (Arbnum.num * string * bir_inst_lifting_mem_entry_type) list -> string

  val print_expanded_bir_inst_lifting_mem_regions :
     (Arbnum.num * string * bir_inst_lifting_mem_entry_type) list -> unit

  (* Sanity check, compute min, max

     The lifter expects the addresses of memory regions to be strictly increasing.
     Moreover, they should all live in a a protected memory range. The function
     "check_expanded_bir_inst_lifting_mem_regions" checks whether the addresses are
     non-empty and strictly increasing. If this is the case, the minimal and maximal
     address is returned. Otherwise, NONE is returned.
  *)
  val check_expanded_bir_inst_lifting_mem_regions :  (Arbnum.num * string * bir_inst_lifting_mem_entry_type) list -> (Arbnum.num * Arbnum.num) option

end;
