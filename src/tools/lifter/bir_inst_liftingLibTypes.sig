(* Type definitions used by bir_inst_liftingLib. For technical reasons
   they need to be in a separate file. *)

signature bir_inst_liftingLibTypes = sig

  (* Errors are reported via the exception bir_inst_liftingExn (hex_code, reason)
     which indicates that lifting of the given hex-code failed for the given reason. *)
  datatype bir_inst_liftingExn_data =
     BILED_msg of string
   | BILED_msg_term of string * Abbrev.term
   | BILED_lifting_failed of Abbrev.term

  exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;

  (* For debugging a printer *)
  val bir_inst_liftingExn_data_to_string : bir_inst_liftingExn_data -> string;


  (* We need to encode where instructions and data are stored in memory. This is
     done via bir_inst_lifting_mem_regions. They consist of a start address followed
     by a list of annotated hex-codes. The annotation states, wether the entry is code, data
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

end;
