(* Some code connecting with the GCC tools. *)
open bir_inst_liftingLibTypes;

signature gcc_supportLib = sig

  (* Parse objdump disassembly. This format contains

     - nice section names
     - hexcodes and their addresses
     - mnemonics for hexcodes
     - distinction between code and data

     Therefore it is nice for our purposes.
     A call like "aarch64-linux-gnu-objdump -d main.elf" can be used to produce such
     a disassembly file. It contains usually lots of sections. We might be interested
     in just one of them corresponding to some function we are interested in.

     The whole file can be parsed, processed and then in the form of mem regions handed over
     to the lifter functions.
  *)

  (***********************)
  (* Datatype definition *)
  (***********************)

  (* The entries are single data entries. They have an address, a hex-code and
     a description. *)
  type disassembly_entry = {
    DAE_addr : Arbnum.num,
    DAE_hex  : string,
    DAE_desc : string
  };

  (* A block is a list of entries with consecutive addresses. *)
  type disassembly_block = disassembly_entry list;

  (* Each lbl has a name, a start address and a list of blocks. *)
  type disassembly_lbl = {
    DAL_name   : string,
    DAL_addr   : Arbnum.num,
    DAL_blocks : disassembly_block list
  }

  (* Each section has a name and a list of label section entries *)
  type disassembly_section = {
    DAS_name : string,
    DAS_lbls : disassembly_lbl list
  }

  (* Data parsed from an disassembly file consists of a list of sections. *)
  type disassembly_data = disassembly_section list;


  (*******************)
  (* Pretty printing *)
  (*******************)

  (* We can pretty print disassembly data *)
  val disassembly_data_to_string : disassembly_data -> string;
  val print_disassembly_data : disassembly_data -> unit;


  (******************)
  (* Parsing a file *)
  (******************)

  (* Most importantly, we can read it from a file produced by e.g. objdump *)
  val read_disassembly_file : string (* filename *) -> disassembly_data


  (*******************)
  (* Processing data *)
  (*******************)

  (* getting list of sections, labels and their addresses *)
  val disassembly_data_to_labels : disassembly_data -> (string * string * Arbnum.num) list

  (* Often we are only interested in a small part of a disassembler file, like the code
     of a single C function. The function "disassembly_data_filter" allows to filter for
     lbls in sections. Given a predicate "filter_pred : string -> string -> bool" only
     disassembly labels are kept in sections for which "filter_pred sec_name lbl_name" holds. *)
  val disassembly_data_filter : (string -> string -> bool) -> disassembly_data -> disassembly_data


  (* We also might want to relocate sections. Given a function "section-name -> offset",
     the specified offset is added to all addresses of the section. The offset can be negative.
     This is a very poor mans version of a proper relocator. *)
  val disassembly_data_relocate : (string -> Arbint.int) -> disassembly_data -> disassembly_data

  (* Finally we can convert the possibly processed disassembly data to memory regions
     that are processed by the lifter. *)
  val disassembly_data_to_mem_regions : disassembly_data ->
     bir_inst_liftingLibTypes.bir_inst_lifting_mem_region list


  (*************)
  (* Shortcuts *)
  (*************)

  (* Some combinations of above functions are useful shortcuts *)

  (* Parse file, filter sections and regions and convert to label list and mem regions *)
  val read_disassembly_file_regions_filter :
    (string -> string -> bool) -> string ->
    (string * string * num) list * bir_inst_lifting_mem_region list

  (* Parse file and convert to label list and mem regions *)
  val read_disassembly_file_regions :
    string -> (string * string * num) list * bir_inst_lifting_mem_region list

end
