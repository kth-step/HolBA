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

     Then "read_disassembly_file filter file_name" can be used.
     "filter" is a predicate on section names supposed to specify the sections we are interested in.
     "file_name" is the file to parse. It returns a mapping of section names to their
     start addresses and a list of regions. This list of regions is properly annotated
     with respect to code and data entries and contains mnemonics. *)

  val read_disassembly_file : (string -> bool) -> string ->
    (string * Arbnum.num) list * bir_inst_lifting_mem_region list

end
