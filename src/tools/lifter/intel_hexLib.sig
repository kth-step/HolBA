(* It is useful that the lifter can interact with compilers like GCC. For this
   an exchange format is needed that both the HOL libs and the compilers understand.
   For simplicity and because it is kind of human-readable, intel-hex is choosen.

   https://en.wikipedia.org/wiki/Intel_HEX
*)

signature intel_hexLib = sig

  (* An Intel HEX file consists of a list of
     records. Each line is an encoded record. There are the following
     5 types of records:
   *)

  datatype ihex_record_type =
      IHEX_data of Arbnum.num * Arbnum.num list
      (* Data Record: start addr (lower 16 bit) + list of bytes starting at the addr *)
    | IHEX_eof (* End of file, needs to be the last entry *)
    | IHEX_extended_linear_address of Arbnum.num
      (* add offset of given no * 16 to all following addresses *)
    | IHEX_extended_segment_address of Arbnum.num
      (* add offset of given no * 2^16 to all following addresses *)
    | IHEX_start_linear_address of Arbnum.num
      (* set EIP register on 80386 and newer *)
    | IHEX_start_segment_address of Arbnum.num
      (* set CS:IP registers on 80x86 *)

  (* We can translate between this datatype and the string representation.
     Notice that things like dealing with checksums is done transparently. *)
  val decode_ihex : string -> ihex_record_type
  val encode_ihex : ihex_record_type -> string

  (* Using these encoding / decoding functions it is easy to read and write
     lists of ihex-records from and to files. The extra flag of
     write_to_ihex_file adds an IHEX_eof entry at the end of the file, if
     set to true. *)
  val write_to_ihex_file  : string -> bool -> ihex_record_type list -> unit
  val read_from_ihex_file : string -> ihex_record_type list


  (* Semantically, the IHEX files encode which values are stored where in memory.
     We represent such memory as a list of "(start_addr, byte_list)" tuples.
     They mean that add "start_addr" and consecutive addresses in memory the given
     list of bytes is stored. Since there might be gaps, we need a list of such
     tuples.

     The following functions map lists of ihex-records to and from these semantics. *)

  val decode_ihex_list : ihex_record_type list -> (Arbnum.num * Arbnum.num list) list
  val encode_ihex_list : (Arbnum.num * Arbnum.num list) list -> ihex_record_type list


  (* However the lifter interface uses the l3 step theorem infrastructure and
     therefore does not use lists of bytes, but hex-strings to encode instructions.
     The following functions convert between the format described above and
     the one used by the lifter. Besides the start address and the actual content,
     the lifter uses also flags for each entry whether the content is data or code.
     We ignore this since it cannot be stored in HEX files.

     For encoding and decoding we assume a fixed size of instructions. This as well
     as the endianness is given to the following functions. (4, true) means that
     an instruction has 4 bytes and is encoded little-endian. (2, false) would mean
     2 bytes and big endian.
  *)

  val decode_ihex_list_hex :
     int * bool -> ihex_record_type list -> (Arbnum.num * string list) list

  val encode_ihex_list_hex :
     int * bool -> (Arbnum.num * string list) list -> ihex_record_type list

end
