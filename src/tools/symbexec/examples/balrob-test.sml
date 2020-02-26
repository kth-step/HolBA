open HolKernel Parse

open binariesTheory;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

(* get program behavior *)
val (_, mem_wi_prog_tm, mem_tm, prog_tm) = (dest_bir_is_lifted_prog o concl) balrob_program_THM;

(* get memory contents (including data) *)
val da_file     = "binaries/balrob.elf.da.plus";
val symb_filter = fn secname =>
  case secname of
      ".text" => (K true)
    | ".data" => (K true)
    | ".bss"  => (K true)
    | _       => (K false);
val data_filter = fn secname => fn _ => secname = ".data" orelse secname = ".bss";

val da_data = read_disassembly_file symb_filter da_file;
val _ = print_disassembly_data da_data;


