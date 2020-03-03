structure binariesDefsLib =
struct

open binariesBalrobDefsLib;

val da_file_mem     = "balrob/balrob.elf.da.plus";
val symb_filter_mem = fn secname =>
  case secname of
      ".text" => (K true)
    | ".data" => (K true)
    | ".bss"  => (K true)
    | _       => (K false);
val data_filter_mem = fn secname => fn _ => secname = ".data" orelse secname = ".bss";


val mem_file     = "balrob/balrob.elf.mem";


end (* struct *)
