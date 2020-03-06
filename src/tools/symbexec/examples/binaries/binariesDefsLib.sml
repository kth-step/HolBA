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

val mem_region_const = (Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003564);
val mem_region_data  = (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d));
val mem_region_stack = (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0);


end (* struct *)
