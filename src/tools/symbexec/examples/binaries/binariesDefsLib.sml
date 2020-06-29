structure binariesDefsLib =
struct

open binariesBalrobDefsLib;

val symb_filter_mem = fn secname =>
  case secname of
      ".text" => (K true)
    | ".data" => (K true)
    | ".bss"  => (K true)
    | _       => (K false);
val data_filter_mem = fn secname => fn _ => secname = ".data" orelse secname = ".bss";

val (prog_id, (da_file_lift, da_file_mem, mem_file), thm_name, (mem_region_const, mem_region_data, mem_region_stack)) = List.nth(configs,0);

end (* struct *)
