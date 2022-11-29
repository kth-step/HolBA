structure binariesDefsLib =
struct

open binariesBalrobDefsLib;

val symb_filter_mem = fn secname =>
  case secname of
      ".text" => (Lib.K true)
    | ".data" => (Lib.K true)
    | ".bss"  => (Lib.K true)
    | _       => (Lib.K false);
val data_filter_mem = fn secname => fn _ => secname = ".data" orelse secname = ".bss";

val (prog_id, (da_file_lift, da_file_mem, mem_file), thm_name, (mem_region_const, mem_region_data, mem_region_stack)) = List.nth(configs,0);
val (mem_region_const, mem_region_data, mem_region_stack) =
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x10001c54),
                            (Arbnum.fromInt 0x10001c54, Arbnum.fromInt (0x0000001c + 0x338 - 0x80 - 0x10)),
                            (Arbnum.fromInt (0x10001ff0 - 0x48 - 0x80 - 0x10), Arbnum.fromInt (0x00000010 + 0x48 + 0x80 + 0x10)))
;


end (* struct *)
