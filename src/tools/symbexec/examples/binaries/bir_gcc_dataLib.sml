structure bir_gcc_dataLib =
struct
local

  open gcc_supportLib;

  fun find_single_SOME []             = NONE
    | find_single_SOME ( NONE   ::xs) = find_single_SOME xs
    | find_single_SOME ((SOME x)::xs) =
	case find_single_SOME xs of
	    NONE   => SOME x
	  | SOME _ => raise ERR "find_single_SOME" "search criterion matched multiple times";

in (* local *)

  fun mem_find_in_lbl mem_find_in_block_f   item (l:disassembly_lbl) =
    find_single_SOME (List.map (mem_find_in_block_f item) (#DAL_blocks l));

  fun mem_find_in_section mem_find_in_lbl_f item (s:disassembly_section) =
    find_single_SOME (List.map (mem_find_in_lbl_f item) (#DAS_lbls   s));

  fun mem_find_in_data    mem_find_in_lbl_f item (d:disassembly_data) =
    find_single_SOME (List.map (mem_find_in_section mem_find_in_lbl_f item) d);

  fun mem_find_in_data_at_block mem_find_in_block_f item (d:disassembly_data) =
      mem_find_in_data (mem_find_in_lbl mem_find_in_block_f) item d;

  fun mem_find_in_data_at_lbl mem_find_in_lbl_f item (d:disassembly_data) =
      mem_find_in_data mem_find_in_lbl_f item d;


  fun is_addr_in_entry addr (e: disassembly_entry) =
    (Arbnumcore.<= (#DAE_addr e, addr)) andalso
    (Arbnumcore.< (addr, Arbnumcore.+ (#DAE_addr e, Arbnumcore.fromInt ((length (explode (#DAE_hex e))) div 2))));

  fun mem_read_byte_from_block addr (b: disassembly_block) =
    let
      val entries = List.filter (is_addr_in_entry addr) b;
      val bytes   = List.map (fn e =>
	    let
	      val offset  = Arbnumcore.-(addr, #DAE_addr e);
	      val hex_idx = (Arbnumcore.toInt offset) * 2;
	      val cl      = explode (#DAE_hex e);
	      val hex     = implode (List.take (List.drop (cl, hex_idx), 2));
	    in
	      Arbnumcore.toInt (Arbnumcore.fromHexString hex)
	    end
	  ) entries;
      val bytes_ol = List.map SOME bytes;
    in
      find_single_SOME bytes_ol
    end;


  fun mem_find_symbol_addr_lbl name (l:disassembly_lbl) =
    let val lbl_name = #DAL_name l in
    if name = lbl_name then
      SOME (#DAL_addr l)
    else
      NONE
    end;


  fun mem_find_symbol_by_addr_block addr name (b: disassembly_block) =
    let
      val entries = List.filter (is_addr_in_entry addr) b;
    in
      find_single_SOME (List.map (K (SOME name)) entries)
    end;

  fun mem_find_symbol_by_addr_lbl addr (l:disassembly_lbl) =
    find_single_SOME (List.map (mem_find_symbol_by_addr_block addr (#DAL_name l)) (#DAL_blocks l));

end (* local *)
end (* struct *)
