structure examplesBinaryLib =
struct

  local
    open bir_subprogramLib;
    open examplesBinaryTheory;
  in

    (* The entire example program, as a term *)
    val (_, bir_prog_tm) =
      dest_comb
	(concl examplesBinaryTheory.examples_arm8_program_THM);

    (* The greatest common divisor function *)
    val gcd_prog_tm =
      extract_subprogram bir_prog_tm 0x7dc 0x850;

    (* The square root function *)
    val sqrt_prog_tm =
      extract_subprogram bir_prog_tm 0x854 0x89c;

    (* The modular exponentiation function *)
    val modexp_prog_tm =
      extract_subprogram bir_prog_tm 0x8e8 0x9ac;

    (* The buggy binary search function *)
    val binsearch_bad_prog_tm =
      extract_subprogram bir_prog_tm 0x9b0 0xa5c;

    (* The hopefully non-buggy binary search function *)
    val binsearch_ok_prog_tm =
      extract_subprogram bir_prog_tm 0xb20 0xbdc;

  end

end
