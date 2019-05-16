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
      extract_subprogram bir_prog_tm 0x4001d8 0x40024c;

    (* The square root function *)
    val sqrt_prog_tm =
      extract_subprogram bir_prog_tm 0x400250 0x400294;

    (* The modular exponentiation function *)
    val modexp_prog_tm =
      extract_subprogram bir_prog_tm 0x400298 0x40035c;

    (* The buggy binary search function *)
    val binsearch_bad_prog_tm =
      extract_subprogram bir_prog_tm 0x400360 0x40040c;

    (* The hopefully non-buggy binary search function *)
    val binsearch_ok_prog_tm =
      extract_subprogram bir_prog_tm 0x4004d0 0x40058c;

  end

end
