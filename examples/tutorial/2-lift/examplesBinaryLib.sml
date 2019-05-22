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

  end

end
