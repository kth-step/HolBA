structure bir_subprogramLib =
struct

  local
    open bir_programSyntax;
    open bir_immSyntax;
    open wordsSyntax;

  in
 
    val ERR = mk_HOL_ERR "bir_subprogramLib"

    (* TODO: Copied from bslSyntax (not in bslSyntax.sig). This should
     * really be placed in bir_programlabelsSyntax.  *)
    local
      open bir_program_labelsTheory
      fun syntax_fns n d m =
	HolKernel.syntax_fns {n = n, dest = d, make = m}
			     "bir_program_labels"
      val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop
				     HolKernel.mk_binop
    in
      val (BL_Address_HC_tm, mk_BL_Address_HC, dest_BL_Address_HC,
	     is_BL_Address_HC) = syntax_fns2 "BL_Address_HC"
    end

    (* DESCRIPTION: Function extracting subrograms from BirProgram
     * terms.
     * 
     * USAGE: Look at the .elf.da file. Observe the memory
     * addresses in the leftmost column. Pick out the first
     * address in the function you want to analyse, and then the
     * last address.
     *
     * EXAMPLE: 
     * Get a term containing a lifted program:
    
       val (_, bir_prog) =
         dest_comb
           (concl examplesBinaryTheory.examples_arm8_program_THM);
     
     * This should extract the SQRT function
     * (adjust addresses as needed):

       val sqrt_prog_tm =
         extract_subprogram bir_prog 0x400250 0x400294;

     *
     * *)
    local
      fun address_of_block h =
	let
	  val (label, _, _) = dest_bir_block h
	  val (curr_address, _) = dest_BL_Address_HC label
	  val (_, word) = gen_dest_Imm curr_address
	in
	  uint_of_word word
	end

      fun find_subprogram_end []     _  _ = NONE
	| find_subprogram_end (h::t) a2 sprog_block =
	  let
	    val curr_address = address_of_block h
	  in
	    if curr_address = a2
	    then SOME (sprog_block@[h])
	    else find_subprogram_end t a2 (sprog_block@[h])
	  end

      fun find_subprogram_start []     _  _  = NONE
	| find_subprogram_start (h::t) a1 a2 =
	  let
	    val curr_address = address_of_block h
	  in
	    if curr_address = a1
	    then find_subprogram_end t a2 [h]
	    else find_subprogram_start t a1 a2
	  end

    in
      fun extract_subprogram prog a1 a2 =
        let
          val (obs_ty, prog_list_tm) = dest_BirProgram_list prog
	  val subprog_tm_opt =
            find_subprogram_start prog_list_tm a1 a2
        in
          mk_BirProgram_list (obs_ty, valOf subprog_tm_opt)
        end handle Option => raise ERR "extract_subprogram"
              ("The provided addresses "^
               "0x"^(Int.fmt StringCvt.HEX a1)^
               "0x"^(Int.fmt StringCvt.HEX a2)^
               "do not match any subprogram. Please double-check "^
               "these addresses with the .elf.da file of the "^
               "lifted program.");
    end;

  end

end
