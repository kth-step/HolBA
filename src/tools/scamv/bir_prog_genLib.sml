structure bir_prog_genLib :> bir_prog_genLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open arm8_progLib arm8AssemblerLib arm8;


(* general *)
(* ========================================================================================= *)
  fun bir_prog_gen_asm_lines_to_code asm_lines =
    List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "" asm_lines;


(* fixed programs for mockup *)
(* ========================================================================================= *)
  val mock_progs_i = ref 0;
  val mock_progs = ref [["ldr x2, [x1]"]];
  val wrap_around = ref false;

  fun bir_prog_gen_arm8_mock_set progs =
    let
      val _ = mock_progs_i := 0;
      val _ = mock_progs := progs;
    in
      ()
    end;

  fun bir_prog_gen_arm8_mock_set_wrap_around b =
    let
      val _ = wrap_around := b;
      val _ = if not (!wrap_around) then ()
	      else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
    in
      ()
    end;

  fun bir_prog_gen_arm8_mock () =
    let
      val _ = if !mock_progs_i < length (!mock_progs) then ()
	      else raise ERR "bir_prog_gen_arm8_mock" "no more programs";

      val prog = List.nth(!mock_progs, !mock_progs_i);

      val _ = mock_progs_i := (!mock_progs_i) + 1;
      val _ = if not (!wrap_around) then ()
	      else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
    in
      prog
    end;


(* randomly generated programs *)
(* ========================================================================================= *)
 val arm8_names_weighted = [(0,"Address"),
  (1,"AddSubShiftedRegister32-1"),      (1,"AddSubShiftedRegister32-2"),     (1,"AddSubShiftedRegister32-3"),
  (1,"AddSubShiftedRegister32-4"),      (1,"AddSubShiftedRegister64-1"),     (1,"AddSubShiftedRegister64-2"),
  (1,"AddSubShiftedRegister64-3"),      (1,"AddSubShiftedRegister64-4"),     (1,"AddSubExtendRegister-1"),
  (0,"AddSubExtendRegister-2"),         (1,"AddSubExtendRegister-3"),        (0,"AddSubExtendRegister-4"),
  (1,"AddSubExtendRegister-5"),         (0,"AddSubExtendRegister-6"),        (1,"AddSubExtendRegister-7"),
  (0,"AddSubExtendRegister-8"),         (1,"AddSubImmediate-1"),             (1,"AddSubImmediate-2"),
  (1,"AddSubImmediate-3"),              (1,"AddSubImmediate-4"),             (1,"AddSubImmediate-5"),
  (1,"AddSubImmediate-6"),              (1,"AddSubImmediate-7"),             (1,"AddSubImmediate-8"),
  (1,"AddSubCarry-1"),                  (1,"AddSubCarry-2"),                 (1,"AddSubCarry-3"),
  (1,"AddSubCarry-4"),                  (1,"LogicalShiftedRegister32-1"),    (1,"LogicalShiftedRegister32-2"),
  (1,"LogicalShiftedRegister32-3"),     (1,"LogicalShiftedRegister32-4"),    (1,"LogicalShiftedRegister64-1"),
  (1,"LogicalShiftedRegister64-2"),     (1,"LogicalShiftedRegister64-3"),    (1,"LogicalShiftedRegister64-4"),
  (1,"LogicalImmediate32-1"),           (1,"LogicalImmediate32-2"),          (1,"LogicalImmediate32-3"),
  (1,"LogicalImmediate32-4"),           (1,"LogicalImmediate64-1"),          (1,"LogicalImmediate64-2"),
  (1,"LogicalImmediate64-3"),           (1,"LogicalImmediate64-4"),          (1,"Shift-1"),
  (1,"Shift-2"),                        (1,"MoveWide32"),                    (1,"MoveWide64"),
  (1,"BitfieldMove32"),                 (1,"BitfieldMove64"),                (0,"ConditionalCompareImmediate-1"),
  (1,"ConditionalCompareImmediate-2"),  (1,"ConditionalCompareImmediate-3"), (1,"ConditionalCompareImmediate-4"),
  (1,"ConditionalCompareRegister-1"),   (14,"ConditionalCompareRegister-2"), (14,"ConditionalCompareRegister-3"),
  (1,"ConditionalCompareRegister-4"),   (1,"ConditionalSelect-1"),           (14,"ConditionalSelect-2"),
  (1,"CountLeading-1"),                 (1,"CountLeading-2"),                (1,"ExtractRegister32"),
  (1,"ExtractRegister64"),              (1,"Division-1"),                    (1,"Division-2"),
  (1,"MultiplyAddSub-1"),               (1,"MultiplyAddSub-2"),              (1,"MultiplyAddSubLong"),
  (0,"MultiplyHigh"),                   (1,"Reverse32"),                     (1,"Reverse64"),
  (1,"CRC8"),                           (1,"CRC16"),                         (1,"CRC32"),
  (1,"CRC64"),                          (1,"BranchConditional"),             (1,"BranchImmediate-1"),
  (1,"BranchImmediate-2"),              (1,"BranchRegisterJMP"),             (1,"BranchRegisterCALL"),
  (1,"BranchRegisterRET"),              (1,"CompareAndBranch-1"),            (1,"CompareAndBranch-2"),
  (1,"TestBitAndBranch-1"),             (1,"TestBitAndBranch-2"),            (1,"TestBitAndBranch-3"),
  (1,"TestBitAndBranch-4"),             (1,"LoadStoreImmediate-1-1"),        (1,"LoadStoreImmediate-1-2"),
  (1,"LoadStoreImmediate-1-3"),         (1,"LoadStoreImmediate-1-4"),        (1,"LoadStoreImmediate-1-5"),
  (1,"LoadStoreImmediate-1-6"),         (1,"LoadStoreImmediate-1-7"),        (1,"LoadStoreImmediate-1-8"),
  (1,"LoadStoreImmediate-1-9"),         (1,"LoadStoreImmediate-1-10"),       (1,"LoadStoreImmediate-1-11"),
  (1,"LoadStoreImmediate-1-12"),        (1,"LoadStoreImmediate-1-13"),       (1,"LoadStoreImmediate-1-14"),
  (1,"LoadStoreImmediate-1-15"),        (1,"LoadStoreImmediate-1-16"),       (1,"LoadStoreImmediate-1-17"),
  (1,"LoadStoreImmediate-1-18"),        (1,"LoadStoreImmediate-1-19"),       (1,"LoadStoreImmediate-1-20"),
  (1,"LoadStoreImmediate-1-21"),        (1,"LoadStoreImmediate-1-22"),       (1,"LoadStoreImmediate-1-23"),
  (1,"LoadStoreImmediate-1-24"),        (1,"LoadStoreImmediate-1-25"),       (1,"LoadStoreImmediate-1-26"),
  (1,"LoadStoreImmediate-1-27"),        (1,"LoadStoreImmediate-1-28"),       (1,"LoadStoreImmediate-2-1"),
  (1,"LoadStoreImmediate-2-2"),         (1,"LoadStoreImmediate-2-3"),        (1,"LoadStoreImmediate-2-4"),
  (1,"LoadStoreImmediate-2-5"),         (1,"LoadStoreImmediate-2-6"),        (1,"LoadStoreImmediate-2-7"),
  (1,"LoadStoreImmediate-2-8"),         (1,"LoadStoreImmediate-2-9"),        (1,"LoadStoreImmediate-2-10"),
  (1,"LoadStoreImmediate-2-11"),        (1,"LoadStoreImmediate-2-12"),       (1,"LoadStoreImmediate-2-13"),
  (1,"LoadStoreImmediate-2-14"),        (1,"LoadStoreImmediate-2-15"),       (1,"LoadLiteral-1"),
  (1,"LoadLiteral-2"),                  (1,"LoadLiteral-3"),                 (1,"LoadLiteral-4"),
  (1,"LoadStoreRegister-1"),            (1,"LoadStoreRegister-2"),           (1,"LoadStoreRegister-3"),
  (1,"LoadStoreRegister-4"),            (1,"LoadStoreRegister-5"),           (1,"LoadStoreRegister-6"),
  (1,"LoadStoreRegister-7"),            (1,"LoadStoreRegister-8"),           (1,"LoadStoreRegister-9"),
  (1,"LoadStoreRegister-10"),           (1,"LoadStoreRegister-11"),          (1,"LoadStoreRegister-12"),
  (1,"LoadStoreRegister-13"),           (1,"LoadStoreRegister-14"),          (1,"StorePair32-1"),
  (1,"StorePair32-2"),                  (1,"LoadPair32-1"),                  (1,"LoadPair32-2"),
  (1,"LoadStorePair64-1"),              (1,"LoadStorePair64-2"),             (1,"LoadStorePair64-3"),
  (1,"LoadStorePair64-4"),              (1,"NoOperation")]
			   
 fun instClass subs =
     hd (String.tokens  (fn c => Char.compare (c,#"-") = EQUAL) subs);

(* ---------------------------------------------  *)
 type gen = Random.generator
 val rg = Random.newgenseed 1.0
 val emp_str = ""
     
 fun bits gen bits =
     map (fn x => x = 1) (Random.rangelist (0,2) (bits,gen))

 fun select l =
     let val ln = length l
     in
      fn gen => let val i = Random.range (0,ln) gen in (i,List.nth (l,i)) end
     end

 fun weighted_select l = select (List.concat (map (fn (n,x) => List.tabulate (n,fn _ => x)) l));
 fun flat xs = List.foldr (fn (x, acc) => x @ acc) [] xs;

 local
     val gen = Random.newgenseed 1.0
     fun random_bit () =
	 if Random.range (0, 2) gen = 1 then boolSyntax.T else boolSyntax.F
 in
 fun random_hex tm =
     let
         val l = Term.free_vars tm
         val s = List.map (fn v => v |-> random_bit ()) l
     in
         bitstringSyntax.hexstring_of_term (Term.subst s tm)
     end
 end

 val random = random_hex o Option.valOf o arm8_stepLib.arm8_pattern;

(*
val el = "6B831B94"
*)
 fun decomp el =  arm8AssemblerLib.arm8_disassemble [QUOTE el];

 fun inst_decomp inst =
     instructionToString
         (Decode((Option.valOf o BitsN.fromHexString) (inst ,32)))  

 fun member(x,[]) = false
   |  member(x,L) =
      if x=hd(L) then true
      else member(x,tl(L));

 fun intersect([],[]) = []
   | intersect(L1,[]) = []
   | intersect(L1,L2) = if member(hd(L2), L1) then hd(L2)::intersect(L1, tl(L2))
			else intersect(L1, tl(L2));

 fun remChars  (c,s) =
     let fun rem [] = []
           | rem (c'::cs) =
             if c = c'
             then rem cs
             else c'::rem cs
     in
	 implode (rem (explode s)) 
     end

 fun getReg args = 
     map (fn arg => foldl remChars arg [#",", #" ", #"]"]) args


 fun instGen () =
     let val ic = (snd(weighted_select arm8_names_weighted rg))
	 val ib = random ic
	 val wl = filter (fn c => String.isSubstring "WORD" c) (decomp ib)
     in
	 if null wl then (ic, ib) else instGen ()
     end 

 local 
     val gen = Random.newgenseed 1.0
     fun addr_to_hexString adr =
	 (BitsN.toHexString (BitsN.fromInt ((IntInf.fromInt adr), 32)))

     fun cmp_ast s =
	 case instructionFromString s of
	     OK ast => ast
           | _ => raise ERR "cmp_ast" "some progGen error"

     fun cmp_mcode ast = 
	 (case Encode ast of
              arm8.ARM8 w =>
              ("",
               Option.SOME(L3.padLeftString(#"0",(8,BitsN.toHexString w))))
            | BadCode err => ("Encode error: " ^ err,NONE));

 in
 fun branch_instGen (pc, base, len) =
     let val adr = base + (4*(Random.range (pc, len) gen))
	 val adr_str = String.concat["bl +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 fun c_branch_instGen (inst, pc, base, len) =
     let val adr = base + (4*(Random.range (pc, len) gen))
	 val adr_str = String.concat[hd((p_tokens(hd(decomp(inst)))))," +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 fun cmp_and_branch_instGen (inst, pc, base, len) =
     let val adr = base + (4*(Random.range (pc, len) gen))
	 val tks = (p_tokens(hd(decomp(inst))))
	 val rinst = String.concat[List.nth(tks,0), List.nth(tks,1),", +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast rinst)
     in
	 (emp_str, inst)
     end     
 end

 fun instsGen (pc, [], base, len)  =
     let val inst = snd (instGen ())
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
     in
	 (hd args, inst)
     end
     
   | instsGen (pc, src, base, len) =
     let val (c, inst) = instGen ()
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
	 val inclusion =  intersect (src, tl args)
     in
	 case (instClass c) of 
	     "BranchImmediate" =>  branch_instGen(pc, base, len)
	   | "BranchConditional" => c_branch_instGen (inst,pc, base, len)
	   | "CompareAndBranch" => cmp_and_branch_instGen (inst,pc, base, len)			   
	   | _ =>
	     if List.null inclusion
	     then instsGen (pc,src, base, len) 
	     else (hd args, inst)
     end

 (* ---------------------------------------------  *)
 fun progGen (n, base) =
     let val src = ref ([]:string list);
	 val pc = ref 0;
     in
	 (List.tabulate (n, fn _ => let val (d,i) = (instsGen (!pc,!src, base, n)) 			
				    in  (src:= (d::(!src)); pc:= !pc + 1);i end))
     end

  val do_debug = false;
  fun remove_plus s = concat (String.tokens (fn c => c = #"+") s);
  fun remove_minus s = concat (String.tokens (fn c => c = #"-") s);
  fun remove_junk s = (hd (String.tokens (fn c => c = #";")
                                        (remove_minus (remove_plus s)))) ^ (if not do_debug then ""
                                                                            else " /* orig: " ^ s ^ " */");

(*
val n = 3;
*)
 (* The function take number of instructions and the base address *)
 fun bir_prog_gen_arm8_rand_raw n = map (remove_junk o hd o decomp) (progGen (n, 0x40000));


local

  (* this was copied -----> *)
  open bir_inst_liftingLib;

  open gcc_supportLib;
  open bir_gccLib;

  open bir_programSyntax;
  open listSyntax;


  (* for arm8 *)
  val (bmil_bir_lift_prog_gen, disassemble_fun) = (bmil_arm8.bir_lift_prog_gen, arm8AssemblerLib.arm8_disassemble);


  fun process_asm_code asm_code =
      let
	  val da_file = bir_gcc_assembe_disassemble asm_code "./tempdir"

	  val (region_map, sections) = read_disassembly_file_regions da_file;
      in
	  (asm_code, sections)
      end

  fun disassembly_section_to_minmax section =
      case section of
	  BILMR(addr_start, entries) =>
	  let
	      val data_strs = List.map fst entries;
		    (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
	      val lengths_st = List.map String.size data_strs;
	      val _ = List.map (fn x => ()) lengths_st;
	      val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
	      val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
	  in
	      (addr_start, Arbnum.+(addr_start, length))
	  end;

  fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
					  ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
					   (if Arbnum.>(max_1, max_2) then max_1 else max_2))
				      ) (hd ls) (tl ls);

  fun da_sections_minmax sections = minmax_fromlist (List.map disassembly_section_to_minmax sections);

  fun lift_program_from_sections sections =
      let
	  val prog_range = da_sections_minmax sections;
	  val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;
	  val lifted_prog = (snd o dest_comb o concl) thm_prog;
	  val lifted_prog_typed =
	      inst [Type`:'observation_type` |-> Type`:bir_val_t`]
		   lifted_prog;
      in
	  lifted_prog_typed
      end

  fun print_asm_code asm_code = (
                print "---------------------------------\n";
                print "=================================\n";
                print asm_code;
                print "=================================\n";
                print "---------------------------------\n");

  (* <---- this was copied *)

  fun gen_until_liftable n =
    let
      val prog = bir_prog_gen_arm8_rand_raw n;
      val asm_code_ = bir_prog_gen_asm_lines_to_code prog;
      val compile_opt = SOME (process_asm_code asm_code_)
	     handle HOL_ERR x => (print_asm_code asm_code_; NONE);
    in
      case compile_opt of
	  NONE => gen_until_liftable n
	| SOME (asm_code, sections) => 
    let
      val lifted_prog = lift_program_from_sections sections;
      val blocks = (fst o dest_list o dest_BirProgram) lifted_prog;
      (* val labels = List.map (fn t => (snd o dest_eq o concl o EVAL) ``(^t).bb_label``) blocks; *)
      val lift_worked = (List.length blocks = n);
      val _ = if lift_worked then ()
	      else print_asm_code asm_code;
    in
      if lift_worked then prog else (gen_until_liftable n)
    end
    end;

in

  val bir_prog_gen_arm8_rand =
    if do_debug then
      bir_prog_gen_arm8_rand_raw
    else
      gen_until_liftable;

end (* local *)


end; (* struct *)


