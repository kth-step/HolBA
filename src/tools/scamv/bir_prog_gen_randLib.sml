structure bir_prog_gen_randLib :> bir_prog_gen_randLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open arm8_progLib arm8AssemblerLib arm8;

  open bir_scamv_helpersLib regExLib;


(* library for randomly generated programs *)
(* ========================================================================================= *)

 val arm8_names_weighted = [(0,"Address"),
  (10,"AddSubShiftedRegister32-1"),      (10,"AddSubShiftedRegister32-2"),     (10,"AddSubShiftedRegister32-3"),
  (10,"AddSubShiftedRegister32-4"),      (10,"AddSubShiftedRegister64-1"),     (10,"AddSubShiftedRegister64-2"),
  (10,"AddSubShiftedRegister64-3"),      (10,"AddSubShiftedRegister64-4"),     (10,"AddSubExtendRegister-1"),
  (0,"AddSubExtendRegister-2"),          (10,"AddSubExtendRegister-3"),        (0,"AddSubExtendRegister-4"),
  (10,"AddSubExtendRegister-5"),         (0,"AddSubExtendRegister-6"),         (10,"AddSubExtendRegister-7"),
  (0,"AddSubExtendRegister-8"),          (10,"AddSubImmediate-1"),             (10,"AddSubImmediate-2"),
  (10,"AddSubImmediate-3"),              (10,"AddSubImmediate-4"),             (10,"AddSubImmediate-5"),
  (10,"AddSubImmediate-6"),              (10,"AddSubImmediate-7"),             (10,"AddSubImmediate-8"),
  (10,"AddSubCarry-1"),                  (10,"AddSubCarry-2"),                 (10,"AddSubCarry-3"),
  (10,"AddSubCarry-4"),                  (10,"LogicalShiftedRegister32-1"),    (10,"LogicalShiftedRegister32-2"),
  (10,"LogicalShiftedRegister32-3"),     (10,"LogicalShiftedRegister32-4"),    (10,"LogicalShiftedRegister64-1"),
  (10,"LogicalShiftedRegister64-2"),     (10,"LogicalShiftedRegister64-3"),    (10,"LogicalShiftedRegister64-4"),
  (10,"LogicalImmediate32-1"),           (10,"LogicalImmediate32-2"),          (10,"LogicalImmediate32-3"),
  (10,"LogicalImmediate32-4"),           (10,"LogicalImmediate64-1"),          (10,"LogicalImmediate64-2"),
  (10,"LogicalImmediate64-3"),           (10,"LogicalImmediate64-4"),          (10,"Shift-1"),
  (10,"Shift-2"),                        (10,"MoveWide32"),                    (10,"MoveWide64"),
  (10,"BitfieldMove32"),                 (10,"BitfieldMove64"),                (0,"ConditionalCompareImmediate-1"),
  (10,"ConditionalCompareImmediate-2"),  (10,"ConditionalCompareImmediate-3"), (10,"ConditionalCompareImmediate-4"),
  (10,"ConditionalCompareRegister-1"),   (60,"ConditionalCompareRegister-2"),  (60,"ConditionalCompareRegister-3"),
  (10,"ConditionalCompareRegister-4"),   (10,"ConditionalSelect-1"),           (60,"ConditionalSelect-2"),
  (10,"CountLeading-1"),                 (10,"CountLeading-2"),                (10,"ExtractRegister32"),
  (10,"ExtractRegister64"),              (10,"Division-1"),                    (10,"Division-2"),
  (10,"MultiplyAddSub-1"),               (10,"MultiplyAddSub-2"),              (10,"MultiplyAddSubLong"),
  (0,"MultiplyHigh"),                    (10,"Reverse32"),                     (10,"Reverse64"),
  (0,"CRC8"),                            (0,"CRC16"),                          (0,"CRC32"),
  (0,"CRC64"),                           (10,"BranchConditional"),             (0,"BranchImmediate-1"),
  (10,"BranchImmediate-2"),              (10,"BranchRegisterJMP"),             (10,"BranchRegisterCALL"),
  (10,"BranchRegisterRET"),              (0,"CompareAndBranch-1"),             (0,"CompareAndBranch-2"),
  (10,"TestBitAndBranch-1"),             (10,"TestBitAndBranch-2"),            (10,"TestBitAndBranch-3"),
  (10,"TestBitAndBranch-4"),             (10,"LoadStoreImmediate-1-1"),        (10,"LoadStoreImmediate-1-2"),
  (10,"LoadStoreImmediate-1-3"),         (10,"LoadStoreImmediate-1-4"),        (10,"LoadStoreImmediate-1-5"),
  (10,"LoadStoreImmediate-1-6"),         (10,"LoadStoreImmediate-1-7"),        (10,"LoadStoreImmediate-1-8"),
  (10,"LoadStoreImmediate-1-9"),         (10,"LoadStoreImmediate-1-10"),       (10,"LoadStoreImmediate-1-11"),
  (10,"LoadStoreImmediate-1-12"),        (10,"LoadStoreImmediate-1-13"),       (10,"LoadStoreImmediate-1-14"),
  (10,"LoadStoreImmediate-1-15"),        (10,"LoadStoreImmediate-1-16"),       (10,"LoadStoreImmediate-1-17"),
  (10,"LoadStoreImmediate-1-18"),        (15,"LoadStoreImmediate-1-19"),       (10,"LoadStoreImmediate-1-20"),
  (10,"LoadStoreImmediate-1-21"),        (15,"LoadStoreImmediate-1-22"),       (10,"LoadStoreImmediate-1-23"),
  (10,"LoadStoreImmediate-1-24"),        (15,"LoadStoreImmediate-1-25"),       (10,"LoadStoreImmediate-1-26"),
  (10,"LoadStoreImmediate-1-27"),        (10,"LoadStoreImmediate-1-28"),       (10,"LoadStoreImmediate-2-1"),
  (10,"LoadStoreImmediate-2-2"),         (10,"LoadStoreImmediate-2-3"),        (10,"LoadStoreImmediate-2-4"),
  (10,"LoadStoreImmediate-2-5"),         (10,"LoadStoreImmediate-2-6"),        (10,"LoadStoreImmediate-2-7"),
  (10,"LoadStoreImmediate-2-8"),         (10,"LoadStoreImmediate-2-9"),        (10,"LoadStoreImmediate-2-10"),
  (10,"LoadStoreImmediate-2-11"),        (10,"LoadStoreImmediate-2-12"),       (10,"LoadStoreImmediate-2-13"),
  (10,"LoadStoreImmediate-2-14"),        (10,"LoadStoreImmediate-2-15"),       (10,"LoadLiteral-1"),
  (10,"LoadLiteral-2"),                  (10,"LoadLiteral-3"),                 (10,"LoadLiteral-4"),
  (10,"LoadStoreRegister-1"),            (80,"LoadStoreRegister-2"),           (60,"LoadStoreRegister-3"),
  (10,"LoadStoreRegister-4"),            (10,"LoadStoreRegister-5"),           (60,"LoadStoreRegister-6"),
  (10,"LoadStoreRegister-7"),            (10,"LoadStoreRegister-8"),           (10,"LoadStoreRegister-9"),
  (10,"LoadStoreRegister-10"),           (60,"LoadStoreRegister-11"),          (10,"LoadStoreRegister-12"),
  (10,"LoadStoreRegister-13"),           (60,"LoadStoreRegister-14"),          (10,"StorePair32-1"),
  (10,"StorePair32-2"),                  (10,"LoadPair32-1"),                  (10,"LoadPair32-2"),
  (10,"LoadStorePair64-1"),              (10,"LoadStorePair64-2"),             (10,"LoadStorePair64-3"),
  (10,"LoadStorePair64-4"),              (10,"NoOperation")]
			   
 fun instClass subs =
     hd (String.tokens  (fn c => Char.compare (c,#"-") = EQUAL) subs);

 (* ---------------------------------------------  *)
 type gen = Random.generator

 val emp_str = ""
 val splitter = String.tokens (fn c => c = #";");
     
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
     fun random_bit () =
	 if Random.range (0, 2) (rand_gen_get()) = 1 then boolSyntax.T else boolSyntax.F
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


 val whitespace_r =
     STAR (ALTERNATION [LITERAL #" ", LITERAL #"\t", LITERAL #"\n"])     
 val lowerAlphaList = regExLib.literalList "abcdefghijklmnopqrstuvwxyz"
 val upperAlphaList = regExLib.literalList "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
 val alphaList = lowerAlphaList @ upperAlphaList
 val numList = regExLib.literalList "1234567890"
 val specialChar= regExLib.literalList"[],#+-!"
 val identifierList =
     alphaList @ numList @ (regExLib.literalList "'_") @ specialChar @ [LITERAL #" ", LITERAL #"\t", LITERAL #"\n"]

 val alphabet_r = ALTERNATION (identifierList)

 val pattern_ld   = CONCATENATION [stringLiteral "ld", 
				   STAR(ALTERNATION(lowerAlphaList)),		
				   whitespace_r, 
				   ALTERNATION[(stringLiteral "xzr,"),(stringLiteral "wzr,")], 
				   STAR(alphabet_r),
				   END];    
 (* val pattern_stp   = CONCATENATION [stringLiteral "stp", whitespace_r, stringLiteral "xzr,", STAR (alphabet_r), END] *)
 val pattern_cbnz  = CONCATENATION [stringLiteral "cbnz", whitespace_r, STAR (alphabet_r), END]

 fun filter_inspected_instr str =
     let
	 fun reader nil    = NONE
           | reader (h::t) = SOME (h, t)
			     
	 fun checkPatterns (pattern, str) =	     
	     let
		 val result = Option.map (fn (str, strm) => str) (
			      evalRegex pattern reader (String.explode str)
			      )
		 val resultBool = if (isSome result) then true else false
	     in
		 resultBool
	     end
     in
	 (
	  checkPatterns(pattern_ld, str) orelse
	  checkPatterns(pattern_cbnz, str) 
	 )
     end
 (* filter_inspected_instr "ldr xzr, x19, [x21, #0xC8]"; *)

 fun instGen () =
     let
         val gen = rand_gen_get();
	 val ic = (snd(weighted_select arm8_names_weighted gen));
	 val ib = random ic;
	 val wl = filter (fn c => String.isSubstring "WORD" c) (decomp ib);
     in
	 if (not(null wl) orelse (filter_inspected_instr ((hd o splitter o hd o decomp) ib))) then instGen () else (ic, ib)
     end 
 (*
  val inst = "15c984de"
  val pc = 0
  val len = 3
  *)
 local
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
 fun branch_instGen (pc, len) =
     let
         val gen = rand_gen_get()
         val adr = (4*(Random.range (1, 1+len-pc) gen))
	 val adr_str = String.concat["b +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 fun c_branch_instGen (inst, pc, len) =
     let
         val gen = rand_gen_get()
         val adr = (4*(Random.range (1, 1+len-pc) gen))
	 val adr_str = String.concat[hd((p_tokens(hd(decomp(inst)))))," +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 fun cmp_and_branch_instGen (inst, pc, len) =
     let
         val gen = rand_gen_get()
         val adr = (4*(Random.range (1, 1+len-pc) gen))
	 val tks = (p_tokens(hd(decomp(inst))))
	 val rinst = String.concat[List.nth(tks,0), List.nth(tks,1),", +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast rinst)
     in
	 (emp_str, inst)
     end     
 end

 fun instsGen (pc, [], len)  =
     let val (c, inst) = instGen ()
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
     in
	 case (instClass c) of 
	     "BranchImmediate" =>  instsGen (pc, [], len)
	   | "BranchConditional" => instsGen (pc, [], len)
	   | "CompareAndBranch" => instsGen (pc, [], len)			   
	   | _ => if String.isPrefix "bl" inst
                  then instsGen (pc, [], len)
                  else (hd args, inst)
     end
     
   | instsGen (pc, src, len) =
     let val (c, inst) = instGen ()
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
	 val inclusion =  intersect (src, tl args)
     in
	 case (instClass c) of 
	     "BranchImmediate" =>  branch_instGen(pc, len)
	   | "BranchConditional" => c_branch_instGen (inst,pc, len)
	   | "CompareAndBranch" => cmp_and_branch_instGen (inst,pc, len)			   
	   | _ =>
	     if List.null inclusion orelse String.isPrefix "bl" inst
	     then instsGen (pc,src, len)
	     else (hd args, inst)
     end

 (* ---------------------------------------------  *)
 fun progGen n =
     let val src = ref ([]:string list);
	 val pc = ref 0;
     in
	 (List.tabulate (n, fn _ => let val (d,i) = (instsGen (!pc,!src, n)) 			
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
 (* takes the number of instructions to generate *)
 fun bir_prog_gen_arm8_rand n = map ((strip_ws_off false) o remove_junk o hd o decomp) (progGen n);

end; (* struct *)


