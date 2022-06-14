structure fence_insertionLib =
struct

local

    open arm8;
    
    (* error handling *)
    val libname  = "fence_insertionLib"
    val ERR      = Feedback.mk_HOL_ERR libname
    val wrap_exn = Feedback.wrap_exn libname
in


fun search_cond_branches binary  =
    let
	val instrs = List.map (fn i => Decode((Option.valOf o BitsN.fromHexString) (i,32))) binary;

	fun is_Branch x =
	    case x of
		Branch x => true
	      | _ => false;	    
	fun find_branches ([], instrs_marked) = instrs_marked
	  | find_branches (x::xs, instrs_marked) = (
	    if (is_Branch x) then
		find_branches (xs, instrs_marked@[(x, true)])
	    else find_branches (xs, instrs_marked@[(x, false)]))
							
    in find_branches (instrs, []) end;

fun patch_target_jump taddr baddr pos_fence =
    let
	open BitsN;
	val bfence = (valOf o BitsN.fromString) ((Arbnum.toString (valOf pos_fence)), 64);
	val bbaddr = (valOf o BitsN.fromString) ((Arbnum.toString baddr), 64);
	val btarget = taddr + bbaddr;
    in
    if (btarget > bfence andalso bbaddr > bfence)
    then taddr
    else (
	if (btarget > bfence andalso bbaddr < bfence)
	then taddr + (B (4, 64))
	else (
	    if (btarget < bfence andalso bbaddr > bfence)
	    then taddr - (B (4, 64))
	    else taddr
	    )
	)
    end;

    	    
fun patch_branch_target ast pos_fence addr =
    case ast of
	BranchConditional (t1, t2) => BranchConditional ((patch_target_jump t1 addr pos_fence), t2)
      | BranchImmediate (t1, t2) => BranchImmediate ((patch_target_jump t1 addr pos_fence), t2)
      | BranchRegister t => BranchRegister t
      | CompareAndBranch''32 (c, (b, (t1, t2))) => CompareAndBranch''32 (c, (b, ((patch_target_jump t1 addr pos_fence), t2)))
      | CompareAndBranch''64 (c, (b, (t1, t2))) => CompareAndBranch''64 (c, (b, ((patch_target_jump t1 addr pos_fence), t2)))
      | TestBitAndBranch''32 (s, (imm, (b, (t1, t2)))) => TestBitAndBranch''32 (s, (imm, (b, ((patch_target_jump t1 addr pos_fence), t2))))
      | TestBitAndBranch''64 (s, (imm, (b, (t1, t2)))) => TestBitAndBranch''64 (s, (imm, (b, ((patch_target_jump t1 addr pos_fence), t2))))
fun patch_branch (addr, ast, b) pos_fence =
    case ast of
	Branch ast => (addr, Branch (patch_branch_target ast pos_fence addr), b)
      | ast => (addr, ast, b)


fun patch_program ([], pos_fence, fixed_instrs) = fixed_instrs
  | patch_program (i::is, pos_fence, fixed_instrs) = patch_program (is, pos_fence, fixed_instrs@[(patch_branch i pos_fence)])
    
fun fence_insertion binary =
    let
	open Arbnum;
	val instrs = search_cond_branches binary;
	val nop_i = Hint SystemHintOp_NOP;
	(* val mb: instruction = MemoryBarrier (MemBarrierOp_DMB, BitsN.B (12, 64)); *)

	fun is_Branch x =
	    case x of
		Branch x => true
	      | _ => false;


	fun transform_prog ([], new_instrs, count, pos_fence, active) = (new_instrs, pos_fence)
	| transform_prog ((x::xs), new_instrs, count, pos_fence, active) =
	    let
		val (i: instruction, b: bool) = x;
		val count = count + (Arbnum.fromInt 4)
	    in
		if (active=true andalso b=true andalso (is_Branch i))
		then (
		    let
			val pos_fence = SOME (count-(Arbnum.fromInt 4));
			val active = false
		    in
			transform_prog (xs, new_instrs@[(count-(Arbnum.fromInt 4), nop_i, false), (count, i, false)], count, pos_fence, active)
		    end)
		else (
		    transform_prog (xs, new_instrs@[(count, i, b)], count, pos_fence, active)
		    )
	    end;

	val (instrs_with_fence, pos_fence) = transform_prog (instrs, [], Arbnum.fromInt 0, NONE, true);
	val patched_prog = patch_program (instrs_with_fence, pos_fence, []);
	(* val instrs2 = List.map (fn (a,i,b)=>(i,b)) instrs_with_fence; *)
	    
    in patched_prog end;
    
(*
open bir_inst_liftingLibTypes;
fun unpack_code x =
    case x of
	(str: string, BILME_code s) => (str, s)
      | (str: string, BILME_data) => (str, NONE)  
      | (str: string, BILME_unknown) => (str, NONE)
      | _ => raise ERR "unpack_code" "";  
fun unpack_section x =
    case x of
	(BILMR (addr, l)) => (addr, (List.map unpack_code l))
      | _ => raise ERR "unpack_section" "section not as expected";
fun get_binary_instrs section =
    let
	val (addr, code) = unpack_section section
    in
	(addr, List.map (fn (hex_code, str_inst) => hex_code) code)
    end;

open bir_prog_genLib;
val asm_code = "\tldr x25, [x19,x4]\n\tldr x26, [x29, #173]\n\tcmp x19, x26\n\tb.eq #0xC\n\tldr x13, [x25, #209]\n\tldr x22, [x13, #16]\n\tldr x24, [x13, #16]\n\tb #0x8\n\tldr x12, [x13, #16]\n";
val asm_code = "cbz\tx0, 400668\n";
val asm_code = "br\tx1\n";
val asm_code = "\tldr\tw0, [x0]\n\ttbz x3, #0, 0\n";
val asm_code = "\tldr x25, [x19,x4]\n\tldr x26, [x29, #173]\n\tcmp x19, x26\n\tb.eq #0xC\n\tldr x13, [x25, #209]\n\tldr x22, [x13, #16]\n\tldr x24, [x13, #16]\n\tb #-0x8\n\tldr x12, [x13, #16]\n";
val asm_code = "\tldr x25, [x19,x4]\n\tldr x26, [x29, #173]\n\tcmp x19, x26\n\tb.eq #0xC\n\tldr x13, [x25, #209]\n\tldr x22, [x13, #16]\n\tldr x24, [x13, #16]\n\tb #-0x18\n\tldr x12, [x13, #16]\n";
val sections = (process_asm_code asm_code);
val (addr, binary) = hd (List.map get_binary_instrs sections);


val i = List.nth (instrs, 3);
val nb = patch_branch i;
instructionToString nb;


val patched_asm_code = List.map (fn (a,i,b)=> instructionToString i) patched_prog;
val filename = TextIO.openOut "test_asm_code.s";
val _ = List.map (fn (s1,s2)=> TextIO.output (filename, s1 ^ "\t" ^ s2 ^ "\n")) patched_asm_code;
val _ = TextIO.closeOut filename;
val asm_code = bir_fileLib.read_from_file ("test_asm_code.s");
*)
    
    
end


end
