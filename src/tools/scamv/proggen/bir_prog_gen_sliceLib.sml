structure bir_prog_gen_sliceLib :> bir_prog_gen_sliceLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open arm8_progLib arm8AssemblerLib arm8;

  (* error handling *)
  val libname  = "bir_prog_gen_sliceLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

open bir_randLib;
open holba_miscLib;
     
fun remChars  (c,s) =
    let fun rem [] = []
          | rem (c'::cs) =
            if c = c'
            then rem cs
            else c'::rem cs
    in
	implode (rem (explode s)) 
    end

val splitter = String.tokens (fn c => c = #";");

type gen = Random.generator

fun genint gen max =
    Random.range (0,max+1) gen     

fun decomp el =  arm8AssemblerLib.arm8_disassemble [QUOTE el];

val hex = Int.fmt StringCvt.HEX;

fun objdump infile outfile =
    let val _ = OS.FileSys.access (infile, [OS.FileSys.A_READ]) orelse
                raise OS.SysErr ("Cannot read file: " ^ infile,NONE)
        val s = String.concat ["arm-elf-objdump -d -j .text -j .data -j .rodata ",
                               infile, " > ", outfile]
        val _ = OS.Process.isSuccess (OS.Process.system s) orelse
                raise OS.SysErr ("Failed to run arm-elf-objdump",NONE)
    in
        ()
    end;

fun remove_padding s =
    s |> Substring.full
      |> Substring.dropl Char.isSpace
      |> Substring.dropr Char.isSpace
      |> Substring.string;

fun parse_objdump infile =
    let val istrm = TextIO.openIn infile
        val inp = TextIO.inputAll istrm before TextIO.closeIn istrm
        val l = List.drop (String.tokens (fn c => c = #"\n") inp, 3)
        fun get_tokens s =
            case String.tokens (fn c => c = #":") s
             of (n::instr::rest) =>
                (remove_padding
                     (hd (String.tokens (fn c => c = #"\t") instr)))
              | _ => raise ERR "parse_objdump" "failed to parse line"
    in
        Lib.mapfilter get_tokens l
    end;

fun load_elf infile =
    let val tmp = OS.FileSys.tmpName ()
        val _ = objdump infile tmp
    in
        parse_objdump tmp before OS.FileSys.remove tmp
    end;


fun c_data ast =
    case ast of
	AddSubCarry''32 d => "AddSubCarry''32"
      | AddSubCarry''64 d => "AddSubCarry''64"
      | AddSubExtendRegister''32 d => "AddSubExtendRegister''32"
      | AddSubExtendRegister''64 d => "AddSubExtendRegister''64"
      | AddSubImmediate''32 d => "AddSubImmediate''32"
      | AddSubImmediate''64 d => "AddSubImmediate''64"
      | AddSubShiftedRegister''32 d => "AddSubShiftedRegister''32"
      | AddSubShiftedRegister''64 d => "AddSubShiftedRegister''64"
      | LogicalImmediate''32 d => "LogicalImmediate''32"
      | LogicalImmediate''64 d => "LogicalImmediate''64"
      | LogicalShiftedRegister''32 d => "LogicalShiftedRegister''32"
      | LogicalShiftedRegister''64 d => "LogicalShiftedRegister''64"
      | Shift''32 d => "Shift''32"
      | Shift''64 d => "Shift''64"
      | MoveWide''32 d => "MoveWide''32"
      | MoveWide''64 d => "MoveWide''64"
      | BitfieldMove''32 d => "BitfieldMove''32"
      | BitfieldMove''64 d => "BitfieldMove''64"
      | ConditionalCompareImmediate''32 d => "ConditionalCompareImmediate''32"
      | ConditionalCompareImmediate''64 d => "ConditionalCompareImmediate''64"
      | ConditionalCompareRegister''32 d => "ConditionalCompareRegister''32"
      | ConditionalCompareRegister''64 d => "ConditionalCompareRegister''64"
      | ConditionalSelect''32 d => "ConditionalSelect''32"
      | ConditionalSelect''64 d => "ConditionalSelect''64"
      | CountLeading''32 d => "CountLeading''32"
      | CountLeading''64 d => "CountLeading''64"
      | ExtractRegister''32 d => "ExtractRegister''32"
      | ExtractRegister''64 d => "ExtractRegister''64"
      | Division''32 d => "Division''32"
      | Division''64 d => "Division''64"
      | MultiplyAddSub''32 d => " MultiplyAddSub''32"
      | MultiplyAddSub''64 d => "MultiplyAddSub''64"
      | MultiplyAddSubLong d => "MultiplyAddSubLong"
      | MultiplyHigh d => "MultiplyHigh"
      | Reverse''32 d => "Reverse''32"
      | Reverse''64 d => "Reverse''64"

fun c_branch ast =
    case ast of
	BranchConditional d =>"BranchConditional"
      | BranchImmediate d => "BranchImmediate"
      | BranchRegister d => "BranchRegister"
      | CompareAndBranch''32 d => "CompareAndBranch''32"
      | CompareAndBranch''64 d => "CompareAndBranch''64"
      | TestBitAndBranch''32 d => "TestBitAndBranch''32"
      | TestBitAndBranch''64 d => "TestBitAndBranch''64"

fun c_load_store ast =
    case ast of
	LoadStoreImmediate''8 d => "LoadStoreImmediate''8"
      | LoadStoreImmediate''16 d => "LoadStoreImmediate''16"
      | LoadStoreImmediate''32 d => "LoadStoreImmediate''32"
      | LoadStoreImmediate''64 d => "LoadStoreImmediate''64"
      | LoadStoreRegister''8 d => "LoadStoreRegister''8"
      | LoadStoreRegister''16 d => "LoadStoreRegister''16"
      | LoadStoreRegister''32 d => "LoadStoreRegister''32"
      | LoadStoreRegister''64 d => "LoadStoreRegister''64"
      | LoadLiteral''32 d => "LoadLiteral''32"
      | LoadLiteral''64 d => "LoadLiteral''64"
      | LoadStorePair''32 d => "LoadStorePair''32"
      | LoadStorePair''64 d => "LoadStorePair''64"
      | LoadStoreAcquire''8 d => "LoadStoreAcquire''8"
      | LoadStoreAcquire''16 d => "LoadStoreAcquire''16"
      | LoadStoreAcquire''32 d => "LoadStoreAcquire''32"
      | LoadStoreAcquire''64 d => "LoadStoreAcquire''64"
      | LoadStoreAcquirePair''64 d => "LoadStoreAcquirePair''64"
      | LoadStoreAcquirePair''128 d => "LoadStoreAcquirePair''128";

fun instClass subs =
    hd (String.tokens  (fn c => Char.compare (c,#"'") = EQUAL) subs);


fun instructionClass ast =
    case ast of
	Address a => "Address"
      | Data d => instClass(c_data d)
      | LoadStore d => instClass(c_load_store d)
      | Branch b => instClass(c_branch b)
      | _ => "NOI"

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
fun branch_instGen (pc, base, len) =
    let
        val gen = rand_gen_get ()
        val adr = base + (4*(Random.range (pc, len) gen))
	val adr_str = String.concat["bl +#0x", (addr_to_hexString(adr))]
	val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
    in
	(inst)
    end
fun cond_branch_instGen (inst, pc, base, len) =
    let
        val gen = rand_gen_get ()
        val adr = base + (4*(Random.range (pc, len) gen))
	val adr_str = String.concat[hd((p_tokens(hd(decomp(inst)))))," +#0x", (addr_to_hexString(adr))]
	val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
    in
	(inst)
    end

fun cmp_and_branch_instGen (inst, pc, base, len) =
    let
        val gen = rand_gen_get ()
        val adr = base + (4*(Random.range (pc, len) gen))
	val tks = (p_tokens(hd(decomp(inst))))
	val rinst = String.concat[List.nth(tks,0), List.nth(tks,1),", +#0x", (addr_to_hexString(adr))]
	val inst = (valOf o snd o cmp_mcode)(cmp_ast rinst)
    in
	(inst)
    end

end

fun filter_slice (n, insts, base) =
    let val pc = ref 0;
	fun instsGen (pc, inst, cls, base, len) =
	    case (cls) of 
		"BranchImmediate" => decomp(branch_instGen(pc, base, len))
	      | "BranchConditional" => decomp(cond_branch_instGen (inst,pc, base, len))
	      | "CompareAndBranch" => decomp(cmp_and_branch_instGen (inst,pc, base, len))
	      | _ => decomp inst

    in
	(map (fn (cls, i) => let val v = instsGen (!pc, i, cls, base, n) in (pc := !pc + 1); v end) insts)
    end

fun bir_prog_slice_arm8_rand (inputfile, base, len) =
    let val t1  = parse_objdump inputfile
	val t2  = map (fn i => (instructionClass ((Decode((Option.valOf o BitsN.fromHexString) (i ,32)))), i)) t1
	val idx = genint (rand_gen_get ()) ((List.length t1) - len)
	val instructions = List.take(List.drop(t2,idx), len)
    in
	filter_slice (len, instructions, base)
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
 fun bir_prog_gen_arm8_slice n = 
     let val mc = map (fn i => let val a::b::l = splitter (remChars (#" ", (hd i))) in b end)(bir_prog_slice_arm8_rand ("/home/xmate/Projects/HolBA/HolBA/examples/aes/bin/aes-aarch64.da", 0, n))
     in
	 map ((strip_ws_off false) o remove_junk o hd o decomp) (mc)
     end
     
end; (* struct *)




