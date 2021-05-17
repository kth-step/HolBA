signature herdLitmusProgLib =
sig
    include Abbrev
    (* Argument: Program section
       Returns: List of BIR programs *)
    val parse_prog : string -> term list
end


structure herdLitmusProgLib : herdLitmusProgLib =
struct
open HolKernel Parse bossLib boolLib
open bir_lifter_interfaceLib
open UtilLib

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble prog =
    let
	val proc = Unix.execute("./compile_and_da.sh", [])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

fun lift_prog prog =
    let
	(* Create a DA file *)
	val da_file = compile_and_disassemble prog
	(* Lift the DA file *)
	val _ = lift_da_and_store_mc_riscv "litmus_tmp" da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
	(* Fetch the Program definition *)
	val bir_litmus_tmp_prog_def = DB.fetch "scratch" "bir_litmus_tmp_prog_def"
    in (* Return the program term *)
	(rhs o concl) bir_litmus_tmp_prog_def
    end

fun parse_prog prog_sec =
    let
	fun split c = String.tokens (eq c)
	val stmts = transpose (map (split #"|") (tl (split #";" prog_sec)))
	val progs = map ((fn x => x ^ "\n") o (String.concatWith "\n")) stmts
	val bir_progs = map lift_prog progs
    in bir_progs end
end
