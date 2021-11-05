    signature herdLitmusLib =
sig
    include Abbrev
    type litmus = {arch:string,
		   name:string,
		   info:string list,
		   inits: term * term list,
		   progs: term list,
		   final: term}

    (* Argument: path to herdtools litmus test
       Returns: Litmus test for BIR. *)
    val parse : string -> litmus
end



structure herdLitmusLib : herdLitmusLib =
struct
open HolKernel Parse boolLib bossLib;
open stringSyntax;
open bir_execLib bir_valuesSyntax bir_immSyntax;

open UtilLib

open herdLitmusProgLib herdLitmusInitLib herdLitmusFinalLib

type litmus = {arch:string,
	       name:string,
	       info:string list,
	       inits: term * term list,
	       progs: term list,
	       final: term}

(* Split the herd litmus test into sections *)
local
    fun remove_comments s =
	let
	    fun comment_start (x::y::r, acc) = 
		(case (x,y) of (#"(", #"*") => comment_end (r, acc)
			     | _ => comment_start (y::r, x::acc))
	      | comment_start (xs, acc) = List.revAppend (acc, xs)
	    and comment_end (x::y::r, acc) =
		(case (x,y) of (#"*", #")") => comment_start (r, acc)
			     | _ => comment_end (y::r, x::acc))
	      | comment_end _ = raise Fail "Expected end of comment"
	in String.implode (comment_start (String.explode s, [])) end
    fun names [] = raise Fail "Expected arch and testname"
      | names (x::lines) =
	case String.tokens Char.isSpace x
	 of (arch::name::_) => ((arch, name), lines)
	  | _ => raise Fail "Expected arch and testname"
    fun info [] = raise Fail "Expected info section"
      | info (x::r) =
	if String.isPrefix "{" x then
	    ([], x::r)
	else
	    let val (xs, r2) = info r in (x::xs, r2) end
    fun init [] = raise Fail "Expected init section"
      | init (x::r) =
	if String.isSuffix "}" x then
	    ([x],r)
	else
	    let val (xs, r2) = init r in (x::xs, r2) end
    fun prog [] = raise Fail "Expected prog and final"
      | prog (x::r) =
	if String.isSuffix ";" x then
	    let val (xs, r2) = prog r in (x::xs, r2) end
	else
	    ([], x::r)
in
fun split_to_sections text =
    let
	val ls1 = String.tokens (eq #"\n") (remove_comments text)
	val ls1' = map (trim Char.isSpace) ls1
	val ls1'' = List.filter (fn s => not(s = "")) ls1'
	val ((arch, name), ls2) = names ls1''
	val (info_sec, ls3) = info ls2
	val (init_sec, ls4) = init ls3
	val (prog_sec, final_sec) = prog ls4
    in (arch, name, info_sec, String.concat init_sec,
	String.concat prog_sec, String.concat final_sec) end
    handle Fail msg => raise Fail ("Failed splitting herd litmus test: " ^ msg)
end; (* local *)


val term_EVAL = rhs o concl o EVAL


fun regs_of_prog prog =
    let
	val bvars = strip_set $ term_EVAL “bir_varset_of_program ^prog”
	val regs = filter (is_BType_Imm o snd)$ map dest_BVar bvars
	fun f (x,y) = (fromHOLstring x, size_of_bir_immtype_t $ dest_BType_Imm y)
    in map f regs end

fun parse text =
    let
	(* Split text into sections *)
	val (arch, name, info_sec, init_sec, prog_sec, final_sec)
	    = split_to_sections text
	(* Parse the program section, create one bir_program per processes *)
	val progs = parse_prog prog_sec
	(* Get registers used by each program *)
	val progs_regs = map regs_of_prog progs
	(* Parse init section, get initial bir memory and thread environments *)
	val inits = parse_init init_sec progs_regs
	(* Parse the constraint, returns a predicate for a set of bir states *)
	val final = parse_final final_sec
    in
	{arch=arch,
	 name=name,
	 info=info_sec,
	 inits=inits,
	 progs=progs,
	 final=final}
    end
(*
val filename = "../tests/non-mixed-size/BASIC_2_THREAD/MP+po+addr.litmus"
val prog = hd $ tl progs
val text = bir_fileLib.read_from_file filename;
val (arch, name, info_sec, init_sec, prog_sec, final_sec) = split_to_sections text
val progs = parse_prog prog_sec
*)

end (* herdLitmusLib *)
