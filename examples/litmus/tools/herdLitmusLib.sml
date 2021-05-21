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
open HolKernel Parse boolLib bossLib
open bir_execLib

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
	val ls1 = String.tokens (eq #"\n") text
	val ls1' = map (trim Char.isSpace) ls1
	val ((arch, name), ls2) = names ls1'
	val (info_sec, ls3) = info ls2
	val (init_sec, ls4) = init ls3
	val (prog_sec, final_sec) = prog ls4
    in (arch, name, info_sec, String.concat init_sec,
	String.concat prog_sec, String.concat final_sec) end
    handle Fail msg => raise Fail ("Failed splitting herd litmus test: " ^ msg)
end; (* local *)


(* Gets the registers used by the program *)
fun regs_of_prog prog =
    let val bvars = gen_vars_of_prog prog
	val names = map (fst o dest_BVar_string) bvars
	val regs = List.filter (String.isPrefix "x") names
    in regs end


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

end (* herdLitmusLib *)
