signature herdLitmusInitLib =
sig
    include Abbrev
    (* Arguments: Init section, registers used by each program
       Returns: BIR environments for memory and threads *)
    val parse_init : string -> (string list list) -> term * term list
end


structure herdLitmusInitLib : herdLitmusInitLib =
struct
(* Parse the init section *)
open HolKernel Parse boolLib bossLib
open stringSyntax numSyntax wordsSyntax combinSyntax
open pairSyntax optionSyntax finite_mapSyntax
open bir_immSyntax bir_envSyntax bir_valuesSyntax
open UtilLib herdLitmusRegLib
open Listsort

fun fst2 ((x,_),(y,_)) = (x,y)

fun snd2 ((_,x),(_,y)) = (x,y)

(* Get individual tokens *)
fun tokenize init_sec =
    let
	fun f x = (x = #";" orelse x = #"{" orelse x = #"}")
	val assigns = String.tokens f init_sec
    in map (trim Char.isSpace) assigns end

(* Split initial assignments of memory and thread *)
fun partition assigns =
    let
	(* riscv_cannonize converts ABI register to standard register names,
	   e.g., a1 -> x11. *)
	fun mk_reg (t,r,v) = (valOf (Int.fromString t),
			      (riscv_cannonize r, v))
	fun loop [] = ([], [])
	  | loop (x::xs) =
	    let val (mem, thds) = loop xs
	    in (case split (eq #"=") x
		 of SOME(l, v) =>
		    (case split (eq #":") l
		      of SOME (t, r) =>
			 (mem,mk_reg(t,r,v)::thds)
		       | NONE => ((l,v)::mem, thds))
		  | NONE => raise Fail "Expected assignment")
	    end
    in loop assigns end

(* Group register initial values by their threads *)
fun group_regs regs =
    let
	val sorted = sort (Int.compare o fst2) regs
	val grouped = groupBy (op= o fst2) sorted
    in map (map snd) grouped end

(* Default value of a register used by a program is 0.
   If init state does not set a value to the register, we set it to 0*)
fun padd_regs regs prog_regs =
    let
	fun mk_defaults ([],_) = []
	  | mk_defaults (regs::rest,n) =
	    map (fn r => (n,(r,"0"))) regs @ mk_defaults (rest,n+1)
	val defaults = mk_defaults (prog_regs, 0)
	fun eq_tid_reg a = (op= o fst2) a andalso (op= o fst2 o snd2) a
    in
	(* Merge regs and default_regs, keep the first tuple only *)
	nubBy eq_tid_reg (regs @ defaults)
    end

(* Make BIR environment for memory *)
fun mk_mem_env mem =
    let
	val f = mk_w2n o word_of_string
	val mem_num = map (fn (x,y) => mk_pair(f x, f y)) mem
	val fmap = list_mk_fupdate (mk_fempty(num,num), mem_num)
	val bval = mk_BVal_Mem (Bit64_tm,Bit8_tm,fmap)
	val env_empty = “(K NONE) : string -> bir_val_t option”
	val env = mk_comb(mk_update (“"MEM8"”, mk_some bval), env_empty)
    in mk_BEnv env end

(* Make BIR environment for a thread *)
fun mk_thd_env regs =
    let
	val f = mk_Imm64 o word_of_string
	fun str2term (r,v) = (fromMLstring r, mk_some (mk_BVal_Imm(f v)))
	val list_mk_update = foldl (fn(r,e) => mk_comb(mk_update r, e))
	val env_empty = “(K NONE) : string -> bir_val_t option”
	val regs_hol = map str2term regs
	val env = list_mk_update env_empty regs_hol
    in mk_BEnv env end

fun parse_init init_sec prog_regs =
    let
	val assigns = tokenize init_sec
	val (mem, regs) = partition assigns
	val grouped_regs = group_regs (padd_regs regs prog_regs)
	val mem_env = mk_mem_env mem
	val thd_envs = map mk_thd_env grouped_regs
    in
	(mem_env, thd_envs)
    end
end
