signature herdLitmusProgLib =
sig
    include Abbrev
    (* Argument: Program section
       Returns: List of BIR programs *)
    val parse_prog : string -> term list
    exception WrongType;
end


structure herdLitmusProgLib : herdLitmusProgLib =
struct
open HolKernel Parse bossLib boolLib
open listSyntax;
open bir_lifter_interfaceLib
open bir_programSyntax bir_expSyntax;
open bslSyntax;
open UtilLib;

val SOURCE_DIR = valOf (Posix.ProcEnv.getenv ("PWD"))

(* compile and disassemble the program, returns the filename of the .da file *)
fun compile_and_disassemble prog =
    let
	val proc = Unix.execute(SOURCE_DIR ^ "/compile_and_da.sh", [])
	val (inStream, outStream) = Unix.streamsOf proc
    in
	TextIO.output(outStream, prog) before TextIO.closeOut outStream;
	TextIO.inputAll(inStream) before TextIO.closeIn inStream
    end

(* Replace the nop with Halt *)
fun patch_halt prog =
  let
    val prog_l = bir_programSyntax.dest_BirProgram prog
    val (blocks,ty) = dest_list prog_l;
    val obs_ty = (hd o snd o dest_type) ty;
    val (lbl,_,_,_) = bir_programSyntax.dest_bir_block (List.last blocks);
    val new_last_block =  bir_programSyntax.mk_bir_block
              (lbl, “F”, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
               ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);

    val blocks' = (List.take (blocks, (List.length blocks) - 1))@[new_last_block];
  in
    bir_programSyntax.mk_BirProgram (mk_list (blocks',ty))
  end;

fun lift_prog prog =
    let
	(* Create a DA file, also put nop at end *)
	val da_file = compile_and_disassemble (prog ^ "\nnop\n")
	(* Lift the DA file *)
	val _ = lift_da_and_store_mc_riscv "litmus_tmp" da_file (Arbnum.fromInt 0, Arbnum.fromInt 1000)
	(* Fetch the Program definition *)
	val bir_litmus_tmp_prog_def = DB.fetch "scratch" "bir_litmus_tmp_prog_def"
    in (* Return the program term *)
	(patch_halt o rhs o concl) bir_litmus_tmp_prog_def
    end
	
fun tokens p s = 
    let
	val length = String.size s
	fun tok i j =
	    if j = length then
		[String.substring (s, i, j-i)]
	    else if p (String.sub (s,j)) then
		String.substring (s, i, j-i) :: tok (j+1) (j+1)
	    else tok i (j+1)
    in tok 0 0 end

local
  val count = ref 0;
in
fun reset_var () = (count := 0)
fun fresh_var ty =
    let val v = bvar ("TMP"^(PolyML.makestring (!count))) ty;
    in (count := !count + 1; v)
    end;
end

exception WrongType;
val term_EVAL = rhs o concl o EVAL

fun bir_type exp =
    let open bir_typing_expTheory optionSyntax;
        val ty = term_EVAL “type_of_bir_exp ^exp”;
    in
      if is_some ty
      then dest_some ty
      else raise WrongType
    end;


fun canonicalise_prog prog =
    let 
	val (block_list,ty) = dest_list (dest_BirProgram prog);
	fun fix_cast stmt =
	    if is_BStmt_Assign stmt
	    then let val (var,body) = dest_BStmt_Assign stmt;
		 in
		     if is_BExp_Cast body
		     then let val (cast, exp, ty) = dest_BExp_Cast body;
			      val tmp_var = fresh_var “BType_Imm Bit64”;
			  in
			      [mk_BStmt_Assign (var, exp)]
			      (*
			      [mk_BStmt_Assign (tmp_var,exp), 
			       mk_BStmt_Assign(var, mk_BExp_Cast (cast, bden tmp_var, ty))] *)
			  end
		     else [stmt]
		 end
	    else  [stmt];
	fun fix_block block =
	    let val (lbl,is_atomic,stmts,last_stmt) = dest_bir_block block;
		val (stmt_list,stmt_ty) = dest_list stmts;
		val new_stmts = mk_list (List.concat (List.map fix_cast stmt_list), stmt_ty);
	    in
		mk_bir_block (lbl,is_atomic,new_stmts,last_stmt)
	    end;
    in
	reset_var ();
	mk_BirProgram (mk_list (List.map fix_block block_list,ty))
    end;

fun typed_prog p = inst [“:'observation_type” |-> Type`:'a`] p;

fun parse_prog prog_sec =
    let
	fun split c = tokens (eq c)
	val stmts = transpose (map (split #"|") (tl (split #";" prog_sec))) ""
	val progs = map (String.concatWith "\n") stmts
	val bir_progs = map (canonicalise_prog o typed_prog o lift_prog) progs
    in bir_progs end
end

(*
open listSyntax bir_programSyntax;
val example = 
 "P0          | P1          ;"^
 "sw x5,0(x6) | sw x5,0(x6) ;"^
 "sw x5,0(x7) | lw x7,0(x8) ;"
val prog2 = tl $ parse_prog example

*)
