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
open listSyntax bir_programSyntax;
open bir_lifter_interfaceLib
open UtilLib

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

(* Get the label of the bir_block *)
fun get_label tm =
    let
	val (ty, l) = TypeBase.dest_record tm
	val _ = if is_bir_block_t_ty ty then () else fail()
    in Lib.assoc "bb_label" l end

(* Replace the nop with Halt *)
fun patch_halt prog =
  let
    val prog_l = dest_BirProgram prog
    val (blocks,ty) = dest_list prog_l;
    val obs_ty = (hd o snd o dest_type) ty;
    val lbl = get_label (List.last blocks);
    val new_last_block =  bir_programSyntax.mk_bir_block
              (lbl, “F”, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
               ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);

    val blocks' = (List.take (blocks, (List.length blocks) - 1))@[new_last_block];
  in
    mk_BirProgram (mk_list (blocks',ty))
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

fun parse_prog prog_sec =
    let
	fun split c = String.tokens (eq c)
	val stmts = transpose (map (split #"|") (tl (split #";" prog_sec)))
	val progs = map (String.concatWith "\n") stmts
	val bir_progs = map lift_prog progs
    in bir_progs end
end

(*
val example = "P0 | P1;"
	 ^ "sw x1, 0(x2) | sw x1, 0(x2);"
	 ^ "lw x4, 0(x3) | lw x4, 0(x3);"
val [prog1, prog2] = parse_prog example


open listSyntax bir_programSyntax;


*)
