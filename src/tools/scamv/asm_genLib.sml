structure asm_genLib :> asm_genLib =
struct

open qc_genLib;
infix 5 <$>;
infix 5 >>=;

datatype BranchCond = EQ | NE | LT | GT
datatype Operand =
         Imm of int
         | Ld of int option * string
         | Reg of string
datatype ArmInstruction =
         Load of Operand * Operand
         | Branch of BranchCond option * Operand

(* pp *)

fun pp_operand (Imm n) = "#0x" ^ Int.fmt StringCvt.HEX n
  | pp_operand (Ld (NONE, src)) = "[" ^ src ^ "]"
  | pp_operand (Ld (SOME offset, src)) =
    "[" ^ src ^ ", #" ^ Int.toString offset ^ "]"
  | pp_operand (Reg str) = str

fun pp_opcode (Load _) = "ldr"
  | pp_opcode (Branch _) = "b"

fun pp_cond bc =
    case bc of
        EQ => "eq"
      | NE => "ne"
      | LT => "lt"
      | GT => "gt"

fun pp_instr instr =
    case instr of
        Load (target,source) =>
        pp_opcode instr ^ " " ^ pp_operand target ^ ", "
        ^ pp_operand source
     |  Branch (NONE, target) =>
        "b " ^ pp_operand target
     | Branch (SOME cond, target) =>
       "b." ^ pp_cond cond ^ " " ^ pp_operand target

fun pp_program is = List.map pp_instr is;

(* arb instances *)

val min_addr = 0x1000;
val max_addr = 0x2000;
val arb_addr = choose (min_addr, max_addr);

val arb_armv8_regname =
    let
        fun regs n = List.tabulate (n, fn x => "x" ^ (Int.toString x))
    in
        elements (regs 30)
    end;

val arb_imm = Imm <$> arb_addr;
val arb_reg = Reg <$> arb_armv8_regname;
val arb_operand =
    frequency
        [(1, arb_imm)
        ,(5, arb_reg)]

fun arb_option m =
    frequency [(1,return NONE)
              ,(2,SOME <$> m)];

val arb_branchcond =
    let val arb_cond = elements [EQ, NE, LT, GT];
    in
        arb_option arb_cond
    end;

val arb_ld = Ld <$> two (arb_option (elements [4,8,16])) arb_armv8_regname;

val arb_instruction =
    frequency
        [(1, Load <$> (two arb_reg (oneof [arb_ld, arb_imm])))
        ,(1, Branch <$> (two arb_branchcond arb_imm))]

val max_prog_size = 10;

fun arb_list_of m =
    sized (fn prog_size =>
              repeat prog_size m);

val arb_program = arb_list_of arb_instruction;

local
    open Random;
    val fresh_seed = false;
    val g = ref (if fresh_seed
                 then newgen ()
                 else newgenseed 3141592.654);
in
fun prog_gen_a_la_qc n =
    let val (p, rnd) = run_step n (!g) arb_program;
        val _ = (g := rnd);
    in
        pp_program (generate n (!g) arb_program)
    end
end

end
