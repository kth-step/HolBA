signature asm_genLib =
sig
    include qc_genLib;

    datatype BranchCond = EQ | NE | LT | GT
    datatype Operand =
             Imm of int
             | Ld of int option * string
             | Reg of string
    datatype ArmInstruction =
             Load of Operand * Operand
             | Branch of BranchCond option * Operand
             | Compare of Operand * Operand
             | Nop
             | Add of Operand * Operand * Operand

    val pp_program : ArmInstruction list -> string list;

    val arb_addr : int Gen;

    val arb_imm : Operand Gen;
    val arb_reg : Operand Gen;
    val arb_armv8_regname : string Gen;
    val arb_operand : Operand Gen;

    val arb_branchcond : BranchCond option Gen;
    val arb_ld : Operand Gen;
    val arb_instruction_noload_nobranch : ArmInstruction Gen;
    val arb_program_load : ArmInstruction list Gen;
    val prog_gen_a_la_qc : int -> string list;
end

