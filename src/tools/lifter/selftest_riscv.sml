open HolKernel Parse
open testutils
open bir_inst_liftingLib;
open PPBackEnd
open riscv_assemblerLib;
open selftestLib;

(* Flags for determining type of output *)
val unicode = false;
val raw_output = false;

(* Flags used here *)
val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)

(* TODO: Any other way to supply this to the functor? *)
structure log_name =
struct
  val log_name = "riscv_selftest.log";
end;

structure test_RISCV = test_bmr(structure MD = bmil_riscv; structure log_name_str = log_name);

(* TODO: Double-check these numbers are OK, should work with arbitrary ones though *)
val mu_b = Arbnum.fromInt 0; (* Memory starts at address 0x0 *)
val mu_e = Arbnum.fromInt 0x1000000; (* Memory ends at address 0x1000000 *)
val pc =   Arbnum.fromInt 0x10030; (* Program counter is at address 0x10030 *)


fun riscv_test_hex hex = test_RISCV.lift_instr mu_b mu_e pc hex NONE
fun riscv_test_asm asm =
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    riscv_test_hex (riscv_hex_from_asm asm)
  end
;
val riscv_test_asms = map riscv_test_asm

val _ = test_RISCV.print_log true "\n";
val _ = test_RISCV.print_log_with_style test_RISCV.sty_HEADER true "MANUAL TESTS (HEX) - RISC-V RV64I Base Instruction Set\nInstructions inherited from RV32I\n";
val _ = test_RISCV.print_log true "\n";
(* Good presentation of RISC-V instructions at https://inst.eecs.berkeley.edu/~cs61c/sp19/lectures/lec05.pdf *)
(* 62 instructions in initial scope *)
(* 10 still TODO:
 *  2 fences
 *  environment call and breakpoint
 *  6 CSR instructions *)

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* Upon BILED_lifting_failed exception, debug from
 * exp_lift_fn in bir_inst_liftingLib *)

(* U-format *)
(* TODO: Integrate with assembler *)
  (* Load upper immediate - places imm value in top 20 bits of destination register, zeroing rest *)
  (* "lui x10, 0xDEAD" *)
  val res = riscv_test_hex "0DEAD537";

  (* Add upper immediate to PC - shifting immediate 12 bits to left, then adding address to this and
   * placing value in destination register *)
  (* "auipc x10, 0xDEAD" *)
  val res = riscv_test_hex "0DEAD517";

(* J-format *)
(* TODO: Integrate with assembler *)
  (* Jump and link *)
  (* "jal x1, 0x0" *)
  val res = riscv_test_hex "000000EF";

  (* Jump and link register *)
  (* "jalr x1, 0x0" *)
  val res = riscv_test_hex "000000E7";

(* B-format *)
  (* Immediate is signed value denoting multiples of two bytes (so 2 means 4 bytes)
   * which is added to the PC to give the target address. *)
  val _ = riscv_test_asms [
    (* Branch on equality of registers *)
    "beq x19, x10, 8",
    (* Branch on non-equality of registers *)
    "bne x19, x10, 8",
    (* Branch on less-than relation between registers *)
    "blt x19, x10, 8",
    (* Branch on greater-than-or-equal relation between registers *)
    "bge x19, x10, 8",
    (* Branch on unsigned less-than relation between registers *)
    "bltu x19, x10, 8",
    (* Branch on unsigned greater-than-or-equal relation between registers *)
    "bgeu x19, x10, 8"
  ];

(* I-type variant (opcode LOAD) *)
  val _ = riscv_test_asms [
    (* Load byte *)
    "lb x1,x2,-50",
    (* Load halfword *)
    "lh x1,x2,-50",
    (* Load word *)
    "lw x1,x2,-50",
    (* Load byte (unsigned) *)
    "lbu x1,x2,-50",
    (* Load halfword (unsigned) *)
    "lhu x1,x2,-50"
  ];

(* S-format *)
(* TODO: Integrate with assembler *)
  (* Store the byte (8 least significant bits) in x14 to the memory address in x2 with offset 8 *)
  (* "sb x14, 8(x2)" *)
  (* OK *)
  val res = riscv_test_hex "00E10423";

  (* Store the halfword (16 least significant bits) in x14 to the memory address in x2 with offset 8 *)
  (* "sh x14, 8(x2)" *)
  (* OK *)
  val res = riscv_test_hex "00E11423";

  (* Store the word (32 least significant bits) in x14 to the memory address in x2 with offset 8 *)
  (* "sw x14, 8(x2)" *)
  (* OK *)
  val res = riscv_test_hex "00E12423";

(* I-format (opcode OP-IMM) *)
  val _ = riscv_test_asms [
    (* Addition by constant *)
    "addi x15,x1,-50",
    (* Signed less-than comparison with constant *)
    "slti x15,x1,5",
    (* Unsigned less-than comparison with constant *)
    "sltiu x15,x1,5",
    (* Exclusive OR with constant *)
    "xori x15,x1,5",
    (* OR with constant *)
    "ori x15,x1,5",
    (* AND with constant *)
    "andi x15,x1,5",

    (* Note that these are the 64-bit variants of SLLI, SRLI and SRAI *)
    (* Logical left shift by constant *)
    "slli x15,x1,5",
    (* Logical right shift by constant *)
    "srli x15,x1,5",
    (* Arithmetic right shift by constant (note funky format of immediate) *)
    "srai x15,x1,1029"
  ];

(* R-format (opcode OP) *)
  val _ = riscv_test_asms [
    (* Addition *)
    "add x5, x6, x7",
    (* Subtraction *)
    (* TODO: Rewrite multiplication??? *)
    "sub x5, x6, x7",
    (* Logical left shift *)
    "sll x5, x6, x7",
    (* Signed comparison *)
    "slt x5, x6, x7",
    (* Unsigned comparison *)
    "sltu x5, x6, x7",
    (* Exclusive OR *)
    "xor x5, x6, x7",
    (* Logical right shift *)
    "srl x5, x6, x7",
    (* Arithmetic right shift *)
    "sra x5, x6, x7",
    (* OR *)
    "or x5, x6, x7",
    (* AND *)
    "and x5, x6, x7"
  ];

(* TODO: Fence instructions go here... *)
(* TODO: ECALL/EBREAK goes here... *)
(* TODO: CSR instructions go here... *)

val _ = test_RISCV.print_log true "\n";
val _ = test_RISCV.print_log_with_style test_RISCV.sty_HEADER true "Additions to RV32I\n";
val _ = test_RISCV.print_log true "\n";

(* I-type load variants *)
  val _ = riscv_test_asms [
    (* Load word (unsigned) *)
    "lwu x1,x2,-50",
    (* Load doubleword *)
    "ld x1,x2,-50"
  ];

(* S-format variants *)
  (* Store the doubleword (64 bits, the entire 64-bit register) in x14 to the memory address in x2 with offset 8 *)
  (* "sd x14, 8(x2)" *)
  (* OK *)
  val res = riscv_test_hex "00E13423";

(* I-type variant (opcode OP-IMM-32) *)
  val _ = riscv_test_asms [
    (* Addition by constant (32-bit) *)
    "addiw x15,x1,-50",
    (* Logical left shift by constant (32-bit) *)
    "slliw x15,x1,5",
    (* Logical right shift by constant (32-bit) *)
    "srliw x15,x1,5",
    (* Arithmetic right shift by constant (note funky format of immediate) (32-bit) *)
    "sraiw x15,x1,1029"
  ];

(* R-type variants (opcode OP-32) *)
  val _ = riscv_test_asms [
    (* Addition (32-bit) *)
    "addw x5, x6, x7",
    (* Subtraction (32-bit) *)
    "subw x5, x6, x7",
    (* Logical left shift (32-bit) *)
    "sllw x5, x6, x7",
    (* Logical right shift (32-bit) *)
    "srlw x5, x6, x7",
    (* Arithmetic right shift (32-bit) *)
    "sraw x5, x6, x7"
  ];

(* TODO: M extension (R-type instructions)

   ("MUL",    "FFFFFFT__________FFF_____FTTFFTT"),
   ("MULH",   "FFFFFFT__________FFT_____FTTFFTT"),
   ("MULHSU", "FFFFFFT__________FTF_____FTTFFTT"),
   ("MULHU",  "FFFFFFT__________FTT_____FTTFFTT"),
   ("DIV",    "FFFFFFT__________TFF_____FTTFFTT"),
   ("DIVU",   "FFFFFFT__________TFT_____FTTFFTT"),
   ("REM",    "FFFFFFT__________TTF_____FTTFFTT"),
   ("REMU",   "FFFFFFT__________TTT_____FTTFFTT"),
   ("MULW",   "FFFFFFT__________FFF_____FTTTFTT"),
   ("DIVW",   "FFFFFFT__________TFF_____FTTTFTT"),
   ("DIVUW",  "FFFFFFT__________TFT_____FTTTFTT"),
   ("REMW",   "FFFFFFT__________TTF_____FTTTFTT"),
   ("REMUW",  "FFFFFFT__________TTT_____FTTTFTT"),

*)

(* Unknown format *)
(* TODO: FENCE, FENCE.I (memory-ordering instructions + instruction fetch fence, exists in current L3 version but not in stepLib) *)
(* TODO: ECALL, EBREAK (environment call and breakpoints, exists in current L3 version but not in stepLib) *)
(* TODO: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI (CSR instructions, exists in current L3 version but not in stepLib) *)
(* TODO: Instructions from privileged instruction set: MRET (exists in latest L3 version), SRET (S ext., exists in latest L3 version), URET (N ext., exists in latest L3 version) *)
(* TODO: Most important extensions: A, M (exists in riscv_stepLib), C *)

(* TODO: Are NOPs in riscv_stepLib for real? *)
(* TODO: Take second look at stepLib code for Sail model (test.sml) *)
