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

(******************************)
(* Shorthands from test_RISCV *)
(******************************)
fun print_msg msg = test_RISCV.print_log true msg;
fun print_header header = test_RISCV.print_log_with_style sty_HEADER true header;
fun fail_with_msg msg =
  let
    val _ = test_RISCV.print_log true (msg^" - ");
    val _ = test_RISCV.print_log_with_style sty_FAIL true "FAILED\n";
  in
    ()
  end
;

fun riscv_test_hex hex = test_RISCV.lift_instr mu_b mu_e pc hex NONE

fun riscv_test_hex_print_asm asm hex = 
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    test_RISCV.lift_instr mu_b mu_e pc hex NONE
  end
;

fun riscv_test_asm asm =
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    riscv_test_hex (riscv_hex_from_asm asm)
  end
;
val riscv_test_asms = map riscv_test_asm

(*********)
(* Tests *)
(*********)
val _ = print_msg "\n";
val _ = print_header "MANUAL TESTS (HEX) - RISC-V\nRV64I Base Instruction Set (instructions inherited from RV32I)\n";
val _ = print_msg "\n";
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
  (* Load upper immediate - places imm value in top 20 bits of
   * destination register, zeroing rest *)
  val _ = riscv_test_hex_print_asm "LUI x10, 0xDEAD" "0DEAD537";

  (* Add upper immediate to PC - shifting immediate 12 bits to left,
   * then adding address to this and placing value in destination register *)
  val _ = riscv_test_hex_print_asm "AUIPC x10, 0xDEAD" "0DEAD517";

(* J-format *)
(* TODO: Integrate with assembler *)
  (* Jump and link *)
  val _ = riscv_test_hex_print_asm "JAL x1, 0x0" "000000EF";

  (* Jump and link register *)
  val _ = riscv_test_hex_print_asm "JALR x1, 0x0" "000000E7";

(* B-format *)
  (* Immediate is signed value denoting multiples of two bytes (so 2 means 4 bytes)
   * which is added to the PC to give the target address. *)
  val _ = riscv_test_asms [
    (* Branch on equality of registers *)
    "BEQ x19, x10, 8",
    (* Branch on non-equality of registers *)
    "BNE x19, x10, 8",
    (* Branch on less-than relation between registers *)
    "BLT x19, x10, 8",
    (* Branch on greater-than-or-equal relation between registers *)
    "BGE x19, x10, 8",
    (* Branch on unsigned less-than relation between registers *)
    "BLTU x19, x10, 8",
    (* Branch on unsigned greater-than-or-equal relation between registers *)
    "BGEU x19, x10, 8"
  ];

(* I-type variant (opcode LOAD) *)
  val _ = riscv_test_asms [
    (* Load byte *)
    "LB x1,x2,-50",
    (* Load halfword *)
    "LH x1,x2,-50",
    (* Load word *)
    "LW x1,x2,-50",
    (* Load byte (unsigned) *)
    "LBU x1,x2,-50",
    (* Load halfword (unsigned) *)
    "LHU x1,x2,-50"
  ];

(* S-format *)
(* TODO: Integrate with assembler *)
  (* Store the byte (8 least significant bits) in x14 to the
   * memory address in x2 with offset 8 *)
  val _ = riscv_test_hex_print_asm "SB x14, 8(x2)" "00E10423";

  (* Store the halfword (16 least significant bits) in x14 to the
   * memory address in x2 with offset 8 *)
  val _ = riscv_test_hex_print_asm "SH x14, 8(x2)" "00E11423";

  (* Store the word (32 least significant bits) in x14 to the
   * memory address in x2 with offset 8 *)
  val _ = riscv_test_hex_print_asm "SW x14, 8(x2)" "00E12423";

(* I-format (opcode OP-IMM) *)
  val _ = riscv_test_asms [
    (* Addition by constant *)
    "ADDI x15,x1,-50",
    (* Signed less-than comparison with constant *)
    "SLTI x15,x1,5",
    (* Unsigned less-than comparison with constant *)
    "SLTIU x15,x1,5",
    (* Exclusive OR with constant *)
    "XORI x15,x1,5",
    (* OR with constant *)
    "ORI x15,x1,5",
    (* AND with constant *)
    "ANDI x15,x1,5",

    (* Note that these are the 64-bit variants of SLLI, SRLI and SRAI *)
    (* Logical left shift by constant *)
    "SLLI x15,x1,5",
    (* Logical right shift by constant *)
    "SRLI x15,x1,5",
    (* Arithmetic right shift by constant (note funky format of immediate) *)
    "SRAI x15,x1,1029"
  ];

(* R-format (opcode OP) *)
  val _ = riscv_test_asms [
    (* Addition *)
    "ADD x5, x6, x7",
    (* Subtraction *)
    (* TODO: Rewrite multiplication??? *)
    "SUB x5, x6, x7",
    (* Logical left shift *)
    "SLL x5, x6, x7",
    (* Signed comparison *)
    "SLT x5, x6, x7",
    (* Unsigned comparison *)
    "SLTU x5, x6, x7",
    (* Exclusive OR *)
    "XOR x5, x6, x7",
    (* Logical right shift *)
    "SRL x5, x6, x7",
    (* Arithmetic right shift *)
    "SRA x5, x6, x7",
    (* OR *)
    "OR x5, x6, x7",
    (* AND *)
    "AND x5, x6, x7"
  ];

(* TODO: Fence instructions go here... *)
val _ = fail_with_msg "FENCE not yet supported by stepLib";
val _ = fail_with_msg "FENCE.I not yet supported by stepLib";
(* TODO: ECALL/EBREAK goes here... *)
val _ = fail_with_msg "ECALL not yet supported by stepLib";
val _ = fail_with_msg "EBREAK not yet supported by stepLib";
(* TODO: CSR instructions go here... *)
val _ = fail_with_msg "CSRRW not yet supported by stepLib";
val _ = fail_with_msg "CSRRS not yet supported by stepLib";
val _ = fail_with_msg "CSRRC not yet supported by stepLib";
val _ = fail_with_msg "CSRRWI not yet supported by stepLib";
val _ = fail_with_msg "CSRRSI not yet supported by stepLib";
val _ = fail_with_msg "CSRRCI not yet supported by stepLib";

val _ = print_msg "\n";
val _ = print_header "RV64I Base Instruction Set (instructions added to RV32I)\n";
val _ = print_msg "\n";

(* I-type load variants *)
  val _ = riscv_test_asms [
    (* Load word (unsigned) *)
    "LWU x1,x2,-50",
    (* Load doubleword *)
    "LD x1,x2,-50"
  ];

(* S-format variants *)
  (* Store the doubleword (64 bits, the entire 64-bit register)
   * in x14 to the memory address in x2 with offset 8 *)
  val _ = riscv_test_hex_print_asm "SD x14, 8(x2)" "00E13423";

(* I-type variant (opcode OP-IMM-32) *)
  val _ = riscv_test_asms [
    (* Addition by constant (32-bit) *)
    "ADDIW x15,x1,-50",
    (* Logical left shift by constant (32-bit) *)
    "SLLIW x15,x1,5",
    (* Logical right shift by constant (32-bit) *)
    "SRLIW x15,x1,5",
    (* Arithmetic right shift by constant (note funky format of immediate) (32-bit) *)
    "SRAIW x15,x1,1029"
  ];

(* R-type variants (opcode OP-32) *)
  val _ = riscv_test_asms [
    (* Addition (32-bit) *)
    "ADDW x5, x6, x7",
    (* Subtraction (32-bit) *)
    "SUBW x5, x6, x7",
    (* Logical left shift (32-bit) *)
    "SLLW x5, x6, x7",
    (* Logical right shift (32-bit) *)
    "SRLW x5, x6, x7",
    (* Arithmetic right shift (32-bit) *)
    "SRAW x5, x6, x7"
  ];

val _ = print_msg "\n";
val _ = print_header "RV64M Standard Extension (instructions inherited from RV32M)\n";
val _ = print_msg "\n";

(* TODO: Fix MULH, MULHSU, MULHU (64 MSBs of 128-bit word), REM (some kind of if-not statement) *)
(* R-type variants (opcode OP) *)
  val _ = riscv_test_asms [
    (* Multiplication *)
    "MUL x5, x6, x7",
    (* FAILED *)
    "MULH x5, x6, x7",
    (* FAILED *)
    "MULHSU x5, x6, x7",
    (* FAILED *)
    "MULHU x5, x6, x7",
    (*  *)
    "DIV x5, x6, x7",
    (*  *)
    "DIVU x5, x6, x7",
    (*  *)
    "REM x5, x6, x7",
    (*  *)
    "REMU x5, x6, x7"
  ];

(* TODO: Fix REMW (probably will fix itself when fixing REM)*)
(* R-type variants (opcode OP-32) *)
  val _ = riscv_test_asms [
    (* Multiplication (32-bit) *)
    "MULW x5, x6, x7",
    (*  *)
    "DIVW x5, x6, x7",
    (*  *)
    "DIVUW x5, x6, x7",
    (*  *)
    "REMW x5, x6, x7",
    (*  *)
    "REMUW x5, x6, x7"
  ];

(* TODO: Instructions from privileged instruction set: MRET (exists in latest L3 version), SRET (S ext., exists in latest L3 version), URET (N ext., exists in latest L3 version) *)
(* TODO: Most important extensions: A (atomics), C (compressed) *)

(* TODO: Are NOPs in riscv_stepLib correct? *)
(* TODO: Take second look at stepLib code for Sail model (test.sml) *)
