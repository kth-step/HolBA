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
  val log_name = "selftest_riscv.log";
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
(* 75 instructions in initial scope (including M extension) *)
(* 10 still TODO:
 *  2 fences
 *  environment call and breakpoint
 *  6 CSR instructions *)
(* TODO: Instructions from privileged instruction set: MRET (exists in latest L3 version), SRET (S ext., exists in latest L3 version), URET (N ext., exists in latest L3 version) *)
(* TODO: Most important extensions: A (atomics), C (compressed) *)
(* TODO: Are NOPs in riscv_stepLib correct? *)
(* TODO: Take second look at stepLib code for Sail model (test.sml) *)

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* Upon BILED_lifting_failed exception, debug from
 * exp_lift_fn in bir_inst_liftingLib *)
(* When you get something like
 *
 *   lifting of ``(ms.c_MCSR ms.procID).mstatus.MPRV = 3w`` failed
 *
 * you must lift more registers (mstatus in this case). *)

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

(* Memory ordering isntructions (opcode MISC-MEM) *)
(*   0000  1000  1000   00010  000  00001  0001111

Not sure about asm formatting...
val _ = fail_with_msg "FENCE not yet supported by stepLib";
*)
val _ = riscv_test_hex_print_asm "FENCE x1, x2, i, i" "0881008F";

(* Environment Call and Breakpoints (opcode SYSTEM) *)
(*

  open riscv_stepLib;
  val _ = riscv_step_hex "00000073";

val _ = fail_with_msg "ECALL not yet supported by stepLib";
*)
val _ = riscv_test_hex_print_asm "ECALL" "00000073";

(* 

  open riscv_stepLib;
  val _ = riscv_step_hex "00100073";

val _ = fail_with_msg "EBREAK not yet supported by stepLib";
*)
val _ = riscv_test_hex_print_asm "EBREAK" "00100073";

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
val _ = print_header "RV64 Zifencei Standard Extension\n";
val _ = print_msg "\n";

(* FENCE.I x0, x0, 0 :  000000000000   00000  001   00000  0001111

  open riscv_stepLib;
  val _ = riscv_step_hex "0000100F";

val _ = fail_with_msg "FENCE.I not yet supported by stepLib";
*)

val _ = riscv_test_hex_print_asm "FENCE.I x0, x0, 0" "0000100F";

val _ = print_msg "\n";
val _ = print_header "RV64 Zicsr Standard Extension\n";
val _ = print_msg "\n";

(* CSR instructions (opcode SYSTEM) *)
(* TODO: Note that machine mode is currently assumed for these instructions
 * (see bottom of riscv_stepScript.sml) *)
(* CSRRW x1, mscratch(0x340), x2 : 001101000000    00010 001000011110011

  open riscv_stepLib;
  val _ = riscv_step_hex "340110F3";

*)
val _ = riscv_test_hex_print_asm "CSRRW x1, mscratch(0x340), x2" "340110F3";
(* CSRRS x1, mscratch(0x340), x2 : 001101000000    00010 010000011110011

  open riscv_stepLib;
  val test = riscv_step_hex "340120F3";

*)
val _ = riscv_test_hex_print_asm "CSRRS x1, mscratch(0x340), x2" "340120F3";
(* CSRRC x1, mscratch(0x340), x2 : 001101000000    00010 011000011110011

  open riscv_stepLib;
  val test = riscv_step_hex "340130F3";

*)
val _ = riscv_test_hex_print_asm "CSRRC x1, mscratch(0x340), x2" "340130F3";
(* CSRRWI x1, mscratch(0x340), 0x1 : 001101000000    00001 101 000011110011

  open riscv_stepLib;
  val _ = riscv_step_hex "3400D0F3";

*)
val _ = riscv_test_hex_print_asm "CSRRWI x1, mscratch(0x340), 0x1" "3400D0F3";
(* CSRRSI x1, mscratch(0x340), 0x1 : 001101000000    00001 110 00001 1110011

  open riscv_stepLib;
  val test = riscv_step_hex "3400E0F3";

*)
val _ = riscv_test_hex_print_asm "CSRRSI x1, mscratch(0x340), 0x1" "3400E0F3";
(* CSRRCI x1, mscratch(0x340), 0x1 : 001101000000    00001 111 000011110011

  open riscv_stepLib;
  val test = riscv_step_hex "3400F0F3";

*)
val _ = riscv_test_hex_print_asm "CSRRCI x1, mscratch(0x340), 0x1" "3400F0F3";

val _ = print_msg "\n";
val _ = print_header "RV64M Standard Extension (instructions inherited from RV32M)\n";
val _ = print_msg "\n";

(* R-type variants (opcode OP) *)
  val _ = riscv_test_asms [
    (* Multiplication *)
    "MUL x5, x6, x7",
    (*  *)
    "MULH x5, x6, x7",
    (*  *)
    "MULHSU x5, x6, x7",
    (*  *)
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

val _ = print_msg "\n";
val _ = print_header "RV64M Standard Extension (instructions added to RV32M)\n";
val _ = print_msg "\n";

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


val riscv_expected_failed_hexcodes:string list =
[
   (* Base *)
   "0881008F" (* FENCE x1, x2, i, i *),
   "00000073" (* ECALL *),
   "00100073" (* EBREAK *),
   (* Zifencei *)
   "0000100F" (* FENCE.I *),
   (* Zicsr *)
   "340110F3" (* CSRRW x1, mscratch(0x340), x2 *),
   "340120F3" (* CSRRS x1, mscratch(0x340), x2 *),
   "340130F3" (* CSRRC x1, mscratch(0x340), x2 *),
   "3400D0F3" (* CSRRWI x1, mscratch(0x340), 0x1 *),
   "3400E0F3" (* CSRRWI x1, mscratch(0x340), 0x1 *),
   "3400F0F3" (* CSRRCI x1, mscratch(0x340), 0x1 *)
];

val _ = test_RISCV.final_results "RISC-V" riscv_expected_failed_hexcodes;

val _ = test_RISCV.close_log();

(* check whether the result is different *)
val _ =
  if OS.Process.isSuccess (OS.Process.system ("git diff --exit-code selftest_riscv.log"))
  then ()
  else
    raise Fail ("selftest_riscv.sml::Output in selftest_riscv.log has diverged")
