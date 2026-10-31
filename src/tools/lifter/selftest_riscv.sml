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
val _ = print_header "MANUAL TESTS (HEX) - RISC-V";
val _ = print_msg "\n";
val _ = print_header "RV64I Base Instruction Set (instructions inherited from RV32I)";
val _ = print_msg "\n\n";
(* Good presentation of RISC-V instructions at https://inst.eecs.berkeley.edu/~cs61c/sp19/lectures/lec05.pdf *)
(* 75 instructions in initial scope (including M extension) *)
(* TODO: SC.W and SC.D, whose result depends on the load reservation *)
(* TODO: Are NOPs in riscv_stepLib correct? *)
(* TODO: Take second look at stepLib code for Sail model (test.sml) *)

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* Upon BILED_lifting_failed exception, debug from
 * exp_lift_fn in bir_inst_liftingLib *)
(* When you get something like
 *
 *   lifting of ``ms.c_cycles ms.procID`` failed
 *
 * the step theorem depends on state that is not lifted (riscv_bmr in
 * bir_lifting_machinesScript.sml lists the lifted state). *)
(* Every instruction is lifted with the assertions of the M-mode contract
 * of the step theorems (see riscv_state_is_OK_def): priv = 3 (H1), no
 * locked PMP entry in pmpcfg0 and pmpcfg2 (H3), mstatus.MIE clear (H6),
 * and for loads, stores and AMOs mstatus.MPRV clear (H2), natural
 * alignment of the address (H5) and, for 8-byte accesses, PMP entries OFF
 * or NAPOT (H4). *)

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

(* ret instruction *)
  val _ = print_term (concl ((valOf o (fn (x,_,_) => x)) (riscv_test_hex_print_asm "ret" "00008067")));

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

  (* Usage of the zero register: ("SD x0, 0(x7)") *)
  val _ = riscv_test_hex_print_asm "SD x0, 0(x7)" "0003B023";

  (* Usage of the zero register: ("SW x0, 0(x7)") *)
  val _ = riscv_test_hex_print_asm "SW x0, 0(x7)" "0003A023";

  (* Usage of the zero register: ("SH x0, 0(x15)") *)
  val _ = riscv_test_hex_print_asm "SH x0, 0(x15)" "00079023";

  (* Usage of the zero register: ("SB x0, 0(x15)") *)
  val _ = riscv_test_hex_print_asm "SB x0, 0(x15)" "00078023";

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
*)
val _ = riscv_test_hex_print_asm "FENCE x1, x2, i, i" "0881008F";

(* Environment Call and Breakpoints (opcode SYSTEM): a trap to M-mode,
 * which sets mepc, mcause, mtval, mstatus and the privilege and jumps to
 * the base of mtvec *)
val _ = riscv_test_hex_print_asm "ECALL" "00000073";

val _ = riscv_test_hex_print_asm "EBREAK" "00100073";

val _ = print_msg "\n";
val _ = print_header "RV64I Base Instruction Set (instructions added to RV32I)";
val _ = print_msg "\n\n";

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
val _ = print_header "RV64 Zifencei Standard Extension";
val _ = print_msg "\n\n";

(* FENCE.I x0, x0, 0 :  000000000000   00000  001   00000  0001111 *)

val _ = riscv_test_hex_print_asm "FENCE.I x0, x0, 0" "0000100F";

val _ = print_msg "\n";
val _ = print_header "RV64 Zicsr Standard Extension";
val _ = print_msg "\n\n";

(* CSR instructions (opcode SYSTEM), in M-mode, as every instruction *)
(* CSRRW x1, mscratch(0x340), x2 : 001101000000    00010 001000011110011 *)
val _ = riscv_test_hex_print_asm "CSRRW x1, mscratch(0x340), x2" "340110F3";
val _ = riscv_test_hex_print_asm "CSRW mie(0x304), 0" "30405073";
val _ = riscv_test_hex_print_asm "CSRW mstatus(0x300), 0" "30005073";

(* CSRRS x1, mscratch(0x340), x2 : 001101000000    00010 010000011110011 *)
val _ = riscv_test_hex_print_asm "CSRRS x1, mscratch(0x340), x2" "340120F3";
(* CSRRC x1, mscratch(0x340), x2 : 001101000000    00010 011000011110011 *)
val _ = riscv_test_hex_print_asm "CSRRC x1, mscratch(0x340), x2" "340130F3";
(* CSRRWI x1, mscratch(0x340), 0x1 : 001101000000    00001 101 000011110011 *)
val _ = riscv_test_hex_print_asm "CSRRWI x1, mscratch(0x340), 0x1" "3400D0F3";
(* CSRRSI x1, mscratch(0x340), 0x1 : 001101000000    00001 110 00001 1110011 *)
val _ = riscv_test_hex_print_asm "CSRRSI x1, mscratch(0x340), 0x1" "3400E0F3";
(* CSRRCI x1, mscratch(0x340), 0x1 : 001101000000    00001 111 000011110011 *)
val _ = riscv_test_hex_print_asm "CSRRCI x1, mscratch(0x340), 0x1" "3400F0F3";

val _ = riscv_test_hex_print_asm "CSRR a2, mhartid(0xF14)" "F1402673";

val _ = riscv_test_hex_print_asm "CSRR a5, mepc(0x341)" "341027F3";

val _ = riscv_test_hex_print_asm "CSRR a5, mcause(0x342)" "342027F3";

val _ = riscv_test_hex_print_asm "CSRR a5, mtval(0x343)" "343027F3";

(* A read of mip: the stored SSIP, STIP and SEIP, MSIP and MTIP from the
 * CLINT in memory (msip and mtimecmp of the hart procID, and mtime), and
 * the external interrupt lines *)
val _ = riscv_test_hex_print_asm "CSRR a5, mip(0x344)" "344027F3";
(* Writes of mip store only SSIP, STIP and SEIP; CSRRS and CSRRC read SEIP
 * as stored, without the external line *)
val _ = riscv_test_hex_print_asm "CSRRW x1, mip(0x344), x2" "344110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, mip(0x344), x2" "344120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, mip(0x344), x2" "344130F3";

(* mcycle is not lifted: NextRISCV does not count cycles *)
val _ = riscv_test_hex_print_asm "CSRR a5, mcycle(0xB00)" "B00027F3";

(* The six forms of CSR instruction on CSRs that S3K writes, with rd = x1
 * and rs1 = x2 or an immediate *)
val _ = riscv_test_hex_print_asm "CSRRW x1, mstatus(0x300), x2" "300110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, mstatus(0x300), x2" "300120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, mstatus(0x300), x2" "300130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, mstatus(0x300), 0x8" "300450F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, mstatus(0x300), 0x8" "300460F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, mstatus(0x300), 0x8" "300470F3";
val _ = riscv_test_hex_print_asm "CSRRW x1, mtvec(0x305), x2" "305110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, mtvec(0x305), x2" "305120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, mtvec(0x305), x2" "305130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, mtvec(0x305), 0x1" "3050D0F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, mtvec(0x305), 0x1" "3050E0F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, mtvec(0x305), 0x1" "3050F0F3";
val _ = riscv_test_hex_print_asm "CSRRW x1, mie(0x304), x2" "304110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, mie(0x304), x2" "304120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, mie(0x304), x2" "304130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, mie(0x304), 0x8" "304450F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, mie(0x304), 0x8" "304460F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, mie(0x304), 0x8" "304470F3";
val _ = riscv_test_hex_print_asm "CSRRW x1, pmpcfg0(0x3A0), x2" "3A0110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, pmpcfg0(0x3A0), x2" "3A0120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, pmpcfg0(0x3A0), x2" "3A0130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, pmpcfg0(0x3A0), 0x1" "3A00D0F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, pmpcfg0(0x3A0), 0x1" "3A00E0F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, pmpcfg0(0x3A0), 0x1" "3A00F0F3";
val _ = riscv_test_hex_print_asm "CSRRW x1, pmpaddr0(0x3B0), x2" "3B0110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, pmpaddr0(0x3B0), x2" "3B0120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, pmpaddr0(0x3B0), x2" "3B0130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, pmpaddr0(0x3B0), 0x1" "3B00D0F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, pmpaddr0(0x3B0), 0x1" "3B00E0F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, pmpaddr0(0x3B0), 0x1" "3B00F0F3";
val _ = riscv_test_hex_print_asm "CSRRW x1, mcounteren(0x306), x2" "306110F3";
val _ = riscv_test_hex_print_asm "CSRRS x1, mcounteren(0x306), x2" "306120F3";
val _ = riscv_test_hex_print_asm "CSRRC x1, mcounteren(0x306), x2" "306130F3";
val _ = riscv_test_hex_print_asm "CSRRWI x1, mcounteren(0x306), 0x1" "3060D0F3";
val _ = riscv_test_hex_print_asm "CSRRSI x1, mcounteren(0x306), 0x1" "3060E0F3";
val _ = riscv_test_hex_print_asm "CSRRCI x1, mcounteren(0x306), 0x1" "3060F0F3";

(* Writes of misa, one that clears misa.C and one that sets it: no write of
 * misa lifts (see the RISC-V section of README) *)
val _ = riscv_test_hex_print_asm "CSRW misa(0x301), zero" "30101073";
val _ = riscv_test_hex_print_asm "CSRSI misa(0x301), 0x4" "30126073";

val _ = print_msg "\n";
val _ = print_header "RV64 Privileged Instructions (M-mode)";
val _ = print_msg "\n\n";

(* Return from a trap: the privilege becomes mstatus.MPP (U-mode for the
 * reserved encoding 2), MIE becomes MPIE, MPIE becomes 1, MPP becomes U,
 * MPRV is cleared unless MPP is M, and the block ends in a jump to mepc *)
val _ = riscv_test_hex_print_asm "MRET" "30200073";

(* Wait for interrupt: does nothing in the model *)
val _ = riscv_test_hex_print_asm "WFI" "10500073";

(* Fence for address translation: does nothing in M-mode *)
val _ = riscv_test_hex_print_asm "SFENCE.VMA x0, x0" "12000073";


val _ = print_msg "\n";
val _ = print_header "RV64M Standard Extension (instructions inherited from RV32M)";
val _ = print_msg "\n\n";

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
val _ = print_header "RV64M Standard Extension (instructions added to RV32M)";
val _ = print_msg "\n\n";

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

val _ = print_msg "\n";
val _ = print_header "RV64A Standard Extension";
val _ = print_msg "\n\n";

(* Atomic memory operations on words *)
val _ = riscv_test_hex_print_asm "AMOSWAP.W a0, a2, (a1)" "08C5A52F";
val _ = riscv_test_hex_print_asm "AMOADD.W a0, a2, (a1)" "00C5A52F";
val _ = riscv_test_hex_print_asm "AMOXOR.W a0, a2, (a1)" "20C5A52F";
val _ = riscv_test_hex_print_asm "AMOAND.W a0, a2, (a1)" "60C5A52F";
val _ = riscv_test_hex_print_asm "AMOOR.W a0, a2, (a1)" "40C5A52F";
val _ = riscv_test_hex_print_asm "AMOMIN.W a0, a2, (a1)" "80C5A52F";
val _ = riscv_test_hex_print_asm "AMOMAX.W a0, a2, (a1)" "A0C5A52F";
val _ = riscv_test_hex_print_asm "AMOMINU.W a0, a2, (a1)" "C0C5A52F";
val _ = riscv_test_hex_print_asm "AMOMAXU.W a0, a2, (a1)" "E0C5A52F";

(* Atomic memory operations on doublewords *)
val _ = riscv_test_hex_print_asm "AMOSWAP.D a0, a2, (a1)" "08C5B52F";
val _ = riscv_test_hex_print_asm "AMOADD.D a0, a2, (a1)" "00C5B52F";
val _ = riscv_test_hex_print_asm "AMOXOR.D a0, a2, (a1)" "20C5B52F";
val _ = riscv_test_hex_print_asm "AMOAND.D a0, a2, (a1)" "60C5B52F";
val _ = riscv_test_hex_print_asm "AMOOR.D a0, a2, (a1)" "40C5B52F";
val _ = riscv_test_hex_print_asm "AMOMIN.D a0, a2, (a1)" "80C5B52F";
val _ = riscv_test_hex_print_asm "AMOMAX.D a0, a2, (a1)" "A0C5B52F";
val _ = riscv_test_hex_print_asm "AMOMINU.D a0, a2, (a1)" "C0C5B52F";
val _ = riscv_test_hex_print_asm "AMOMAXU.D a0, a2, (a1)" "E0C5B52F";

(* Ordering bits, x0 as destination, and destination equal to a source *)
val _ = riscv_test_hex_print_asm "AMOSWAP.W.AQRL a0, a2, (a1)" "0EC5A52F";
val _ = riscv_test_hex_print_asm "AMOOR.W x0, a2, (a1)" "40C5A02F";
val _ = riscv_test_hex_print_asm "AMOSWAP.W a0, a0, (a1)" "08A5A52F";
val _ = riscv_test_hex_print_asm "AMOADD.D a1, a2, (a1)" "00C5B5AF";

(* Load-reserved and store-conditional *)
val _ = riscv_test_hex_print_asm "LR.W a0, (a1)" "1005A52F";
val _ = riscv_test_hex_print_asm "LR.D a0, (a1)" "1005B52F";
val _ = riscv_test_hex_print_asm "LR.W.AQ x0, (a1)" "1405A02F";
(* TODO: the result depends on the load reservation, which is not lifted *)
val _ = riscv_test_hex_print_asm "SC.W a0, a2, (a1)" "18C5A52F";
val _ = riscv_test_hex_print_asm "SC.D a0, a2, (a1)" "18C5B52F";

val _ = print_msg "\n";
val _ = print_header "RV64C Standard Extension (integer instructions)";
val _ = print_msg "\n\n";

(* 16-bit instructions.
 * Corresponding 32-bit instructions in comments. *)

(* Quadrant 0 *)
  (* addi a0, sp, 16 *)
  val _ = riscv_test_hex_print_asm "C.ADDI4SPN a0, sp, 16" "0808";
  (* lw a0, 4(a1) *)
  val _ = riscv_test_hex_print_asm "C.LW a0, 4(a1)" "41C8";
  (* ld a0, 8(a1) *)
  val _ = riscv_test_hex_print_asm "C.LD a0, 8(a1)" "6588";
  (* sw a0, 4(a1) *)
  val _ = riscv_test_hex_print_asm "C.SW a0, 4(a1)" "C1C8";
  (* sd a0, 8(a1) *)
  val _ = riscv_test_hex_print_asm "C.SD a0, 8(a1)" "E588";

(* Quadrant 1 *)
  (* addi x0, x0, 0 *)
  val _ = riscv_test_hex_print_asm "C.NOP" "0001";
  (* addi a0, a0, -5 *)
  val _ = riscv_test_hex_print_asm "C.ADDI a0, -5" "156D";
  (* addiw a0, a0, 3 *)
  val _ = riscv_test_hex_print_asm "C.ADDIW a0, 3" "250D";
  (* addi a0, x0, 0 *)
  val _ = riscv_test_hex_print_asm "C.LI a0, 0" "4501";
  (* addi sp, sp, -64 *)
  val _ = riscv_test_hex_print_asm "C.ADDI16SP sp, -64" "7139";
  (* lui a0, 0x1f *)
  val _ = riscv_test_hex_print_asm "C.LUI a0, 0x1f" "657D";
  (* srli a0, a0, 3 *)
  val _ = riscv_test_hex_print_asm "C.SRLI a0, 3" "810D";
  (* srai a0, a0, 3 *)
  val _ = riscv_test_hex_print_asm "C.SRAI a0, 3" "850D";
  (* andi a0, a0, -6 *)
  val _ = riscv_test_hex_print_asm "C.ANDI a0, -6" "9969";
  (* sub a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.SUB a0, a1" "8D0D";
  (* xor a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.XOR a0, a1" "8D2D";
  (* or a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.OR a0, a1" "8D4D";
  (* and a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.AND a0, a1" "8D6D";
  (* subw a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.SUBW a0, a1" "9D0D";
  (* addw a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.ADDW a0, a1" "9D2D";
  (* jal x0, 8 *)
  val _ = riscv_test_hex_print_asm "C.J 8" "A021";
  (* beq a0, x0, 8 *)
  val _ = riscv_test_hex_print_asm "C.BEQZ a0, 8" "C501";
  (* bne a0, x0, 8 *)
  val _ = riscv_test_hex_print_asm "C.BNEZ a0, 8" "E501";

(* Quadrant 2 *)
  (* slli a0, a0, 3 *)
  val _ = riscv_test_hex_print_asm "C.SLLI a0, 3" "050E";
  (* lw a0, 4(sp) *)
  val _ = riscv_test_hex_print_asm "C.LWSP a0, 4(sp)" "4512";
  (* ld a0, 8(sp) *)
  val _ = riscv_test_hex_print_asm "C.LDSP a0, 8(sp)" "6522";
  (* jalr x0, 0(ra), that is, ret *)
  val _ = riscv_test_hex_print_asm "C.JR ra" "8082";
  (* add a0, x0, a1 *)
  val _ = riscv_test_hex_print_asm "C.MV a0, a1" "852E";
  (* ebreak *)
  val _ = riscv_test_hex_print_asm "C.EBREAK" "9002";
  (* jalr ra, 0(a5) *)
  val _ = riscv_test_hex_print_asm "C.JALR a5" "9782";
  (* add a0, a0, a1 *)
  val _ = riscv_test_hex_print_asm "C.ADD a0, a1" "952E";
  (* sw a0, 4(sp) *)
  val _ = riscv_test_hex_print_asm "C.SWSP a0, 4(sp)" "C22A";
  (* sd a0, 8(sp) *)
  val _ = riscv_test_hex_print_asm "C.SDSP a0, 8(sp)" "E42A";


val riscv_expected_failed_hexcodes:string list =
[
   (* Zicsr *)
   "B00027F3" (* CSRR mcycle: c_cycles is not lifted *),
   (* writes of misa: the lifter cannot show riscv_state_is_OK after one, at
      any pc and whatever the written value *)
   "30101073" (* CSRW misa, zero *),
   "30126073" (* CSRSI misa, 0x4 *),
   (* A *)
   "18C5A52F" (* SC.W: depends on the load reservation, which is not lifted *),
   "18C5B52F" (* SC.D: likewise *)
];

val _ = test_RISCV.final_results "RISC-V" riscv_expected_failed_hexcodes;

val _ = test_RISCV.close_log();

(* check whether the result is different *)
val _ =
  if OS.Process.isSuccess (OS.Process.system ("git diff --exit-code selftest_riscv.log"))
  then ()
  else
    raise Fail ("selftest_riscv.sml::Output in selftest_riscv.log has diverged")
