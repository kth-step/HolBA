open HolKernel Parse
open testutils
open bir_inst_liftingLib;
open PPBackEnd
open riscv_assemblerLib;
open selftestLib;
open selftest_styleLib;

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
fun riscv_test_hex_mc hex = test_RISCV.lift_instr_mc mu_b mu_e pc hex NONE

fun riscv_test_hex_print_asm_gen is_multicore asm hex = 
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    if is_multicore
    then riscv_test_hex_mc hex
    else riscv_test_hex hex
  end
;
val riscv_test_hex_print_asm = 
  riscv_test_hex_print_asm_gen false
;
val riscv_test_hex_print_asm_mc = 
  riscv_test_hex_print_asm_gen true
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
    (* For offset zero ("LW x1,x2,0"):
       Hex : 00012083 
       Bin : 000000000000 00010 010 00001  0000011

       riscv_test_hex "00012083";

     *)
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
  (* For offset zero ("SW x14,x2"):
     Hex : 00E12023 
     Bin : 0000000 01110 00010 010 00000 0100011

     riscv_test_hex "00E12023";

   *)
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
(* NOTE: This uses the Multicore extension *)
(*   0000  0011  0011   00010  000  00001  0001111

val _ = fail_with_msg "FENCE not yet supported by stepLib";

val _ = riscv_test_hex_mc "0331008F";
val fence_res = riscv_test_hex_mc "0331008F";
*)
val _ = riscv_test_hex_print_asm_mc "FENCE x1, x2, rw, rw" "0331008F";

(*   1000  0011  0011   00010  000  00001  0001111

val _ = riscv_test_hex_mc "8331008F";
val fence_res = riscv_test_hex_mc "8331008F";
*)
val _ = riscv_test_hex_print_asm_mc "FENCE.TSO" "8331008F";

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
    (* For offset zero ("LD x1,x2,0"):
       Hex : 00013083 
       Bin : 000000000000 00010 011 00001  0000011

       riscv_test_hex "00013083";

     *)
    "LD x1,x2,-50"
  ];

(* S-format variants *)
  (* Store the doubleword (64 bits, the entire 64-bit register)
   * in x14 to the memory address in x2 with offset 8 *)
  (* For offset zero ("SD x14,x2"):
     Hex : 00E13023 
     Bin : 0000000 01110 00010 010 00000 0100011

     riscv_test_hex "00E12023";

   *)
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

val _ = riscv_test_hex_print_asm_mc "FENCE.I x0, x0, 0" "0000100F";

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

val _ = print_msg "\n";
val _ = print_header "RV32A Standard Extension\n";
val _ = print_msg "\n";

(* TODO: LR/SC *)
(* TODO: Unsure about ASM representation *)
(* Binary: 00010 0 0 00000 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "100120AF";

   x1 is "dest" (in rd position): the register which the loaded
     value is stored to.
   (x2) is "addr" (in rs1 position): register with address to load
     from.
*)
val _ = riscv_test_hex_print_asm_mc "LR.W x1, (x2)" "100120AF";
(* Binary: 00011 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "180120AF";

   x1 is "dest": upon success, a non-zero code is written
   to this register, upon failure, zero.
   (x2) is "addr" (in rs1 position): register with address to store
     to.
   x3 is "src" (in rs2 position): register with value to store.
*)
val _ = riscv_test_hex_print_asm_mc "SC.W x1, x3, (x2)" "180120AF";

(* Binary: 00001 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "083120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOSWAP.W x1, x3, (x2)" "083120AF";
(* Binary: 00000 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "003120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOADD.W x1, x3, (x2)" "003120AF";
(* Binary: 00100 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "203120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOXOR.W x1, x3, (x2)" "203120AF";
(* Binary: 01100 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "603120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOAND.W x1, x3, (x2)" "603120AF";
(* Binary: 01000 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "403120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOOR.W x1, x3, (x2)" "403120AF";
(* Binary: 10000 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "803120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMIN.W x1, x3, (x2)" "803120AF";
(* Binary: 10100 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "A03120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMAX.W x1, x3, (x2)" "A03120AF";
(* Binary: 11000 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "C03120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMINU.W x1, x3, (x2)" "C03120AF";
(* Binary: 11100 0 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "E03120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMAXU.W x1, x3, (x2)" "E03120AF";

(* aq/rl flags *)
(* Binary: 01000 1 0 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "443120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOOR.W.aq x1, x3, (x2)" "443120AF";
(* Binary: 00001 0 1 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "0A3120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOSWAP.W.rl x1, x3, (x2)" "0A3120AF";
(* Binary: 00001 1 1 00011 00010 010 00001 0101111
val amo_res = riscv_test_hex_mc "0E3120AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOSWAP.W.aq.rl x1, x3, (x2)" "0E3120AF";

val _ = print_msg "\n";
val _ = print_header "RV64A Standard Extension (instructions added to RV64A)\n";
val _ = print_msg "\n";

(* TODO: LR/SC *)
(* TODO: Unsure about ASM representation *)
(* Binary: 00010 0 0 00000 00010 011 00001 0101111 *)
val _ = riscv_test_hex_print_asm_mc "LR.D x1, (x2)" "100130AF";
(* Binary: 00011 0 0 00011 00010 011 00001 0101111 *)
val _ = riscv_test_hex_print_asm_mc "SC.D x1, x3, (x2)" "180130AF";

(* Binary: 00001 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "083130AF";
val amo_res = riscv_test_hex_mc "083130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOSWAP.D x1, x3, (x2)" "083130AF";
(* Binary: 00000 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "003130AF";
val amo_res = riscv_test_hex_mc "003130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOADD.D x1, x3, (x2)" "003130AF";
(* Binary: 00100 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "203130AF";
val amo_res = riscv_test_hex_mc "203130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOXOR.D x1, x3, (x2)" "203130AF";
(* Binary: 01100 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "603130AF";
val amo_res = riscv_test_hex_mc "603130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOAND.D x1, x3, (x2)" "603130AF";
(* Binary: 01000 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "403130AF";
val amo_res = riscv_test_hex_mc "403130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOOR.D x1, x3, (x2)" "403130AF";
(* Binary: 10000 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "803130AF";
val amo_res = riscv_test_hex_mc "803130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMIN.D x1, x3, (x2)" "803130AF";
(* Binary: 10100 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "A03130AF";
val amo_res = riscv_test_hex_mc "A03130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMAX.D x1, x3, (x2)" "A03130AF";
(* Binary: 11000 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "C03130AF";
val amo_res = riscv_test_hex_mc "C03130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMINU.D x1, x3, (x2)" "C03130AF";
(* Binary: 11100 0 0 00011 00010 011 00001 0101111

val _ = riscv_test_hex_mc "E03130AF";
val amo_res = riscv_test_hex_mc "E03130AF";
*)
val _ = riscv_test_hex_print_asm_mc "AMOMAXU.D x1, x3, (x2)" "E03130AF";

val riscv_expected_failed_hexcodes:string list =
[
   (* Base *)
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
