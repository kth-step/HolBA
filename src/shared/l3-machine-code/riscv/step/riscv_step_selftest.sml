(* ------------------------------------------------------------------------
   Selftest of riscv_stepLib, run by Holmake when HOLSELFTESTLEVEL is set.

   riscv_step_hex is run on one encoding of every riscv_dict entry (for the
   floating-point instructions with a rounding-mode field, one with a
   static mode and one with the dynamic one, and for the exact conversions
   also one with RMM; for the CSR instructions, one for each CSR that the
   step theorems must cover), on a read and two writes of every CSR of the
   hart and of some addresses that are not CSRs, on every instruction of the
   programs in ../sim/tests, and on some edge cases.  Each theorem must be

     hyps |- NextRISCV s = SOME s'

   with s' a record update of s, and with hyps exactly the hypotheses that
   the M-mode contract of riscv_stepTheory (doc/design-privileged.md §1.5)
   allows for the instruction:

     H1        s.c_privilege s.procID = 3w                    always
     H2        ~(s.c_MCSR s.procID).mstatus.MPRV              data accesses
     H3        pmpcfg0/2 && 0x8080808080808080w = 0w          always
     H4        ((pmpcfg0/2 >>> 1) ?? pmpcfg0/2) &&
               0x0808080808080808w = 0w                       8-byte accesses
     H5        aligned k (address), k = log2 width            accesses of 2,
                                                              4 and 8 bytes
     H6        ~(s.c_MCSR s.procID).mstatus.MIE               always

   and, as before the priv-1.13 model, the preconditions of NextRISCV
   (exception and NextFetch), the fetch (pc alignment and the instruction
   bytes), and the conditions under which the instruction is legal: misa.C
   for a compressed instruction, misa.C or a 4-byte aligned target for a
   jump or branch, misa.MXL <> 1w for the RV64-only instructions,
   mstatus.FS <> 0w for the F and D instructions and for the CSR
   instructions on fflags, frm and fcsr, and for those with the
   dynamic rounding mode fcsr.frm in RNE, RTZ, RDN or RUP (fcsr.frm <+ 5w,
   which adds RMM, for the exact conversions FCVT.D.W, FCVT.D.WU and
   FCVT.D.S).  The address in H5, and the target in the jump condition,
   must be those of the decoded instruction: an H5 hypothesis must be
   equivalent to the alignment of rs1 + offs (of rs1 for an AMO, LR or SC),
   and a target hypothesis to bit 1 of pc + offs (of rs1 + offs with bit 0
   cleared for JALR); both are decided by bit-blasting.  An address or
   target given by x0 and an offset is a constant, which riscv_step decides:
   no hypothesis is left for it.

   These categories (the table exact below and the patterns that follow
   it) are exhaustive: any other hypothesis is UNEXPECTED, and fails the
   test.  So there is none on satp: address translation is off in M-mode,
   and the contract needs no hypothesis on it (doc/design-smode.md §1.1,
   §1.8).  Nor may any hypothesis mention c_SCSR, and a conclusion may
   mention it only for a CSR instruction on one of the S-mode CSRs stored
   there (stvec, scounteren, senvcfg, sscratch, sepc, scause, stval and
   satp), whose value it reads or writes.

   No model function may be left in the conclusion (bad_consts: address
   translation and the PMP check; for the CSR instructions, the read and
   write of the CSR, its legalisation and the access checks; for ECALL,
   EBREAK and MRET, the trap entry and the return).  For the edge cases,
   which include ECALL, EBREAK, MRET, WFI, SFENCE.VMA and CSR instructions
   on the CSRs whose values are legalised (satp and the sstatus view of
   mstatus among them), fields of the state after the step are checked
   against their values as doc/design-privileged.md and
   doc/design-smode.md give them (field checks).

   Encodings that cannot step must make riscv_step_hex fail: reserved
   encodings, which are illegal; SRET, which returns to S-mode or U-mode;
   a CSR instruction on an address that is not a CSR, or that writes a
   read-only CSR, which is illegal (decided here from the CSR table of
   doc/design-privileged.md, independently of the step library); rm = 5 or
   6 (reserved), and rm = 4 (RMM, which L3 does not implement) for an
   instruction that rounds; and a misaligned constant address.  ECALL,
   EBREAK and MRET step: their theorems take the trap to M-mode
   (riscv_stepTheory.NextRISCV_trap) or return from it (NextRISCV_mret).
   The test fails if any check fails.
   ------------------------------------------------------------------------ *)

val () = Feedback.emit_MESG := false;
val () = Feedback.emit_WARNING := false;

load "riscv_stepLib" handle _ => OS.Process.exit OS.Process.failure;
load "blastLib" handle _ => OS.Process.exit OS.Process.failure;

(* Set only at the end of a run without failures: a compile error or an
   exception in the code below makes the test fail too. *)
val selftest_passed = ref false;

local
open HolKernel boolLib bossLib riscv_stepLib

(* ------------------------------------------------------------------------
   Decoding
   ------------------------------------------------------------------------ *)

fun hex_int h = Option.valOf (StringCvt.scanString (Int.scan StringCvt.HEX) h)

fun is_compressed h = String.size h <= 4

(* bits 14:12, the rm field of an F or D instruction *)
fun rm_of h = (hex_int h div 4096) mod 8

(* (outer constructor, instruction name, arguments) of the decoded
   instruction, e.g. ("Load", "LW", [rd, rs1, offs]) *)
fun decoded h =
  let
    val ast = utilsLib.rhsc (riscv_decode_hex h)
    val (c, args) = boolSyntax.strip_comb ast
    val outer = fst (Term.dest_const c)
  in
    case args of
       [a] =>
         let
           val (c', args') = boolSyntax.strip_comb a
         in
           if Term.is_const c' andalso not (pairSyntax.is_pair a) then
             (outer, fst (Term.dest_const c'),
              List.concat (List.map pairSyntax.strip_pair args'))
           else (outer, outer, pairSyntax.strip_pair a)
         end
     | _ => (outer, outer, args)
  end

fun name_of (_, inner, _) = inner

fun closed_value tm = utilsLib.rhsc (EVAL tm)
fun is_zero_reg r = Teq (closed_value ``^r = 0w : word5``)

(* ------------------------------------------------------------------------
   Allowed hypotheses
   ------------------------------------------------------------------------ *)

val s = ``s:riscv_state``
val mcsr = ``^s.c_MCSR ^s.procID``
val rvc = ``^mcsr.misa.C``
fun conjs th = boolSyntax.strip_conj (utilsLib.rhsc (Thm.SPEC mcsr th))
val (h3a, h3b) =
  case conjs riscv_stepTheory.pmp_unlocked_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_unlocked_def"
val (h4a, h4b) =
  case conjs riscv_stepTheory.pmp_off_or_napot_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_off_or_napot_def"

val exact =
  [("H1", ``^s.c_privilege ^s.procID = 3w``),
   ("H2", ``~^mcsr.mstatus.MPRV``),
   ("H3.pmpcfg0", h3a), ("H3.pmpcfg2", h3b),
   ("H4.pmpcfg0", h4a), ("H4.pmpcfg2", h4b),
   ("H6", ``~^mcsr.mstatus.MIE``),
   ("exception", ``^s.exception = NoException``),
   ("NextFetch", ``^s.c_NextFetch ^s.procID = NONE``),
   ("pc<0>", ``~word_bit 0 (^s.c_PC ^s.procID)``),
   ("pc<1>|C", ``~word_bit 1 (^s.c_PC ^s.procID) \/ ^rvc``),
   ("C", rvc),
   ("RV64", ``^mcsr.misa.MXL <> 1w``),
   ("FS", ``^mcsr.mstatus.FS <> 0w``),
   ("frm", ``~word_bit 2 (^s.c_UCSR ^s.procID).fpcsr.FRM``),
   ("frm<5", ``(^s.c_UCSR ^s.procID).fpcsr.FRM <+ 5w``)]

val mem_pat0 = ``^s.MEM8 (^s.c_PC ^s.procID) = v2w (l: bool list)``
val mem_pat = ``^s.MEM8 (^s.c_PC ^s.procID + k) = v2w (l: bool list)``
val aligned_pat = ``aligned n (a: word64)``
val target_pat = ``~word_bit 1 (a: word64) \/ ^rvc``

(* the data address of a load, store, AMO, LR or SC, if it is not given by
   x0, which makes it a constant *)
fun data_address (outer, inner, args) =
  let
    val gpr = fn r => ``^s.c_gpr ^s.procID ^r``
    val base_offs =
      case (outer, args) of
         ("Load", [_, rs1, offs]) => SOME (rs1, SOME offs)
       | ("FPLoad", [_, rs1, offs]) => SOME (rs1, SOME offs)
       | ("Store", [rs1, _, offs]) => SOME (rs1, SOME offs)
       | ("FPStore", [rs1, _, offs]) => SOME (rs1, SOME offs)
       | ("AMO", _ :: _ :: _ :: rs1 :: _) => SOME (rs1, NONE)
       | _ => NONE
  in
    case base_offs of
       NONE => NONE
     | SOME (rs1, offs) =>
         if is_zero_reg rs1 then NONE
         else
           SOME (case offs of
                    SOME offs =>
                      ``^(gpr rs1) + sw2sw (^offs : word12) : word64``
                  | NONE => gpr rs1)
  end

(* the target of a 32-bit jump or branch, if it is not a constant *)
fun jump_target (outer, inner, args) =
  case (inner, args) of
     ("JAL", [_, imm]) =>
       SOME ``^s.c_PC ^s.procID + sw2sw (^imm : word20) << 1``
   | ("JALR", [_, rs1, imm]) =>
       if is_zero_reg rs1 then NONE
       else
         SOME ``(^s.c_gpr ^s.procID ^rs1 + sw2sw (^imm : word12)) &&
                0xFFFFFFFFFFFFFFFEw : word64``
   | (_, [_, _, offs]) =>
       if outer = "Branch" then
         SOME ``^s.c_PC ^s.procID + sw2sw (^offs : word12) << 1``
       else NONE
   | _ => NONE

(* JALR from x0 to a target with bit 1 set: legal only with misa.C *)
fun constant_target_bit1 (_, inner, args) =
  case (inner, args) of
     ("JALR", [_, rs1, imm]) =>
       is_zero_reg rs1 andalso
       Teq (closed_value
              ``word_bit 1 (sw2sw (^imm : word12) &&
                            0xFFFFFFFFFFFFFFFEw : word64)``)
   | _ => false

(* a <=> b, by bit-blasting (atoms such as s.c_gpr s.procID r are kept) *)
local
  val conv =
    Conv.QCONV
      (REWRITE_CONV [alignmentTheory.aligned_extract]
       THENC numLib.REDUCE_CONV
       THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
in
  fun equivalent a b =
    Lib.can (fn tm => blastLib.BBLAST_PROVE (utilsLib.rhsc (conv tm)))
      (boolSyntax.mk_eq (a, b))
end

fun category inst h =
  case List.find (fn (_, t) => Term.aconv t h) exact of
     SOME (c, _) => c
   | NONE =>
       if Lib.can (Term.match_term mem_pat0) h orelse
          Lib.can (Term.match_term mem_pat) h
         then "mem"
       else case Lib.total (Term.match_term aligned_pat) h of
          SOME (sub, _) =>
            let
              val n = Term.subst sub ``n:num``
            in
              case data_address inst of
                 SOME a =>
                   if equivalent h ``aligned ^n ^a``
                     then "H5." ^ Parse.term_to_string n
                   else "UNEXPECTED (not the address of the instruction): " ^
                        Parse.term_to_string h
               | NONE => "UNEXPECTED: " ^ Parse.term_to_string h
            end
        | NONE =>
            if Lib.can (Term.match_term target_pat) h then
              case jump_target inst of
                 SOME t =>
                   if equivalent h ``~word_bit 1 ^t \/ ^rvc``
                     then "target<1>|C"
                   else "UNEXPECTED (not the target of the instruction): " ^
                        Parse.term_to_string h
               | NONE => "UNEXPECTED: " ^ Parse.term_to_string h
            else "UNEXPECTED: " ^ Parse.term_to_string h

(* ------------------------------------------------------------------------
   What each instruction needs
   ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------
   CSR instructions

   Whether a CSR instruction is legal in M-mode, decided here independently
   of the step library, from the CSR table of doc/design-privileged.md
   §3.6.1 (114 addresses) and the rules of §3.2: the CSR must exist, and a
   write (CSRRW and CSRRWI always, the others when their rs1 or uimm field
   is not 0) must not be to a read-only CSR (bits 11:10 of the number are
   3).  fflags, frm and fcsr also need mstatus.FS <> Off, a hypothesis.
   ------------------------------------------------------------------------ *)

val csr_insts = ["CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"]

fun range a b = List.tabulate (b - a + 1, fn i => a + i)

val present_csrs =
  range 0x001 0x003 @ range 0xC00 0xC02 @ [0x100] @ range 0x104 0x106 @
  [0x10A] @ range 0x140 0x144 @ [0x180] @ range 0xF11 0xF15 @
  range 0x300 0x306 @ [0x30A, 0x320] @ range 0x323 0x33F @
  range 0x340 0x344 @ [0x3A0, 0x3A2] @ range 0x3B0 0x3BF @ [0xB00] @
  range 0xB02 0xB1F

(* the CSRs that the step theorems must cover (Stage C of WP3) *)
val required_csrs =
  [0x300, 0x301, 0x304, 0x305, 0x340, 0x341, 0x342, 0x343, 0x344, 0x306,
   0x320, 0x3A0, 0x3A2] @ range 0x3B0 0x3BF @
  [0x001, 0x002, 0x003, 0xC00, 0xC02, 0xB00, 0xB02, 0xF14, 0x106]

fun csr_of h = hex_int h div 1048576
fun csr_field h = (hex_int h div 32768) mod 32

fun csr_write (inner, h) =
  Lib.mem inner ["CSRRW", "CSRRWI"] orelse csr_field h <> 0

(* NONE when legal in M-mode, SOME why otherwise *)
fun csr_illegal inner h =
  let
    val c = csr_of h
  in
    if not (Lib.mem c present_csrs) then SOME "no such CSR"
    else if csr_write (inner, h) andalso c div 1024 = 3
      then SOME "write of a read-only CSR"
    else NONE
  end

fun class_of (outer, inner, _) =
  case outer of
     "ArithI" => "ALU"
   | "ArithR" => "ALU"
   | "Shift" => "ALU"
   | "MulDiv" => "ALU"
   | "Branch" =>
       if inner = "JAL" orelse inner = "JALR" then "JAL/JALR" else "branch"
   | "Load" => "load"
   | "Store" => "store"
   | "AMO" =>
       if String.isPrefix "LR_" inner orelse String.isPrefix "SC_" inner
         then "LR/SC"
       else "AMO"
   | "FPLoad" => "FP load/store"
   | "FPStore" => "FP load/store"
   | "FArith" => "FP arithmetic"
   | "FConv" => "FP arithmetic"
   | "FENCE" => "FENCE"
   | "FENCE_I" => "FENCE"
   | "System" =>
       if Lib.mem inner ["ECALL", "EBREAK"] then "trap"
       else if inner = "MRET" then "MRET"
       else if Lib.mem inner csr_insts then "CSR"
       else "system"
   | _ => "other"

fun width inner =
  if Lib.mem inner ["LB", "LBU", "SB"] then 1
  else if Lib.mem inner ["LH", "LHU", "SH"] then 2
  else if Lib.mem inner ["LW", "LWU", "SW", "FLW", "FSW", "LR_W", "SC_W"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_W" inner then 4
  else if Lib.mem inner ["LD", "SD", "FLD", "FSD", "LR_D", "SC_D"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_D" inner then 8
  else 0

val rv64_only =
  ["ADDIW", "SLLIW", "SRLIW", "SRAIW", "ADDW", "SUBW", "SLLW", "SRLW",
   "SRAW", "MULW", "DIVW", "REMW", "DIVUW", "REMUW", "LD", "LWU", "SD",
   "LR_D", "SC_D"]

(* the instructions with a rounding-mode field ... *)
val rounding =
  ["FADD_S", "FSUB_S", "FMUL_S", "FDIV_S", "FSQRT_S", "FMADD_S", "FMSUB_S",
   "FNMADD_S", "FNMSUB_S", "FCVT_S_W", "FCVT_S_WU", "FCVT_S_L", "FCVT_S_LU",
   "FCVT_W_S", "FCVT_WU_S", "FCVT_L_S", "FCVT_LU_S",
   "FADD_D", "FSUB_D", "FMUL_D", "FDIV_D", "FSQRT_D", "FMADD_D", "FMSUB_D",
   "FNMADD_D", "FNMSUB_D", "FCVT_D_W", "FCVT_D_WU", "FCVT_D_L", "FCVT_D_LU",
   "FCVT_W_D", "FCVT_WU_D", "FCVT_L_D", "FCVT_LU_D", "FCVT_S_D", "FCVT_D_S"]

(* ... and those of them that never round, for which RMM is legal *)
val exact_conversion = ["FCVT_D_W", "FCVT_D_WU", "FCVT_D_S"]

(* required hypotheses, and those that may also occur *)
fun expected h (inst as (outer, inner, _)) =
  let
    val compressed = is_compressed h
    val w = width inner
    val fp = Lib.mem outer ["FPLoad", "FPStore", "FArith", "FConv"]
    val dyn = not compressed andalso Lib.mem inner rounding andalso
              rm_of h = 7
    val const_c = constant_target_bit1 inst
    val required =
      ["H1", "H3.pmpcfg0", "H3.pmpcfg2", "H6", "exception", "NextFetch",
       "pc<0>", "mem", if compressed orelse const_c then "C" else "pc<1>|C"] @
      (if w > 0 then ["H2"] else []) @
      (if w = 8 then ["H4.pmpcfg0", "H4.pmpcfg2"] else []) @
      (case (data_address inst, w) of
          (SOME _, 2) => ["H5.1"]
        | (SOME _, 4) => ["H5.2"]
        | (SOME _, 8) => ["H5.3"]
        | _ => []) @
      (if not compressed andalso Option.isSome (jump_target inst)
         then ["target<1>|C"] else []) @
      (if Lib.mem inner rv64_only then ["RV64"] else []) @
      (if fp orelse
          Lib.mem inner csr_insts andalso Lib.mem (csr_of h) [1, 2, 3]
         then ["FS"] else []) @
      (if dyn then
         [if Lib.mem inner exact_conversion then "frm<5" else "frm"]
       else [])
    (* SLLI, SRLI and SRAI with shamt<5> set are RV64-only *)
    val optional =
      if Lib.mem inner ["SLLI", "SRLI", "SRAI"] then ["RV64"] else []
  in
    (required, optional)
  end

(* The instructions the step library cannot step, and why *)
fun no_step h (inst as (outer, inner, _)) =
  if outer = "UnknownInstruction" then SOME "reserved encoding"
  else if inner = "SRET"
    then SOME "SRET returns to S-mode or U-mode, which NextRISCV does not model"
  else if Lib.mem inner csr_insts then csr_illegal inner h
  else if not (is_compressed h) andalso Lib.mem inner rounding then
    case rm_of h of
       5 => SOME "reserved rounding mode"
     | 6 => SOME "reserved rounding mode"
     | 4 => if Lib.mem inner exact_conversion then NONE
            else SOME "RMM, which L3 does not implement"
     | _ => NONE
  else NONE

(* ------------------------------------------------------------------------
   Checking one theorem
   ------------------------------------------------------------------------ *)

val bad_consts =
  [``signalException``, ``signalAddressException``, ``raise'exception``,
   ``dataAddr``, ``fetchAddr``, ``pmpCheck``, ``round``, ``validRounding``,
   ``accrueFlags``, ``curPrivilege``, ``in32BitMode``, ``haveRVC``,
   (* address translation *)
   ``translateAddr``, ``effectivePrivilege``, ``ptwLevel``, ``ptwStep``,
   ``ptePermits``,
   (* traps and MRET *)
   ``takeTrap``, ``mret``, ``excDest``, ``excCode``, ``trapVector``,
   ``rawInstBits``, ``privilege``, ``privLevel``, ``setPrivilege``,
   ``read_xepc``,
   (* CSRs: the read, the write, the legalisers and the access checks *)
   ``CSR``, ``write'CSR``, ``CSRMap``, ``write'CSRMap``, ``writeCSR``,
   ``checkCSROp``, ``is_CSR_defined``, ``check_CSR_access``,
   ``check_CSR_conditions``, ``counterReadAllowed``, ``fpEnabled``,
   ``is_mhpm_CSR``, ``read_mip``, ``read_mstatus``, ``read_sstatus``,
   ``legalize_mstatus``, ``legalize_sstatus``, ``legalize_misa``,
   ``legalize_xtvec``, ``legalize_xepc``, ``legalize_mcause``,
   ``legalize_scause``, ``legalize_satp``, ``legalize_pmpcfg``,
   ``legalize_pmpcfg_byte``, ``write_pmpaddr``, ``pmpcfg_ent``, ``mtime``,
   ``mtimecmp``, ``msip``, ``MEM``, ``Delta``, ``write'Delta``]

(* s' is s with a sequence of field updates *)
fun is_update tm =
  Term.aconv tm s orelse
  (case boolSyntax.strip_comb tm of
      (f, [_, r]) =>
        Term.is_const f andalso
        String.isSuffix "_fupd" (fst (Term.dest_const f)) andalso
        is_update r
    | _ => false)

fun sort_uniq l = Lib.mk_set (Listsort.sort String.compare l)

(* c_SCSR, read or updated: the S-mode CSRs.  M-mode code does not depend
   on them (doc/design-smode.md §1.1, §1.8), so no hypothesis mentions
   c_SCSR, and a conclusion only for a CSR instruction on one of the CSRs
   stored there (riscv.spec, record SupervisorCSR), whose value it reads or
   writes. *)
val scsr_consts =
  [Term.rator ``^s.c_SCSR``,
   fst (boolSyntax.strip_comb ``^s with c_SCSR := f``)]

fun mentions_scsr tm =
  List.exists (fn c => Lib.can (HolKernel.find_term (Term.same_const c)) tm)
    scsr_consts

val scsr_csrs = [0x105, 0x106, 0x10A, 0x140, 0x141, 0x142, 0x143, 0x180]

fun scsr_access h (_, inner, _) =
  Lib.mem inner csr_insts andalso Lib.mem (csr_of h) scsr_csrs

fun check h inst th =
  let
    val (required, optional) = expected h inst
    val cats = List.map (category inst) (Thm.hyp th)
    val ucats = sort_uniq cats
    val (l, r) = boolSyntax.dest_eq (Thm.concl th)
    val errors =
      List.filter (String.isPrefix "UNEXPECTED") ucats @
      List.mapPartial
        (fn c => if Lib.mem c ucats then NONE else SOME ("missing " ^ c))
        required @
      List.mapPartial
        (fn c => if Lib.mem c (required @ optional) orelse
                    String.isPrefix "UNEXPECTED" c
                   then NONE
                 else SOME ("not allowed: " ^ c)) ucats @
      (* one hypothesis per condition, besides the instruction bytes *)
      List.mapPartial
        (fn c => if c <> "mem" andalso
                    List.length (List.filter (equal c) cats) > 1
                   then SOME ("more than one hypothesis " ^ c) else NONE)
        ucats @
      (if List.exists Feq (Thm.hyp th) then ["vacuous"] else []) @
      (if List.exists mentions_scsr (Thm.hyp th)
         then ["hypothesis on c_SCSR"] else []) @
      (if mentions_scsr r andalso not (scsr_access h inst)
         then ["c_SCSR in the conclusion, not a CSR instruction on it"]
       else []) @
      (if Term.aconv l ``riscv_step$NextRISCV ^s`` andalso
          optionSyntax.is_some r andalso is_update (optionSyntax.dest_some r)
         then []
       else ["conclusion is not NextRISCV s = SOME (s with ...)"]) @
      List.mapPartial
        (fn c => if Lib.can (HolKernel.find_term (Term.same_const c)) r
                   then SOME ("left in conclusion: " ^
                              fst (Term.dest_const c))
                 else NONE) bad_consts
  in
    (ucats, errors)
  end

(* ------------------------------------------------------------------------
   Test cases
   ------------------------------------------------------------------------ *)

(* A deterministic choice of the free bits of a riscv_dict pattern *)
local
  val seed = ref 0w42 : Word32.word ref
  fun next () =
    ( seed := Word32.+ (Word32.* (!seed, 0w1664525), 0w1013904223)
    ; Word32.andb (Word32.>> (!seed, 0w16), 0w1) = 0w1 )
in
  fun random_bit () = next ()
end

fun bits_to_hex bs =
  let
    val n = List.foldl (fn (b, a) => 2 * a + (if b then 1 else 0)) 0 bs
    val digits = List.length bs div 4
  in
    StringCvt.padLeft #"0" digits
      (String.map Char.toLower (Int.fmt StringCvt.HEX n))
  end

(* the pattern's bits, MSB first, with rm (bits 14:12) set when given *)
fun instantiate rm pat =
  let
    val (l, _) = listSyntax.dest_list pat
    val n = List.length l
    val bits =
      List.map
        (fn t => if Teq t then true else if Feq t then false
                 else random_bit ()) l
    val bits =
      case rm of
         NONE => bits
       | SOME v =>
           List.tabulate
             (n, fn i =>
                   if i >= 17 andalso i <= 19
                     then (v div (if i = 17 then 4 else if i = 18 then 2
                                  else 1)) mod 2 = 1
                   else List.nth (bits, i))
  in
    bits_to_hex bits
  end

(* Encodings at the edges of the contract, with whether they must step,
   and for some the values of fields of the state after the step, written
   out from doc/design-privileged.md: each is an equation between a field
   of s' (the argument) and its value, in terms of s. *)
local
  val m = ``^s.c_MCSR ^s.procID``
  val st = ``(^s.c_MCSR ^s.procID).mstatus``
  fun gpr n = ``^s.c_gpr ^s.procID ^(wordsSyntax.mk_wordii (n, 5))``
  fun mcsr s' = ``^s'.c_MCSR ^s'.procID``
  fun scsr s' = ``^s'.c_SCSR ^s'.procID``
  fun same_regs s' = ``^s'.c_gpr = ^s.c_gpr``
  fun same_mcsr s' = ``^s'.c_MCSR = ^s.c_MCSR``
  fun same_scsr s' = ``^s'.c_SCSR = ^s.c_SCSR``
  (* bit i, and bits 12:11 (MPP), of mstatus as stored *)
  fun st_bit i = ``word_bit ^(numSyntax.term_of_int i) (reg'mstatus ^st)``
  val st_mpp = ``(12 >< 11) (reg'mstatus ^st) : word2``
  fun next_pc n s' =
    ``^s'.c_PC ^s'.procID = ^s.c_PC ^s.procID + ^(wordsSyntax.mk_wordii (n, 64))``
  (* the trap of an ECALL or EBREAK from M-mode, with cause ec and trap value
     tval (design-privileged.md §4.6, into M) *)
  fun trap ec tval =
    [fn s' => ``^s'.c_privilege ^s'.procID = 3w``,
     fn s' => ``^s'.c_PC ^s'.procID = ^m.mtvec && ~3w``,
     fn s' => ``(^(mcsr s')).mcause = <| EC := ^(wordsSyntax.mk_wordii (ec, 63));
                                         Int := F |>``,
     fn s' => ``(^(mcsr s')).mepc = ^s.c_PC ^s.procID``,
     fn s' => ``(^(mcsr s')).mtval = ^tval``,
     fn s' => ``(^(mcsr s')).mstatus =
                ^st with <| MIE := F; MPIE := ^st.MIE; MPP := 3w |>``,
     fn s' => ``(^(mcsr s')).mtvec = ^m.mtvec``,
     same_regs]
in
  val edge_cases = [
  ("002000e7", "jalr ra,2(zero): constant target, bit 1 set", true, []),
  ("004000e7", "jalr ra,4(zero): constant target, 4-byte aligned", true, []),
  ("00802503", "lw a0,8(zero): constant aligned address", true, []),
  ("00803503", "ld a0,8(zero): constant aligned address", true, []),
  ("00602503", "lw a0,6(zero): constant misaligned address", false, []),
  ("00101503", "lh a0,1(zero): constant misaligned address", false, []),
  ("0000a02f", "amoadd.w zero,zero,(ra)", true, []),
  ("1000302f", "lr.d zero,(zero)", true, []),
  ("00c5c553", "fadd.s fa0,fa1,fa2,rmm", false, []),
  ("00c5d553", "fadd.s fa0,fa1,fa2 with rm = 5", false, []),
  ("d205c553", "fcvt.d.w fa0,a1,rmm", true, []),
  ("d205e553", "fcvt.d.w fa0,a1 with rm = 6", false, []),
  ("0000", "c.illegal", false, []),
  (* traps, MRET, SRET and WFI *)
  ("00000073", "ecall: trap to M-mode with cause 11", true, trap 11 ``0w: word64``),
  ("00100073", "ebreak: trap to M-mode with cause 3, mtval = pc", true,
   trap 3 ``^s.c_PC ^s.procID``),
  ("9002", "c.ebreak: as ebreak", true, trap 3 ``^s.c_PC ^s.procID``),
  ("30200073", "mret", true,
   [fn s' => ``^s'.c_privilege ^s'.procID =
                if ^st.MPP = 2w then 0w else ^st.MPP``,
    fn s' => ``^s'.c_PC ^s'.procID =
                if ^m.misa.C then ^m.mepc else ^m.mepc && ~3w``,
    fn s' => ``(^(mcsr s')).mstatus =
                ^st with <| MIE := ^st.MPIE; MPIE := T; MPP := 0w;
                            MPRV := (^st.MPRV /\ (^st.MPP = 3w)) |>``,
    fn s' => ``(^(mcsr s')).mepc = ^m.mepc``,
    same_regs]),
  ("10200073", "sret", false, []),
  ("10500073", "wfi: a no-op in M-mode", true,
   [next_pc 4, same_mcsr, same_regs,
    fn s' => ``^s'.c_privilege = ^s.c_privilege``]),
  ("12000073", "sfence.vma: a no-op, with no address-translation cache", true,
   [next_pc 4, same_mcsr, same_scsr, same_regs,
    fn s' => ``^s'.c_privilege = ^s.c_privilege``]),
  (* CSR instructions *)
  ("30529073", "csrw mtvec,t0: legalised mtvec", true,
   [fn s' => ``(^(mcsr s')).mtvec =
                if word_bit 1 ^(gpr 5) then
                  ((63 >< 2) ^(gpr 5) : 62 word) @@ ((1 >< 0) ^m.mtvec : word2)
                else ^(gpr 5)``,
    next_pc 4, same_regs]),
  ("300020f3", "csrrs ra,mstatus,zero: the mstatus read, SD from FS", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 1w =
                reg'mstatus ^st && 0x7E79AAw || 0xA00000000w ||
                (if ^st.FS = 3w then 0x8000000000000000w else 0w)``,
    same_mcsr, next_pc 4]),
  ("10002573", "csrr a0,sstatus: the mstatus read, through SSTATUS_MASK",
   true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w =
                (reg'mstatus ^st && 0x7E79AAw || 0xA00000000w ||
                 (if ^st.FS = 3w then 0x8000000000000000w else 0w)) &&
                0x80000003018DE762w``,
    same_mcsr, next_pc 4]),
  ("10029073", "csrw sstatus,t0: SIE SPIE SPP FS SUM MXR written", true,
   [fn s' => ``(^(mcsr s')).mstatus.SIE = word_bit 1 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SPIE = word_bit 5 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SPP = word_bit 8 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.FS = (14 >< 13) ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SUM = word_bit 18 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.MXR = word_bit 19 ^(gpr 5)``,
    (* the fields that sstatus does not show keep their stored bits *)
    fn s' => ``(^(mcsr s')).mstatus.MIE = ^(st_bit 3)``,
    fn s' => ``(^(mcsr s')).mstatus.MPIE = ^(st_bit 7)``,
    fn s' => ``(^(mcsr s')).mstatus.MPRV = ^(st_bit 17)``,
    fn s' => ``(^(mcsr s')).mstatus.TVM = ^(st_bit 20)``,
    fn s' => ``(^(mcsr s')).mstatus.TW = ^(st_bit 21)``,
    fn s' => ``(^(mcsr s')).mstatus.TSR = ^(st_bit 22)``,
    fn s' => ``(^(mcsr s')).mstatus.MPP =
                if ^st_mpp = 2w then 0w else ^st_mpp``,
    same_scsr, same_regs, next_pc 4]),
  ("18029073", "csrw satp,t0: written iff MODE is Bare, Sv39, Sv48 or Sv57",
   true,
   [fn s' => ``(^(scsr s')).satp =
                if (^(gpr 5) && 0xF000000000000000w = 0w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0x8000000000000000w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0x9000000000000000w) \/
                   (^(gpr 5) && 0xF000000000000000w = 0xA000000000000000w)
                then ^(gpr 5) else (^s.c_SCSR ^s.procID).satp``,
    same_mcsr, same_regs, next_pc 4]),
  ("18005073", "csrwi satp,0: Bare", true,
   [fn s' => ``(^(scsr s')).satp = 0w``, same_mcsr, same_regs, next_pc 4]),
  ("18002573", "csrr a0,satp: the value stored", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w = (^s.c_SCSR ^s.procID).satp``,
    same_mcsr, same_scsr, next_pc 4]),
  ("3a0fd073", "csrwi pmpcfg0,0x1f: entry 0 NAPOT RWX", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 0x1Fw``, same_regs]),
  ("3a015073", "csrwi pmpcfg0,2: W without R, so W cleared", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 0w``]),
  ("3a075073", "csrwi pmpcfg0,14: W and X without R, so both cleared", true,
   [fn s' => ``(^(mcsr s')).pmpcfg0 = 8w``]),
  ("3b329073", "csrw pmpaddr3,t0: bits 63:54 read-only zero", true,
   [fn s' => ``(^(mcsr s')).pmpaddr3 = ^(gpr 5) && 0x3FFFFFFFFFFFFFw``]),
  ("34129073", "csrw mepc,t0: bit 0 cleared", true,
   [fn s' => ``(^(mcsr s')).mepc = ^(gpr 5) && ~1w``]),
  ("34102573", "csrr a0,mepc: bit 1 masked without C", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w =
                if ^m.misa.C then ^m.mepc else ^m.mepc && ~3w``,
    same_mcsr]),
  ("30429073", "csrw mie,t0: the six interrupts", true,
   [fn s' => ``reg'mie (^(mcsr s')).mie = ^(gpr 5) && 0xAAAw``]),
  ("3067d073", "csrwi mcounteren,15: CY, TM, IR", true,
   [fn s' => ``(^(mcsr s')).mcounteren = 7w``]),
  ("32005073", "csrwi mcountinhibit,0", true,
   [fn s' => ``(^(mcsr s')).mcountinhibit = 0w``]),
  ("340110f3", "csrrw ra,mscratch,sp: swap", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 1w = ^m.mscratch``,
    fn s' => ``(^(mcsr s')).mscratch = ^(gpr 2)``]),
  ("f1402673", "csrr a2,mhartid", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 12w = ^m.mhartid``, same_mcsr]),
  ("c0002573", "rdcycle a0", true,
   [fn s' => ``^s'.c_gpr ^s'.procID 10w = ^s.c_cycles ^s.procID``,
    same_mcsr]),
  ("b0229073", "csrw minstret,t0: no increment for this instruction", true,
   [fn s' => ``^s'.c_instret ^s'.procID = ^(gpr 5)``,
    fn s' => ``^s'.c_minstret_written ^s'.procID``]),
  ("0010d073", "csrwi fflags,1: NX, and FS Dirty", true,
   [fn s' => ``reg'FPCSR (^s'.c_UCSR ^s'.procID).fpcsr =
                reg'FPCSR (^s.c_UCSR ^s.procID).fpcsr && 0xFFFFFFE0w || 1w``,
    fn s' => ``(^(mcsr s')).mstatus.FS = 3w``]),
  ("30029073", "csrw mstatus,t0: MIE, SUM, and MPP 2 written as 0", true,
   [fn s' => ``(^(mcsr s')).mstatus.MIE = word_bit 3 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.SUM = word_bit 18 ^(gpr 5)``,
    fn s' => ``(^(mcsr s')).mstatus.MPP =
                if (12 >< 11) ^(gpr 5) = 2w: word2 then 0w
                else (12 >< 11) ^(gpr 5)``]),
  ("c0001073", "unimp (csrrw zero,cycle,zero): write of a read-only CSR",
   false, []),
  ("7c002573", "csrrs a0,0x7c0,zero: no such CSR", false, []),
  ("3a1020f3", "csrrs ra,pmpcfg1,zero: odd pmpcfg, absent on RV64", false,
   []),
  ("c8002573", "csrrs a0,cycleh,zero: RV32 only", false, [])
  ]
end

(* Every distinct instruction encoding of the programs in ../sim/tests, in
   order of first occurrence: the ELFs built by ../sim/Makefile, through
   riscv64-unknown-elf-objdump -d -M no-aliases, with the .word lines
   (encodings that the assembler does not accept, here rm = RMM) kept.
   Those of smode.S, sv39.S, sv48.S and sv57.S run in S-mode and U-mode as
   well, with and without address translation; their step theorems here
   are for M-mode, like all the others, and SRET has none. *)
val sim_tests = [
  (* tests/int.S *)
  ("00002d97", "auipc s11,0x2"),
  ("050d8d93", "addi s11,s11,80"),
  ("00000193", "addi gp,zero,0"),
  ("00002417", "auipc s0,0x2"),
  ("ff440413", "addi s0,s0,-12"),
  ("00000293", "addi t0,zero,0"),
  ("00000513", "addi a0,zero,0"),
  ("00800313", "addi t1,zero,8"),
  ("00329393", "slli t2,t0,0x3"),
  ("007403b3", "add t2,s0,t2"),
  ("0003be03", "ld t3,0(t2)"),
  ("01c50533", "add a0,a0,t3"),
  ("00128293", "addi t0,t0,1"),
  ("fe62c6e3", "blt t0,t1,80000020"),
  ("00adb023", "sd a0,0(s11)"),
  ("008d8d93", "addi s11,s11,8"),
  ("00100193", "addi gp,zero,1"),
  ("00247fb7", "lui t6,0x247"),
  ("8adf8f9b", "addiw t6,t6,-1875"),
  ("00ef9f93", "slli t6,t6,0xe"),
  ("ccdf8f93", "addi t6,t6,-819"),
  ("00cf9f93", "slli t6,t6,0xc"),
  ("5e7f8f93", "addi t6,t6,1511"),
  ("00df9f93", "slli t6,t6,0xd"),
  ("024f8f93", "addi t6,t6,36"),
  ("25f51e63", "bne a0,t6,800002c0"),
  ("01040503", "lb a0,16(s0)"),
  ("00200193", "addi gp,zero,2"),
  ("ff000f93", "addi t6,zero,-16"),
  ("25f51663", "bne a0,t6,800002c0"),
  ("01044503", "lbu a0,16(s0)"),
  ("00300193", "addi gp,zero,3"),
  ("0f000f93", "addi t6,zero,240"),
  ("23f51e63", "bne a0,t6,800002c0"),
  ("01041503", "lh a0,16(s0)"),
  ("00400193", "addi gp,zero,4"),
  ("ffffefb7", "lui t6,0xffffe"),
  ("ef0f8f9b", "addiw t6,t6,-272"),
  ("23f51463", "bne a0,t6,800002c0"),
  ("01045503", "lhu a0,16(s0)"),
  ("00500193", "addi gp,zero,5"),
  ("0000efb7", "lui t6,0xe"),
  ("21f51a63", "bne a0,t6,800002c0"),
  ("01042503", "lw a0,16(s0)"),
  ("00600193", "addi gp,zero,6"),
  ("9abcefb7", "lui t6,0x9abce"),
  ("21f51063", "bne a0,t6,800002c0"),
  ("01046503", "lwu a0,16(s0)"),
  ("00700193", "addi gp,zero,7"),
  ("0004dfb7", "lui t6,0x4d"),
  ("5e7f8f9b", "addiw t6,t6,1511"),
  ("ef0f8f93", "addi t6,t6,-272"),
  ("1df51e63", "bne a0,t6,800002c0"),
  ("00002497", "auipc s1,0x2"),
  ("f5848493", "addi s1,s1,-168"),
  ("fff00593", "addi a1,zero,-1"),
  ("00b4b023", "sd a1,0(s1)"),
  ("01100593", "addi a1,zero,17"),
  ("00b48023", "sb a1,0(s1)"),
  ("000035b7", "lui a1,0x3"),
  ("3225859b", "addiw a1,a1,802"),
  ("00b49123", "sh a1,2(s1)"),
  ("776655b7", "lui a1,0x77665"),
  ("5445859b", "addiw a1,a1,1348"),
  ("00b4a223", "sw a1,4(s1)"),
  ("0004b503", "ld a0,0(s1)"),
  ("00800193", "addi gp,zero,8"),
  ("00776fb7", "lui t6,0x776"),
  ("655f8f9b", "addiw t6,t6,1621"),
  ("443f8f93", "addi t6,t6,1091"),
  ("323f8f93", "addi t6,t6,803"),
  ("010f9f93", "slli t6,t6,0x10"),
  ("f11f8f93", "addi t6,t6,-239"),
  ("17f51c63", "bne a0,t6,800002c0"),
  ("00900193", "addi gp,zero,9"),
  ("0014c503", "lbu a0,1(s1)"),
  ("0ff00f93", "addi t6,zero,255"),
  ("17f51463", "bne a0,t6,800002c0"),
  ("01043583", "ld a1,16(s0)"),
  ("00300613", "addi a2,zero,3"),
  ("02c58533", "mul a0,a1,a2"),
  ("00a00193", "addi gp,zero,10"),
  ("0036afb7", "lui t6,0x36a"),
  ("d03f8f9b", "addiw t6,t6,-765"),
  ("69df8f93", "addi t6,t6,1693"),
  ("00ff9f93", "slli t6,t6,0xf"),
  ("1b5f8f93", "addi t6,t6,437"),
  ("cd0f8f93", "addi t6,t6,-816"),
  ("13f51663", "bne a0,t6,800002c0"),
  ("01843603", "ld a2,24(s0)"),
  ("02c5b533", "mulhu a0,a1,a2"),
  ("00b00193", "addi gp,zero,11"),
  ("12345fb7", "lui t6,0x12345"),
  ("678f8f9b", "addiw t6,t6,1656"),
  ("11f51a63", "bne a0,t6,800002c0"),
  ("ff900593", "addi a1,zero,-7"),
  ("00200613", "addi a2,zero,2"),
  ("02c5c533", "div a0,a1,a2"),
  ("00c00193", "addi gp,zero,12"),
  ("ffd00f93", "addi t6,zero,-3"),
  ("0ff51e63", "bne a0,t6,800002c0"),
  ("02c5e533", "rem a0,a1,a2"),
  ("00d00193", "addi gp,zero,13"),
  ("fff00f93", "addi t6,zero,-1"),
  ("0ff51663", "bne a0,t6,800002c0"),
  ("0205d533", "divu a0,a1,zero"),
  ("00e00193", "addi gp,zero,14"),
  ("0df51e63", "bne a0,t6,800002c0"),
  ("0205e533", "rem a0,a1,zero"),
  ("00f00193", "addi gp,zero,15"),
  ("ff900f93", "addi t6,zero,-7"),
  ("0df51263", "bne a0,t6,800002c0"),
  ("02043583", "ld a1,32(s0)"),
  ("4045d513", "srai a0,a1,0x4"),
  ("01000193", "addi gp,zero,16"),
  ("fff00f9b", "addiw t6,zero,-1"),
  ("03bf9f93", "slli t6,t6,0x3b"),
  ("0bf51663", "bne a0,t6,800002c0"),
  ("0045d513", "srli a0,a1,0x4"),
  ("01100193", "addi gp,zero,17"),
  ("00100f9b", "addiw t6,zero,1"),
  ("09f51c63", "bne a0,t6,800002c0"),
  ("800005b7", "lui a1,0x80000"),
  ("fff5859b", "addiw a1,a1,-1"),
  ("0015851b", "addiw a0,a1,1"),
  ("01200193", "addi gp,zero,18"),
  ("80000fb7", "lui t6,0x80000"),
  ("09f51063", "bne a0,t6,800002c0"),
  ("0045551b", "srliw a0,a0,0x4"),
  ("01300193", "addi gp,zero,19"),
  ("08000fb7", "lui t6,0x8000"),
  ("07f51463", "bne a0,t6,800002c0"),
  ("00100613", "addi a2,zero,1"),
  ("00c5a533", "slt a0,a1,a2"),
  ("01400193", "addi gp,zero,20"),
  ("00100f93", "addi t6,zero,1"),
  ("05f51863", "bne a0,t6,800002c0"),
  ("00c5b533", "sltu a0,a1,a2"),
  ("01500193", "addi gp,zero,21"),
  ("00000f93", "addi t6,zero,0"),
  ("05f51063", "bne a0,t6,800002c0"),
  ("02800513", "addi a0,zero,40"),
  ("01c000ef", "jal ra,800002a4"),
  ("01600193", "addi gp,zero,22"),
  ("02a00f93", "addi t6,zero,42"),
  ("03f51263", "bne a0,t6,800002c0"),
  ("00c0006f", "jal zero,800002ac"),
  ("00250513", "addi a0,a0,2"),
  ("00008067", "jalr zero,0(ra)"),
  ("00001f17", "auipc t5,0x1"),
  ("d50f0f13", "addi t5,t5,-688"),
  ("01ff3023", "sd t6,0(t5)"),
  ("0000006f", "jal zero,800002bc"),
  ("00119f93", "slli t6,gp,0x1"),
  ("001fef93", "ori t6,t6,1"),
  ("d38f0f13", "addi t5,t5,-712"),
  (* tests/rvc.S *)
  ("4181", "c.li gp,0"),
  ("00002117", "auipc sp,0x2"),
  ("04610113", "addi sp,sp,70"),
  ("fee40413", "addi s0,s0,-18"),
  ("4515", "c.li a0,5"),
  ("051d", "c.addi a0,7"),
  ("55f5", "c.li a1,-3"),
  ("952e", "c.add a0,a1"),
  ("862a", "c.mv a2,a0"),
  ("8e0d", "c.sub a2,a1"),
  ("00cdb023", "sd a2,0(s11)"),
  ("0da1", "c.addi s11,8"),
  ("4185", "c.li gp,1"),
  ("4fb1", "c.li t6,12"),
  ("11f61c63", "bne a2,t6,80000148"),
  ("6014", "c.ld a3,0(s0)"),
  ("0685", "c.addi a3,1"),
  ("e414", "c.sd a3,8(s0)"),
  ("6418", "c.ld a4,8(s0)"),
  ("00edb023", "sd a4,0(s11)"),
  ("4189", "c.li gp,2"),
  ("0fba", "c.slli t6,0xe"),
  ("c4df8f93", "addi t6,t6,-947"),
  ("0fb2", "c.slli t6,0xc"),
  ("0fb6", "c.slli t6,0xd"),
  ("ef1f8f93", "addi t6,t6,-271"),
  ("0ff71563", "bne a4,t6,80000148"),
  ("405c", "c.lw a5,4(s0)"),
  ("00fdb023", "sd a5,0(s11)"),
  ("418d", "c.li gp,3"),
  ("0df79a63", "bne a5,t6,80000148"),
  ("713d", "c.addi16sp sp,-32"),
  ("0808", "c.addi4spn a0,sp,16"),
  ("e03a", "c.sdsp a4,0(sp)"),
  ("c43e", "c.swsp a5,8(sp)"),
  ("6582", "c.ldsp a1,0(sp)"),
  ("4622", "c.lwsp a2,8(sp)"),
  ("6105", "c.addi16sp sp,32"),
  ("95b2", "c.add a1,a2"),
  ("00bdb023", "sd a1,0(s11)"),
  ("4191", "c.li gp,4"),
  ("0fbe", "c.slli t6,0xf"),
  ("8adf8f93", "addi t6,t6,-1875"),
  ("f13f8f93", "addi t6,t6,-237"),
  ("569f8f93", "addi t6,t6,1385"),
  ("09f59f63", "bne a1,t6,80000148"),
  ("557d", "c.li a0,-1"),
  ("1572", "c.slli a0,0x3c"),
  ("8511", "c.srai a0,0x4"),
  ("9161", "c.srli a0,0x38"),
  ("897d", "c.andi a0,31"),
  ("4195", "c.li gp,5"),
  ("4ffd", "c.li t6,31"),
  ("09f51363", "bne a0,t6,80000148"),
  ("4571", "c.li a0,28"),
  ("45a9", "c.li a1,10"),
  ("8e6d", "c.and a2,a1"),
  ("8e4d", "c.or a2,a1"),
  ("8e29", "c.xor a2,a0"),
  ("800006b7", "lui a3,0x80000"),
  ("36fd", "c.addiw a3,-1"),
  ("9eb1", "c.addw a3,a2"),
  ("9e8d", "c.subw a3,a1"),
  ("00ddb023", "sd a3,0(s11)"),
  ("4199", "c.li gp,6"),
  ("2fad", "c.addiw t6,11"),
  ("05f69f63", "bne a3,t6,80000148"),
  ("4501", "c.li a0,0"),
  ("4581", "c.li a1,0"),
  ("c111", "c.beqz a0,800000f6"),
  ("4585", "c.li a1,1"),
  ("e99d", "c.bnez a1,8000012c"),
  ("a011", "c.j 800000fc"),
  ("4589", "c.li a1,2"),
  ("419d", "c.li gp,7"),
  ("4f81", "c.li t6,0"),
  ("05f59463", "bne a1,t6,80000148"),
  ("4505", "c.li a0,1"),
  ("00000297", "auipc t0,0x0"),
  ("02a28293", "addi t0,t0,42"),
  ("9282", "c.jalr t0"),
  ("41a1", "c.li gp,8"),
  ("4f8d", "c.li t6,3"),
  ("03f51763", "bne a0,t6,80000148"),
  ("657d", "c.lui a0,0x1f"),
  ("0001", "c.addi zero,0"),
  ("41a5", "c.li gp,9"),
  ("6ffd", "c.lui t6,0x1f"),
  ("03f51163", "bne a0,t6,80000148"),
  ("a039", "c.j 80000138"),
  ("a829", "c.j 80000148"),
  ("85aa", "c.mv a1,a0"),
  ("8082", "c.jr ra"),
  ("4f85", "c.li t6,1"),
  ("ec6f0f13", "addi t5,t5,-314"),
  ("a001", "c.j 80000146"),
  ("eb0f0f13", "addi t5,t5,-336"),
  (* tests/fp.S *)
  ("030d8d93", "addi s11,s11,48"),
  ("000022b7", "lui t0,0x2"),
  ("3002a073", "csrrs zero,mstatus,t0"),
  ("fec40413", "addi s0,s0,-20"),
  ("00043507", "fld fa0,0(s0)"),
  ("00843587", "fld fa1,8(s0)"),
  ("02b57653", "fadd.d fa2,fa0,fa1"),
  ("e2060553", "fmv.x.d a0,fa2"),
  ("00002fb7", "lui t6,0x2"),
  ("007f8f9b", "addiw t6,t6,7"),
  ("031f9f93", "slli t6,t6,0x31"),
  ("0df51a63", "bne a0,t6,80000118"),
  ("12b576d3", "fmul.d fa3,fa0,fa1"),
  ("e2068553", "fmv.x.d a0,fa3"),
  ("00004fb7", "lui t6,0x4"),
  ("00bf8f9b", "addiw t6,t6,11"),
  ("030f9f93", "slli t6,t6,0x30"),
  ("0bf51c63", "bne a0,t6,80000118"),
  ("d225f753", "fcvt.d.l fa4,a1"),
  ("52e6f7c3", "fmadd.d fa5,fa3,fa4,fa0"),
  ("00f43827", "fsd fa5,16(s0)"),
  ("01043503", "ld a0,16(s0)"),
  ("fffe0fb7", "lui t6,0xfffe0"),
  ("1b1f8f9b", "addiw t6,t6,433"),
  ("02df9f93", "slli t6,t6,0x2d"),
  ("09f51463", "bne a0,t6,80000118"),
  ("c2279553", "fcvt.l.d a0,fa5,rtz"),
  ("fea00f93", "addi t6,zero,-22"),
  ("07f51863", "bne a0,t6,80000118"),
  ("01843507", "fld fa0,24(s0)"),
  ("02043587", "fld fa1,32(s0)"),
  ("03fd3fb7", "lui t6,0x3fd3"),
  ("333f8f9b", "addiw t6,t6,819"),
  ("333f8f93", "addi t6,t6,819"),
  ("334f8f93", "addi t6,t6,820"),
  ("03f51863", "bne a0,t6,80000118"),
  ("02843687", "fld fa3,40(s0)"),
  ("a2d62553", "feq.d a0,fa2,fa3"),
  ("01f51e63", "bne a0,t6,80000118"),
  ("0040006f", "jal zero,80000104"),
  ("ef8f0f13", "addi t5,t5,-264"),
  ("ee0f0f13", "addi t5,t5,-288"),
  (* tests/fail.S *)
  ("000d8d93", "addi s11,s11,0"),
  ("03f01a63", "bne zero,t6,80000048"),
  ("03f01463", "bne zero,t6,80000048"),
  ("01f01e63", "bne zero,t6,80000048"),
  ("fc8f0f13", "addi t5,t5,-56"),
  ("fb0f0f13", "addi t5,t5,-80"),
  (* tests/batch-a.S *)
  ("03640413", "addi s0,s0,54"),
  ("00840493", "addi s1,s0,8"),
  ("123455b7", "lui a1,0x12345"),
  ("6785859b", "addiw a1,a1,1656"),
  ("1004252f", "lr.w a0,(s0)"),
  ("18b4a62f", "sc.w a2,a1,(s1)"),
  ("49f61b63", "bne a2,t6,800004c6"),
  ("18b426af", "sc.w a3,a1,(s0)"),
  ("49f69563", "bne a3,t6,800004c6"),
  ("6018", "c.ld a4,0(s0)"),
  ("00aabfb7", "lui t6,0xaab"),
  ("aabf8f9b", "addiw t6,t6,-1365"),
  ("a0bf8f93", "addi t6,t6,-1525"),
  ("aabf8f93", "addi t6,t6,-1365"),
  ("aaaf8f93", "addi t6,t6,-1366"),
  ("47f71163", "bne a4,t6,800004c6"),
  ("1004352f", "lr.d a0,(s0)"),
  ("18b4b62f", "sc.d a2,a1,(s1)"),
  ("45f61963", "bne a2,t6,800004c6"),
  ("18b436af", "sc.d a3,a1,(s0)"),
  ("45f69363", "bne a3,t6,800004c6"),
  ("43f71263", "bne a4,t6,800004c6"),
  ("18b4a02f", "sc.w zero,a1,(s1)"),
  ("41f69863", "bne a3,t6,800004c6"),
  ("3ff71763", "bne a4,t6,800004c6"),
  ("18b4262f", "sc.w a2,a1,(s0)"),
  ("3df61f63", "bne a2,t6,800004c6"),
  ("41a9", "c.li gp,10"),
  ("3df69963", "bne a3,t6,800004c6"),
  ("41ad", "c.li gp,11"),
  ("00555fb7", "lui t6,0x555"),
  ("555f8f9b", "addiw t6,t6,1365"),
  ("509f8f93", "addi t6,t6,1289"),
  ("345f8f93", "addi t6,t6,837"),
  ("678f8f93", "addi t6,t6,1656"),
  ("3bf71563", "bne a4,t6,800004c6"),
  ("004495b7", "lui a1,0x449"),
  ("8cd5859b", "addiw a1,a1,-1843"),
  ("05ba", "c.slli a1,0xe"),
  ("45558593", "addi a1,a1,1109"),
  ("05b2", "c.slli a1,0xc"),
  ("66758593", "addi a1,a1,1639"),
  ("78858593", "addi a1,a1,1928"),
  ("18b435af", "sc.d a1,a1,(s0)"),
  ("41b1", "c.li gp,12"),
  ("39f59063", "bne a1,t6,800004c6"),
  ("41b5", "c.li gp,13"),
  ("00449fb7", "lui t6,0x449"),
  ("8cdf8f9b", "addiw t6,t6,-1843"),
  ("455f8f93", "addi t6,t6,1109"),
  ("667f8f93", "addi t6,t6,1639"),
  ("788f8f93", "addi t6,t6,1928"),
  ("35f71f63", "bne a4,t6,800004c6"),
  ("01040913", "addi s2,s0,16"),
  ("00092023", "sw zero,0(s2)"),
  ("0010029b", "addiw t0,zero,1"),
  ("02fe", "c.slli t0,0x1f"),
  ("8059252f", "amomin.w a0,t0,(s2)"),
  ("41b9", "c.li gp,14"),
  ("35f51263", "bne a0,t6,800004c6"),
  ("00096703", "lwu a4,0(s2)"),
  ("41bd", "c.li gp,15"),
  ("0ffe", "c.slli t6,0x1f"),
  ("33f71a63", "bne a4,t6,800004c6"),
  ("00592023", "sw t0,0(s2)"),
  ("0090029b", "addiw t0,zero,9"),
  ("02f2", "c.slli t0,0x1c"),
  ("c059252f", "amominu.w a0,t0,(s2)"),
  ("41c1", "c.li gp,16"),
  ("31f51b63", "bne a0,t6,800004c6"),
  ("41c5", "c.li gp,17"),
  ("31f71363", "bne a4,t6,800004c6"),
  ("4295", "c.li t0,5"),
  ("1282", "c.slli t0,0x20"),
  ("a059252f", "amomax.w a0,t0,(s2)"),
  ("41c9", "c.li gp,18"),
  ("4f95", "c.li t6,5"),
  ("2ff51763", "bne a0,t6,800004c6"),
  ("41cd", "c.li gp,19"),
  ("2ff71163", "bne a4,t6,800004c6"),
  ("800002b7", "lui t0,0x80000"),
  ("32fd", "c.addiw t0,-1"),
  ("fff0029b", "addiw t0,zero,-1"),
  ("0285", "c.addi t0,1"),
  ("e059252f", "amomaxu.w a0,t0,(s2)"),
  ("41d1", "c.li gp,20"),
  ("3ffd", "c.addiw t6,-1"),
  ("2df51063", "bne a0,t6,800004c6"),
  ("41d5", "c.li gp,21"),
  ("2bf71863", "bne a4,t6,800004c6"),
  ("2d2d32b7", "lui t0,0x2d2d3"),
  ("d2d2829b", "addiw t0,t0,-723"),
  ("1286", "c.slli t0,0x21"),
  ("02a5", "c.addi t0,9"),
  ("00593023", "sd t0,0(s2)"),
  ("fff0031b", "addiw t1,zero,-1"),
  ("1302", "c.slli t1,0x20"),
  ("031d", "c.addi t1,7"),
  ("c069232f", "amominu.w t1,t1,(s2)"),
  ("41d9", "c.li gp,22"),
  ("4fa5", "c.li t6,9"),
  ("29f31663", "bne t1,t6,800004c6"),
  ("00093703", "ld a4,0(s2)"),
  ("41dd", "c.li gp,23"),
  ("2d2d3fb7", "lui t6,0x2d2d3"),
  ("d2df8f9b", "addiw t6,t6,-723"),
  ("1f86", "c.slli t6,0x21"),
  ("0f9d", "c.addi t6,7"),
  ("27f71863", "bne a4,t6,800004c6"),
  ("088892b7", "lui t0,0x8889"),
  ("8892829b", "addiw t0,t0,-1911"),
  ("12fd", "c.addi t0,-1"),
  ("77777337", "lui t1,0x77777"),
  ("7773031b", "addiw t1,t1,1911"),
  ("0305", "c.addi t1,1"),
  ("0069252f", "amoadd.w a0,t1,(s2)"),
  ("41e1", "c.li gp,24"),
  ("11111fb7", "lui t6,0x11111"),
  ("111f8f9b", "addiw t6,t6,273"),
  ("1f82", "c.slli t6,0x20"),
  ("23f71e63", "bne a4,t6,800004c6"),
  ("80000537", "lui a0,0x80000"),
  ("357d", "c.addiw a0,-1"),
  ("2505", "c.addiw a0,1"),
  ("41e5", "c.li gp,25"),
  ("23f51563", "bne a0,t6,800004c6"),
  ("0010051b", "addiw a0,zero,1"),
  ("1506", "c.slli a0,0x21"),
  ("157d", "c.addi a0,-1"),
  ("2501", "c.addiw a0,0"),
  ("41e9", "c.li gp,26"),
  ("5ffd", "c.li t6,-1"),
  ("21f51c63", "bne a0,t6,800004c6"),
  ("0010049b", "addiw s1,zero,1"),
  ("04fe", "c.slli s1,0x1f"),
  ("34fd", "c.addiw s1,-1"),
  ("41ed", "c.li gp,27"),
  ("21f49263", "bne s1,t6,800004c6"),
  ("000927b7", "lui a5,0x92"),
  ("a2b7879b", "addiw a5,a5,-1493"),
  ("07b6", "c.slli a5,0xd"),
  ("78978793", "addi a5,a5,1929"),
  ("27fd", "c.addiw a5,31"),
  ("41f1", "c.li gp,28"),
  ("23456fb7", "lui t6,0x23456"),
  ("7a8f8f9b", "addiw t6,t6,1960"),
  ("1ff79063", "bne a5,t6,800004c6"),
  ("4511", "c.li a0,4"),
  ("459d", "c.li a1,7"),
  ("02b545b3", "div a1,a0,a1"),
  ("41f5", "c.li gp,29"),
  ("1df59863", "bne a1,t6,800004c6"),
  ("4539", "c.li a0,14"),
  ("41f9", "c.li gp,30"),
  ("4f89", "c.li t6,2"),
  ("1df59063", "bne a1,t6,800004c6"),
  ("02b565b3", "rem a1,a0,a1"),
  ("41fd", "c.li gp,31"),
  ("1bf59863", "bne a1,t6,800004c6"),
  ("02b575b3", "remu a1,a0,a1"),
  ("02000193", "addi gp,zero,32"),
  ("1bf59063", "bne a1,t6,800004c6"),
  ("4f15", "c.li t5,5"),
  ("03ef7f33", "remu t5,t5,t5"),
  ("02100193", "addi gp,zero,33"),
  ("19ff1863", "bne t5,t6,800004c6"),
  ("4e85", "c.li t4,1"),
  ("03deeeb3", "rem t4,t4,t4"),
  ("02200193", "addi gp,zero,34"),
  ("19fe9063", "bne t4,t6,800004c6"),
  ("5edd", "c.li t4,-9"),
  ("02300193", "addi gp,zero,35"),
  ("17fe9863", "bne t4,t6,800004c6"),
  ("4d200513", "addi a0,zero,1234"),
  ("02400193", "addi gp,zero,36"),
  ("15f59e63", "bne a1,t6,800004c6"),
  ("02b555b3", "divu a1,a0,a1"),
  ("02500193", "addi gp,zero,37"),
  ("15f59663", "bne a1,t6,800004c6"),
  ("02600193", "addi gp,zero,38"),
  ("4d200f93", "addi t6,zero,1234"),
  ("13f59d63", "bne a1,t6,800004c6"),
  ("02700193", "addi gp,zero,39"),
  ("13f59463", "bne a1,t6,800004c6"),
  ("02b56533", "rem a0,a0,a1"),
  ("02800193", "addi gp,zero,40"),
  ("11f51b63", "bne a0,t6,800004c6"),
  ("4601", "c.li a2,0"),
  ("02c67633", "remu a2,a2,a2"),
  ("02900193", "addi gp,zero,41"),
  ("11f61363", "bne a2,t6,800004c6"),
  ("fff0051b", "addiw a0,zero,-1"),
  ("157e", "c.slli a0,0x3f"),
  ("55fd", "c.li a1,-1"),
  ("02b54633", "div a2,a0,a1"),
  ("02a00193", "addi gp,zero,42"),
  ("1ffe", "c.slli t6,0x3f"),
  ("0ff61663", "bne a2,t6,800004c6"),
  ("02b56633", "rem a2,a0,a1"),
  ("02b00193", "addi gp,zero,43"),
  ("0df61f63", "bne a2,t6,800004c6"),
  ("02c00193", "addi gp,zero,44"),
  ("0df59663", "bne a1,t6,800004c6"),
  ("02d00193", "addi gp,zero,45"),
  ("0bf51e63", "bne a0,t6,800004c6"),
  ("2468b537", "lui a0,0x2468b"),
  ("cf15051b", "addiw a0,a0,-783"),
  ("057e", "c.slli a0,0x1f"),
  ("02b5463b", "divw a2,a0,a1"),
  ("02e00193", "addi gp,zero,46"),
  ("0bf61063", "bne a2,t6,800004c6"),
  ("02b5663b", "remw a2,a0,a1"),
  ("02f00193", "addi gp,zero,47"),
  ("09f61963", "bne a2,t6,800004c6"),
  ("0010059b", "addiw a1,zero,1"),
  ("1582", "c.slli a1,0x20"),
  ("02b545bb", "divw a1,a0,a1"),
  ("03000193", "addi gp,zero,48"),
  ("07f59f63", "bne a1,t6,800004c6"),
  ("02b565bb", "remw a1,a0,a1"),
  ("03100193", "addi gp,zero,49"),
  ("07f59463", "bne a1,t6,800004c6"),
  ("0770059b", "addiw a1,zero,119"),
  ("02b555bb", "divuw a1,a0,a1"),
  ("03200193", "addi gp,zero,50"),
  ("05f59a63", "bne a1,t6,800004c6"),
  ("058d", "c.addi a1,3"),
  ("02b575bb", "remuw a1,a0,a1"),
  ("03300193", "addi gp,zero,51"),
  ("03f59f63", "bne a1,t6,800004c6"),
  ("450d", "c.li a0,3"),
  ("4595", "c.li a1,5"),
  ("02b50533", "mul a0,a0,a1"),
  ("03400193", "addi gp,zero,52"),
  ("4fbd", "c.li t6,15"),
  ("03f51663", "bne a0,t6,800004c6"),
  ("55e5", "c.li a1,-7"),
  ("02b595b3", "mulh a1,a1,a1"),
  ("03500193", "addi gp,zero,53"),
  ("01f59e63", "bne a1,t6,800004c6"),
  ("a009", "c.j 800004b6"),
  ("b48f0f13", "addi t5,t5,-1208"),
  ("b32f0f13", "addi t5,t5,-1230"),
  (* tests/fp-arith.S *)
  ("00003d97", "auipc s11,0x3"),
  ("6299", "c.lui t0,0x6"),
  ("00101073", "csrrw zero,fflags,zero"),
  ("3f800337", "lui t1,0x3f800"),
  ("f00300d3", "fmv.w.x ft1,t1"),
  ("40000337", "lui t1,0x40000"),
  ("f0030153", "fmv.w.x ft2,t1"),
  ("002081d3", "fadd.s ft3,ft1,ft2,rne"),
  ("e2018553", "fmv.x.d a0,ft3"),
  ("001015f3", "csrrw a1,fflags,zero"),
  ("30800337", "lui t1,0x30800"),
  ("33800337", "lui t1,0x33800"),
  ("0020b1d3", "fadd.s ft3,ft1,ft2,rup"),
  ("0020a1d3", "fadd.s ft3,ft1,ft2,rdn"),
  ("002091d3", "fadd.s ft3,ft1,ft2,rtz"),
  ("34400337", "lui t1,0x34400"),
  ("17f0031b", "addiw t1,zero,383"),
  ("035e", "c.slli t1,0x17"),
  ("1670031b", "addiw t1,zero,359"),
  ("0010031b", "addiw t1,zero,1"),
  ("037e", "c.slli t1,0x1f"),
  ("7fc00337", "lui t1,0x7fc00"),
  ("2305", "c.addiw t1,1"),
  ("7f800337", "lui t1,0x7f800"),
  ("1ff0031b", "addiw t1,zero,511"),
  ("4305", "c.li t1,1"),
  ("00800337", "lui t1,0x800"),
  ("337d", "c.addiw t1,-1"),
  ("082081d3", "fsub.s ft3,ft1,ft2,rne"),
  ("0820a1d3", "fsub.s ft3,ft1,ft2,rdn"),
  ("137d", "c.addi t1,-1"),
  ("0820b1d3", "fsub.s ft3,ft1,ft2,rup"),
  ("082091d3", "fsub.s ft3,ft1,ft2,rtz"),
  ("102081d3", "fmul.s ft3,ft1,ft2,rne"),
  ("1020b1d3", "fmul.s ft3,ft1,ft2,rup"),
  ("3f000337", "lui t1,0x3f000"),
  ("3fc00337", "lui t1,0x3fc00"),
  ("430d", "c.li t1,3"),
  ("4301", "c.li t1,0"),
  ("7fc0c337", "lui t1,0x7fc0c"),
  ("eef3031b", "addiw t1,t1,-273"),
  ("182081d3", "fdiv.s ft3,ft1,ft2,rne"),
  ("40400337", "lui t1,0x40400"),
  ("1820b1d3", "fdiv.s ft3,ft1,ft2,rup"),
  ("1820a1d3", "fdiv.s ft3,ft1,ft2,rdn"),
  ("182091d3", "fdiv.s ft3,ft1,ft2,rtz"),
  ("3ff0031b", "addiw t1,zero,1023"),
  ("035a", "c.slli t1,0x16"),
  ("580081d3", "fsqrt.s ft3,ft1,rne"),
  ("5800b1d3", "fsqrt.s ft3,ft1,rup"),
  ("40800337", "lui t1,0x40800"),
  ("5800a1d3", "fsqrt.s ft3,ft1,rdn"),
  ("0021d073", "csrrwi zero,frm,3"),
  ("0020f1d3", "fadd.s ft3,ft1,ft2"),
  ("00215073", "csrrwi zero,frm,2"),
  ("bff0031b", "addiw t1,zero,-1025"),
  ("1352", "c.slli t1,0x34"),
  ("f20300d3", "fmv.d.x ft1,t1"),
  ("de50031b", "addiw t1,zero,-539"),
  ("1356", "c.slli t1,0x35"),
  ("f2030153", "fmv.d.x ft2,t1"),
  ("0220f1d3", "fadd.d ft3,ft1,ft2"),
  ("0020d073", "csrrwi zero,frm,1"),
  ("1820f1d3", "fdiv.s ft3,ft1,ft2"),
  ("00201073", "csrrw zero,frm,zero"),
  ("137a", "c.slli t1,0x3e"),
  ("022081d3", "fadd.d ft3,ft1,ft2,rne"),
  ("3c30031b", "addiw t1,zero,963"),
  ("1e50031b", "addiw t1,zero,485"),
  ("0220b1d3", "fadd.d ft3,ft1,ft2,rup"),
  ("7970031b", "addiw t1,zero,1943"),
  ("134e", "c.slli t1,0x33"),
  ("6305", "c.lui t1,0x1"),
  ("7ff0031b", "addiw t1,zero,2047"),
  ("0a20a1d3", "fsub.d ft3,ft1,ft2,rdn"),
  ("0a2081d3", "fsub.d ft3,ft1,ft2,rne"),
  ("122081d3", "fmul.d ft3,ft1,ft2,rne"),
  ("122091d3", "fmul.d ft3,ft1,ft2,rtz"),
  ("1a2081d3", "fdiv.d ft3,ft1,ft2,rne"),
  ("8013031b", "addiw t1,t1,-2047"),
  ("1a20b1d3", "fdiv.d ft3,ft1,ft2,rup"),
  ("1a20a1d3", "fdiv.d ft3,ft1,ft2,rdn"),
  ("1a2091d3", "fdiv.d ft3,ft1,ft2,rtz"),
  ("5a0081d3", "fsqrt.d ft3,ft1,rne"),
  ("5a00a1d3", "fsqrt.d ft3,ft1,rdn"),
  ("137e", "c.slli t1,0x3f"),
  ("3379", "c.addiw t1,-2"),
  ("f0030253", "fmv.w.x ft4,t1"),
  ("202081c3", "fmadd.s ft3,ft1,ft2,ft4,rne"),
  ("202081c7", "fmsub.s ft3,ft1,ft2,ft4,rne"),
  ("202081cb", "fnmsub.s ft3,ft1,ft2,ft4,rne"),
  ("202081cf", "fnmadd.s ft3,ft1,ft2,ft4,rne"),
  ("202091c3", "fmadd.s ft3,ft1,ft2,ft4,rtz"),
  ("2020b1cf", "fnmadd.s ft3,ft1,ft2,ft4,rup"),
  ("2020a1cf", "fnmadd.s ft3,ft1,ft2,ft4,rdn"),
  ("2020a1c3", "fmadd.s ft3,ft1,ft2,ft4,rdn"),
  ("1379", "c.addi t1,-2"),
  ("f2030253", "fmv.d.x ft4,t1"),
  ("222081c3", "fmadd.d ft3,ft1,ft2,ft4,rne"),
  ("222081cb", "fnmsub.d ft3,ft1,ft2,ft4,rne"),
  ("2220b1cf", "fnmadd.d ft3,ft1,ft2,ft4,rup"),
  ("030d", "c.addi t1,3"),
  ("222081c7", "fmsub.d ft3,ft1,ft2,ft4,rne"),
  ("222081cf", "fnmadd.d ft3,ft1,ft2,ft4,rne"),
  ("6311", "c.lui t1,0x4"),
  ("232d", "c.addiw t1,11"),
  ("1342", "c.slli t1,0x30"),
  ("737d", "c.lui t1,0xfffff"),
  ("231d", "c.addiw t1,7"),
  ("134a", "c.slli t1,0x32"),
  ("282081d3", "fmin.s ft3,ft1,ft2"),
  ("282091d3", "fmax.s ft3,ft1,ft2"),
  ("2309", "c.addiw t1,2"),
  ("2a2081d3", "fmin.d ft3,ft1,ft2"),
  ("2a2091d3", "fmax.d ft3,ft1,ft2"),
  ("0309", "c.addi t1,2"),
  ("e0009553", "fclass.s a0,ft1"),
  ("e2009553", "fclass.d a0,ft1"),
  ("a020a553", "feq.s a0,ft1,ft2"),
  ("a0209553", "flt.s a0,ft1,ft2"),
  ("a0208553", "fle.s a0,ft1,ft2"),
  ("a220a553", "feq.d a0,ft1,ft2"),
  ("a2209553", "flt.d a0,ft1,ft2"),
  ("a2208553", "fle.d a0,ft1,ft2"),
  ("00000f17", "auipc t5,0x0"),
  ("414f0f13", "addi t5,t5,1044"),
  ("3fef0f13", "addi t5,t5,1022"),
  (* tests/fp-conv.S *)
  ("040d8d93", "addi s11,s11,64"),
  ("c0008553", "fcvt.w.s a0,ft1,rne"),
  ("2ff0031b", "addiw t1,zero,767"),
  ("c0009553", "fcvt.w.s a0,ft1,rtz"),
  ("c000a553", "fcvt.w.s a0,ft1,rdn"),
  ("c000b553", "fcvt.w.s a0,ft1,rup"),
  ("40200337", "lui t1,0x40200"),
  ("4f32d337", "lui t1,0x4f32d"),
  ("05e3031b", "addiw t1,t1,94"),
  ("000cf337", "lui t1,0xcf"),
  ("32d3031b", "addiw t1,t1,813"),
  ("0332", "c.slli t1,0xc"),
  ("05e30313", "addi t1,t1,94"),
  ("0cf0031b", "addiw t1,zero,207"),
  ("0362", "c.slli t1,0x18"),
  ("4f000337", "lui t1,0x4f000"),
  ("c0108553", "fcvt.wu.s a0,ft1,rne"),
  ("4f800337", "lui t1,0x4f800"),
  ("0bf0031b", "addiw t1,zero,191"),
  ("c0109553", "fcvt.wu.s a0,ft1,rtz"),
  ("c010a553", "fcvt.wu.s a0,ft1,rdn"),
  ("c010b553", "fcvt.wu.s a0,ft1,rup"),
  ("5f000337", "lui t1,0x5f000"),
  ("c0208553", "fcvt.l.s a0,ft1,rne"),
  ("0df0031b", "addiw t1,zero,223"),
  ("3fa00337", "lui t1,0x3fa00"),
  ("c020b553", "fcvt.l.s a0,ft1,rup"),
  ("5f800337", "lui t1,0x5f800"),
  ("c0308553", "fcvt.lu.s a0,ft1,rne"),
  ("e0f0031b", "addiw t1,zero,-497"),
  ("1306", "c.slli t1,0x21"),
  ("0352", "c.slli t1,0x14"),
  ("c2009553", "fcvt.w.d a0,ft1,rtz"),
  ("c200a553", "fcvt.w.d a0,ft1,rdn"),
  ("20f0031b", "addiw t1,zero,527"),
  ("0356", "c.slli t1,0x15"),
  ("c2008553", "fcvt.w.d a0,ft1,rne"),
  ("41f0031b", "addiw t1,zero,1055"),
  ("c2108553", "fcvt.wu.d a0,ft1,rne"),
  ("c2109553", "fcvt.wu.d a0,ft1,rtz"),
  ("c2208553", "fcvt.l.d a0,ft1,rne"),
  ("e1f0031b", "addiw t1,zero,-481"),
  ("21f0031b", "addiw t1,zero,543"),
  ("7301", "c.lui t1,0xfffe0"),
  ("1b13031b", "addiw t1,t1,433"),
  ("1336", "c.slli t1,0x2d"),
  ("c2209553", "fcvt.l.d a0,ft1,rtz"),
  ("43f0031b", "addiw t1,zero,1087"),
  ("c2308553", "fcvt.lu.d a0,ft1,rne"),
  ("0220b337", "lui t1,0x220b"),
  ("d793031b", "addiw t1,t1,-647"),
  ("0336", "c.slli t1,0xd"),
  ("d7930313", "addi t1,t1,-647"),
  ("b5930313", "addi t1,t1,-1191"),
  ("c4030313", "addi t1,t1,-960"),
  ("dff0031b", "addiw t1,zero,-513"),
  ("c230b553", "fcvt.lu.d a0,ft1,rup"),
  ("01000337", "lui t1,0x1000"),
  ("d00301d3", "fcvt.s.w ft3,t1,rne"),
  ("d00331d3", "fcvt.s.w ft3,t1,rup"),
  ("12345337", "lui t1,0x12345"),
  ("6793031b", "addiw t1,t1,1657"),
  ("d00321d3", "fcvt.s.w ft3,t1,rdn"),
  ("80000337", "lui t1,0x80000"),
  ("d01301d3", "fcvt.s.wu ft3,t1,rne"),
  ("d01311d3", "fcvt.s.wu ft3,t1,rtz"),
  ("537d", "c.li t1,-1"),
  ("d02301d3", "fcvt.s.l ft3,t1,rne"),
  ("ff000337", "lui t1,0xff000"),
  ("d02331d3", "fcvt.s.l ft3,t1,rup"),
  ("d03301d3", "fcvt.s.lu ft3,t1,rne"),
  ("d03311d3", "fcvt.s.lu ft3,t1,rtz"),
  ("131e", "c.slli t1,0x27"),
  ("d03331d3", "fcvt.s.lu ft3,t1,rup"),
  ("d03321d3", "fcvt.s.lu ft3,t1,rdn"),
  ("230d", "c.addiw t1,3"),
  ("536d", "c.li t1,-5"),
  ("d20301d3", "fcvt.d.w ft3,t1"),
  ("d21301d3", "fcvt.d.wu ft3,t1"),
  ("d22301d3", "fcvt.d.l ft3,t1,rne"),
  ("d22331d3", "fcvt.d.l ft3,t1,rup"),
  ("d22321d3", "fcvt.d.l ft3,t1,rdn"),
  ("fd2d5337", "lui t1,0xfd2d5"),
  ("2d33031b", "addiw t1,t1,723"),
  ("d2d30313", "addi t1,t1,-723"),
  ("2d330313", "addi t1,t1,723"),
  ("a5b30313", "addi t1,t1,-1445"),
  ("d22311d3", "fcvt.d.l ft3,t1,rtz"),
  ("d23301d3", "fcvt.d.lu ft3,t1,rne"),
  ("d23321d3", "fcvt.d.lu ft3,t1,rdn"),
  ("d23331d3", "fcvt.d.lu ft3,t1,rup"),
  ("01fdd337", "lui t1,0x1fdd"),
  ("ccd3031b", "addiw t1,t1,-819"),
  ("ccd30313", "addi t1,t1,-819"),
  ("99a30313", "addi t1,t1,-1638"),
  ("401081d3", "fcvt.s.d ft3,ft1,rne"),
  ("401091d3", "fcvt.s.d ft3,ft1,rtz"),
  ("001f9337", "lui t1,0x1f9"),
  ("df93031b", "addiw t1,t1,-519"),
  ("033e", "c.slli t1,0xf"),
  ("79130313", "addi t1,t1,1937"),
  ("59c30313", "addi t1,t1,1436"),
  ("000d3337", "lui t1,0xd3"),
  ("b713031b", "addiw t1,t1,-1167"),
  ("fc330313", "addi t1,t1,-61"),
  ("f8f30313", "addi t1,t1,-113"),
  ("35930313", "addi t1,t1,857"),
  ("4010b1d3", "fcvt.s.d ft3,ft1,rup"),
  ("fc0d3337", "lui t1,0xfc0d3"),
  ("3810031b", "addiw t1,zero,897"),
  ("0366", "c.slli t1,0x19"),
  ("036e", "c.slli t1,0x1b"),
  ("47f0031b", "addiw t1,zero,1151"),
  ("0372", "c.slli t1,0x1c"),
  ("0376", "c.slli t1,0x1d"),
  ("420081d3", "fcvt.d.s ft3,ft1"),
  ("00080337", "lui t1,0x80"),
  ("e093031b", "addiw t1,t1,-503"),
  ("34530313", "addi t1,t1,837"),
  ("0b840413", "addi s0,s0,184"),
  ("00042287", "flw ft5,0(s0)"),
  ("e2028553", "fmv.x.d a0,ft5"),
  ("00542827", "fsw ft5,16(s0)"),
  ("6808", "c.ld a0,16(s0)"),
  ("00442307", "flw ft6,4(s0)"),
  ("e0030553", "fmv.x.w a0,ft6"),
  ("00843387", "fld ft7,8(s0)"),
  ("e0038553", "fmv.x.w a0,ft7"),
  ("00742c27", "fsw ft7,24(s0)"),
  ("4c08", "c.lw a0,24(s0)"),
  ("0073f453", "fadd.s fs0,ft7,ft7"),
  ("e2040553", "fmv.x.d a0,fs0"),
  ("205384d3", "fsgnj.s fs1,ft7,ft5"),
  ("e2048553", "fmv.x.d a0,fs1"),
  ("205294d3", "fsgnjn.s fs1,ft5,ft5"),
  ("206324d3", "fsgnjx.s fs1,ft6,ft6"),
  ("02469337", "lui t1,0x2469"),
  ("acf3031b", "addiw t1,t1,-1329"),
  ("3ff30313", "addi t1,t1,1023"),
  ("f0030553", "fmv.w.x fa0,t1"),
  ("e2050553", "fmv.x.d a0,fa0"),
  ("b008", "c.fsd fa0,32(s0)"),
  ("7008", "c.ld a0,32(s0)"),
  ("e0050553", "fmv.x.w a0,fa0"),
  ("22a505d3", "fsgnj.d fa1,fa0,fa0"),
  ("e2058553", "fmv.x.d a0,fa1"),
  ("d0007653", "fcvt.s.w fa2,zero"),
  ("848a", "c.mv s1,sp"),
  ("8122", "c.mv sp,s0"),
  ("26a2", "c.fldsp fa3,8(sp)"),
  ("b436", "c.fsdsp fa3,40(sp)"),
  ("8126", "c.mv sp,s1"),
  ("2418", "c.fld fa4,8(s0)"),
  ("b818", "c.fsd fa4,48(s0)"),
  ("7408", "c.ld a0,40(s0)"),
  ("7808", "c.ld a0,48(s0)"),
  ("428d", "c.li t0,3"),
  ("00229073", "csrrw zero,frm,t0"),
  ("00302573", "csrrs a0,fcsr,zero"),
  ("00102573", "csrrs a0,fflags,zero"),
  ("00202573", "csrrs a0,frm,zero"),
  ("42fd", "c.li t0,31"),
  ("00129073", "csrrw zero,fflags,t0"),
  ("f3ef0f13", "addi t5,t5,-194"),
  ("f28f0f13", "addi t5,t5,-216"),
  (* tests/fp-rmm.S *)
  ("411d", "c.li sp,7"),
  ("420140d3", ".word 0x420140d3"),
  ("e2008553", "fmv.x.d a0,ft1"),
  ("d20140d3", ".word 0xd20140d3"),
  ("517d", "c.li sp,-1"),
  ("d21140d3", ".word 0xd21140d3"),
  ("4291", "c.li t0,4"),
  ("000c0337", "lui t1,0xc0"),
  ("4913031b", "addiw t1,t1,1169"),
  ("fdb30313", "addi t1,t1,-37"),
  ("420170d3", ".word 0x420170d3"),
  ("0010011b", "addiw sp,zero,1"),
  ("017e", "c.slli sp,0x1f"),
  ("d20170d3", ".word 0xd20170d3"),
  ("f00301d3", "fmv.w.x ft3,t1"),
  ("003140d3", ".word 0x003140d3"),
  ("f0cf0f13", "addi t5,t5,-244"),
  ("ef6f0f13", "addi t5,t5,-266"),
  (* tests/fsoff-all.S *)
  ("010d8d93", "addi s11,s11,16"),
  ("1ae28293", "addi t0,t0,430"),
  ("30529073", "csrrw zero,mtvec,t0"),
  ("fea40413", "addi s0,s0,-22"),
  ("4481", "c.li s1,0"),
  ("6599", "c.lui a1,0x6"),
  ("a5a5859b", "addiw a1,a1,-1446"),
  ("6605", "c.lui a2,0x1"),
  ("2346061b", "addiw a2,a2,564"),
  ("00042087", "flw ft1,0(s0)"),
  ("00043087", "fld ft1,0(s0)"),
  ("00142027", "fsw ft1,0(s0)"),
  ("00143027", "fsd ft1,0(s0)"),
  ("00143087", "fld ft1,1(s0)"),
  ("001431a7", "fsd ft1,3(s0)"),
  ("203170c3", "fmadd.s ft1,ft2,ft3,ft4"),
  ("203170c7", "fmsub.s ft1,ft2,ft3,ft4"),
  ("203170cb", "fnmsub.s ft1,ft2,ft3,ft4"),
  ("203170cf", "fnmadd.s ft1,ft2,ft3,ft4"),
  ("003170d3", "fadd.s ft1,ft2,ft3"),
  ("083170d3", "fsub.s ft1,ft2,ft3"),
  ("103170d3", "fmul.s ft1,ft2,ft3"),
  ("183170d3", "fdiv.s ft1,ft2,ft3"),
  ("580170d3", "fsqrt.s ft1,ft2"),
  ("203100d3", "fsgnj.s ft1,ft2,ft3"),
  ("203110d3", "fsgnjn.s ft1,ft2,ft3"),
  ("203120d3", "fsgnjx.s ft1,ft2,ft3"),
  ("283100d3", "fmin.s ft1,ft2,ft3"),
  ("283110d3", "fmax.s ft1,ft2,ft3"),
  ("a03125d3", "feq.s a1,ft2,ft3"),
  ("a03115d3", "flt.s a1,ft2,ft3"),
  ("a03105d3", "fle.s a1,ft2,ft3"),
  ("c00175d3", "fcvt.w.s a1,ft2"),
  ("c01175d3", "fcvt.wu.s a1,ft2"),
  ("e00105d3", "fmv.x.w a1,ft2"),
  ("e00115d3", "fclass.s a1,ft2"),
  ("d00670d3", "fcvt.s.w ft1,a2"),
  ("d01670d3", "fcvt.s.wu ft1,a2"),
  ("f00600d3", "fmv.w.x ft1,a2"),
  ("c02175d3", "fcvt.l.s a1,ft2"),
  ("c03175d3", "fcvt.lu.s a1,ft2"),
  ("d02670d3", "fcvt.s.l ft1,a2"),
  ("d03670d3", "fcvt.s.lu ft1,a2"),
  ("223170c3", "fmadd.d ft1,ft2,ft3,ft4"),
  ("223170c7", "fmsub.d ft1,ft2,ft3,ft4"),
  ("223170cb", "fnmsub.d ft1,ft2,ft3,ft4"),
  ("223170cf", "fnmadd.d ft1,ft2,ft3,ft4"),
  ("023170d3", "fadd.d ft1,ft2,ft3"),
  ("0a3170d3", "fsub.d ft1,ft2,ft3"),
  ("123170d3", "fmul.d ft1,ft2,ft3"),
  ("1a3170d3", "fdiv.d ft1,ft2,ft3"),
  ("5a0170d3", "fsqrt.d ft1,ft2"),
  ("223100d3", "fsgnj.d ft1,ft2,ft3"),
  ("223110d3", "fsgnjn.d ft1,ft2,ft3"),
  ("223120d3", "fsgnjx.d ft1,ft2,ft3"),
  ("2a3100d3", "fmin.d ft1,ft2,ft3"),
  ("2a3110d3", "fmax.d ft1,ft2,ft3"),
  ("a23125d3", "feq.d a1,ft2,ft3"),
  ("a23115d3", "flt.d a1,ft2,ft3"),
  ("a23105d3", "fle.d a1,ft2,ft3"),
  ("c20175d3", "fcvt.w.d a1,ft2"),
  ("c21175d3", "fcvt.wu.d a1,ft2"),
  ("e20115d3", "fclass.d a1,ft2"),
  ("d20600d3", "fcvt.d.w ft1,a2"),
  ("d21600d3", "fcvt.d.wu ft1,a2"),
  ("c22175d3", "fcvt.l.d a1,ft2"),
  ("c23175d3", "fcvt.lu.d a1,ft2"),
  ("d22670d3", "fcvt.d.l ft1,a2"),
  ("d23670d3", "fcvt.d.lu ft1,a2"),
  ("e20105d3", "fmv.x.d a1,ft2"),
  ("f20600d3", "fmv.d.x ft1,a2"),
  ("401170d3", "fcvt.s.d ft1,ft2"),
  ("420100d3", "fcvt.d.s ft1,ft2"),
  ("001025f3", "csrrs a1,fflags,zero"),
  ("002025f3", "csrrs a1,frm,zero"),
  ("003025f3", "csrrs a1,fcsr,zero"),
  ("00161073", "csrrw zero,fflags,a2"),
  ("00261073", "csrrw zero,frm,a2"),
  ("00361073", "csrrw zero,fcsr,a2"),
  ("0010e073", "csrrsi zero,fflags,1"),
  ("0030f073", "csrrci zero,fcsr,1"),
  ("0020d5f3", "csrrwi a1,frm,1"),
  ("00163073", "csrrc zero,fflags,a2"),
  ("00262073", "csrrs zero,frm,a2"),
  ("2000", "c.fld fs0,0(s0)"),
  ("a000", "c.fsd fs0,0(s0)"),
  ("2082", "c.fldsp ft1,0(sp)"),
  ("a006", "c.fsdsp ft1,0(sp)"),
  ("04f00f93", "addi t6,zero,79"),
  ("0bf49263", "bne s1,t6,8000020c"),
  ("6f99", "c.lui t6,0x6"),
  ("a5af8f9b", "addiw t6,t6,-1446"),
  ("09f59c63", "bne a1,t6,8000020c"),
  ("300022f3", "csrrs t0,mstatus,zero"),
  ("00d2d293", "srli t0,t0,0xd"),
  ("0032f293", "andi t0,t0,3"),
  ("09f29263", "bne t0,t6,8000020c"),
  ("00043283", "ld t0,0(s0)"),
  ("00092fb7", "lui t6,0x92"),
  ("a2bf8f9b", "addiw t6,t6,-1493"),
  ("3c5f8f93", "addi t6,t6,965"),
  ("abdf8f93", "addi t6,t6,-1347"),
  ("deff8f93", "addi t6,t6,-529"),
  ("07f29063", "bne t0,t6,8000020c"),
  ("009db023", "sd s1,0(s11)"),
  ("a099", "c.j 800001fc"),
  ("342022f3", "csrrs t0,mcause,zero"),
  ("4309", "c.li t1,2"),
  ("06448193", "addi gp,s1,100"),
  ("04629563", "bne t0,t1,8000020c"),
  ("341022f3", "csrrs t0,mepc,zero"),
  ("0002d303", "lhu t1,0(t0)"),
  ("00337393", "andi t2,t1,3"),
  ("4e0d", "c.li t3,3"),
  ("01c39863", "bne t2,t3,800001e4"),
  ("0022d383", "lhu t2,2(t0)"),
  ("03c2", "c.slli t2,0x10"),
  ("00736333", "or t1,t1,t2"),
  ("0289", "c.addi t0,2"),
  ("343023f3", "csrrs t2,mtval,zero"),
  ("0c848193", "addi gp,s1,200"),
  ("00731f63", "bne t1,t2,8000020c"),
  ("34129073", "csrrw zero,mepc,t0"),
  ("0485", "c.addi s1,1"),
  ("30200073", "mret"),
  ("e02f0f13", "addi t5,t5,-510"),
  ("decf0f13", "addi t5,t5,-532"),
  (* tests/smode.S *)
  ("00001297", "auipc t0,0x1"),
  ("df428293", "addi t0,t0,-524"),
  ("dfc28293", "addi t0,t0,-516"),
  ("10529073", "csrrw zero,stvec,t0"),
  ("03529293", "slli t0,t0,0x35"),
  ("fff28293", "addi t0,t0,-1"),
  ("3b029073", "csrrw zero,pmpaddr0,t0"),
  ("01f00293", "addi t0,zero,31"),
  ("3a029073", "csrrw zero,pmpcfg0,t0"),
  ("000212b7", "lui t0,0x21"),
  ("8002829b", "addiw t0,t0,-2048"),
  ("30029073", "csrrw zero,mstatus,t0"),
  ("01828293", "addi t0,t0,24"),
  ("00000d17", "auipc s10,0x0"),
  ("010d0d13", "addi s10,s10,16"),
  ("00000073", "ecall"),
  ("00900f93", "addi t6,zero,9"),
  ("55f514e3", "bne a0,t6,80000dbc"),
  ("00000f97", "auipc t6,0x0"),
  ("fe4f8f93", "addi t6,t6,-28"),
  ("53f59ce3", "bne a1,t6,80000dbc"),
  ("53f616e3", "bne a2,t6,80000dbc"),
  ("00022fb7", "lui t6,0x22"),
  ("800f8f9b", "addiw t6,t6,-2048"),
  ("01f6ffb3", "and t6,a3,t6"),
  ("00001f37", "lui t5,0x1"),
  ("800f0f1b", "addiw t5,t5,-2048"),
  ("51ef94e3", "bne t6,t5,80000dbc"),
  ("20000293", "addi t0,zero,512"),
  ("30229073", "csrrw zero,medeleg,t0"),
  ("000012b7", "lui t0,0x1"),
  ("8022829b", "addiw t0,t0,-2046"),
  ("00300f93", "addi t6,zero,3"),
  ("4df516e3", "bne a0,t6,80000dbc"),
  ("012db023", "sd s2,0(s11)"),
  ("4bf91ce3", "bne s2,t6,80000dbc"),
  ("fd8f8f93", "addi t6,t6,-40"),
  ("4bf994e3", "bne s3,t6,80000dbc"),
  ("49fa1ee3", "bne s4,t6,80000dbc"),
  ("015db023", "sd s5,0(s11)"),
  ("12200f93", "addi t6,zero,290"),
  ("01faffb3", "and t6,s5,t6"),
  ("12000f13", "addi t5,zero,288"),
  ("49ef90e3", "bne t6,t5,80000dbc"),
  ("30201073", "csrrw zero,medeleg,zero"),
  ("fff00293", "addi t0,zero,-1"),
  ("30202573", "csrrs a0,medeleg,zero"),
  ("0000bfb7", "lui t6,0xb"),
  ("3fff8f9b", "addiw t6,t6,1023"),
  ("45f51ce3", "bne a0,t6,80000dbc"),
  ("30329073", "csrrw zero,mideleg,t0"),
  ("30302573", "csrrs a0,mideleg,zero"),
  ("22200f93", "addi t6,zero,546"),
  ("43f51ee3", "bne a0,t6,80000dbc"),
  ("30301073", "csrrw zero,mideleg,zero"),
  ("00200293", "addi t0,zero,2"),
  ("30429073", "csrrw zero,mie,t0"),
  ("10402573", "csrrs a0,sie,zero"),
  ("41f51ee3", "bne a0,t6,80000dbc"),
  ("10429073", "csrrw zero,sie,t0"),
  ("30402573", "csrrs a0,mie,zero"),
  ("00200f93", "addi t6,zero,2"),
  ("41f512e3", "bne a0,t6,80000dbc"),
  ("22200293", "addi t0,zero,546"),
  ("3ff516e3", "bne a0,t6,80000dbc"),
  ("3df516e3", "bne a0,t6,80000dbc"),
  ("10401073", "csrrw zero,sie,zero"),
  ("3bf51ce3", "bne a0,t6,80000dbc"),
  ("34416073", "csrrsi zero,mip,2"),
  ("14402573", "csrrs a0,sip,zero"),
  ("3bf510e3", "bne a0,t6,80000dbc"),
  ("14401073", "csrrw zero,sip,zero"),
  ("34402573", "csrrs a0,mip,zero"),
  ("01f57fb3", "and t6,a0,t6"),
  ("00200f13", "addi t5,zero,2"),
  ("39ef92e3", "bne t6,t5,80000dbc"),
  ("37f512e3", "bne a0,t6,80000dbc"),
  ("22000293", "addi t0,zero,544"),
  ("1442a073", "csrrs zero,sip,t0"),
  ("35f516e3", "bne a0,t6,80000dbc"),
  ("14417073", "csrrci zero,sip,2"),
  ("00000f13", "addi t5,zero,0"),
  ("33ef98e3", "bne t6,t5,80000dbc"),
  ("00000b13", "addi s6,zero,0"),
  ("2ff514e3", "bne a0,t6,80000dbc"),
  ("01700193", "addi gp,zero,23"),
  ("03ff9f93", "slli t6,t6,0x3f"),
  ("001f8f93", "addi t6,t6,1"),
  ("2df916e3", "bne s2,t6,80000dbc"),
  ("01800193", "addi gp,zero,24"),
  ("fd0f8f93", "addi t6,t6,-48"),
  ("2bf99ee3", "bne s3,t6,80000dbc"),
  ("01900193", "addi gp,zero,25"),
  ("2bfa18e3", "bne s4,t6,80000dbc"),
  ("01a00193", "addi gp,zero,26"),
  ("29ef9ee3", "bne t6,t5,80000dbc"),
  ("01b00193", "addi gp,zero,27"),
  ("29fb18e3", "bne s6,t6,80000dbc"),
  ("b1028293", "addi t0,t0,-1264"),
  ("0012e293", "ori t0,t0,1"),
  ("01c00193", "addi gp,zero,28"),
  ("25f514e3", "bne a0,t6,80000dbc"),
  ("01d00193", "addi gp,zero,29"),
  ("23f91ae3", "bne s2,t6,80000dbc"),
  ("01e00193", "addi gp,zero,30"),
  ("23f992e3", "bne s3,t6,80000dbc"),
  ("016db023", "sd s6,0(s11)"),
  ("01f00193", "addi gp,zero,31"),
  ("05100f93", "addi t6,zero,81"),
  ("21fb18e3", "bne s6,t6,80000dbc"),
  ("34417073", "csrrci zero,mip,2"),
  ("1df916e3", "bne s2,t6,80000dbc"),
  ("05000f93", "addi t6,zero,80"),
  ("1dfb10e3", "bne s6,t6,80000dbc"),
  ("a1028293", "addi t0,t0,-1520"),
  ("17f512e3", "bne a0,t6,80000dbc"),
  ("fdcf8f93", "addi t6,t6,-36"),
  ("15f59ae3", "bne a1,t6,80000dbc"),
  ("13ef9ce3", "bne t6,t5,80000dbc"),
  ("0ff51ce3", "bne a0,t6,80000dbc"),
  ("0ff912e3", "bne s2,t6,80000dbc"),
  ("0def98e3", "bne t6,t5,80000dbc"),
  ("30401073", "csrrw zero,mie,zero"),
  ("004202b7", "lui t0,0x420"),
  ("0202829b", "addiw t0,t0,32"),
  ("14129073", "csrrw zero,sepc,t0"),
  ("10200073", "sret"),
  ("00800f93", "addi t6,zero,8"),
  ("09f514e3", "bne a0,t6,80000dbc"),
  ("07f59ce3", "bne a1,t6,80000dbc"),
  ("922f8f9b", "addiw t6,t6,-1758"),
  ("02200f13", "addi t5,zero,34"),
  ("05ef9ce3", "bne t6,t5,80000dbc"),
  ("10000293", "addi t0,zero,256"),
  ("03f514e3", "bne a0,t6,80000dbc"),
  ("fecf8f93", "addi t6,t6,-20"),
  ("01f59ce3", "bne a1,t6,80000dbc"),
  ("004012b7", "lui t0,0x401"),
  ("7df51e63", "bne a0,t6,80000dbc"),
  ("7df59663", "bne a1,t6,80000dbc"),
  ("10200fb7", "lui t6,0x10200"),
  ("073f8f9b", "addiw t6,t6,115"),
  ("7bf61e63", "bne a2,t6,80000dbc"),
  ("03428293", "addi t0,t0,52"),
  ("014d0d13", "addi s10,s10,20"),
  ("77f51c63", "bne a0,t6,80000dbc"),
  ("77f59463", "bne a1,t6,80000dbc"),
  ("75ef9863", "bne t6,t5,80000dbc"),
  ("03828293", "addi t0,t0,56"),
  ("9002829b", "addiw t0,t0,-1792"),
  ("018d0d13", "addi s10,s10,24"),
  ("71f51463", "bne a0,t6,80000dbc"),
  ("6ff59c63", "bne a1,t6,80000dbc"),
  ("002002b7", "lui t0,0x200"),
  ("00000b93", "addi s7,zero,0"),
  ("10500073", "wfi"),
  ("00100b93", "addi s7,zero,1"),
  ("6dfb9c63", "bne s7,t6,80000dbc"),
  ("30001073", "csrrw zero,mstatus,zero"),
  ("002012b7", "lui t0,0x201"),
  ("03600193", "addi gp,zero,54"),
  ("69f51663", "bne a0,t6,80000dbc"),
  ("03700193", "addi gp,zero,55"),
  ("67f59e63", "bne a1,t6,80000dbc"),
  ("03800193", "addi gp,zero,56"),
  ("10500fb7", "lui t6,0x10500"),
  ("67f61663", "bne a2,t6,80000dbc"),
  ("03900193", "addi gp,zero,57"),
  ("63f51463", "bne a0,t6,80000dbc"),
  ("03a00193", "addi gp,zero,58"),
  ("61f59c63", "bne a1,t6,80000dbc"),
  ("10016073", "csrrsi zero,sstatus,2"),
  ("03b00193", "addi gp,zero,59"),
  ("5df51e63", "bne a0,t6,80000dbc"),
  ("03c00193", "addi gp,zero,60"),
  ("5df91463", "bne s2,t6,80000dbc"),
  ("03d00193", "addi gp,zero,61"),
  ("5bf99c63", "bne s3,t6,80000dbc"),
  ("03e00193", "addi gp,zero,62"),
  ("57f51e63", "bne a0,t6,80000dbc"),
  ("03f00193", "addi gp,zero,63"),
  ("57f61663", "bne a2,t6,80000dbc"),
  ("04000193", "addi gp,zero,64"),
  ("ff8f8f93", "addi t6,t6,-8"),
  ("53f59863", "bne a1,t6,80000dbc"),
  ("30629073", "csrrw zero,mcounteren,t0"),
  ("30602573", "csrrs a0,mcounteren,zero"),
  ("04100193", "addi gp,zero,65"),
  ("00700f93", "addi t6,zero,7"),
  ("51f51c63", "bne a0,t6,80000dbc"),
  ("10629073", "csrrw zero,scounteren,t0"),
  ("10602573", "csrrs a0,scounteren,zero"),
  ("04200193", "addi gp,zero,66"),
  ("51f51263", "bne a0,t6,80000dbc"),
  ("30601073", "csrrw zero,mcounteren,zero"),
  ("c0002773", "csrrs a4,cycle,zero"),
  ("04300193", "addi gp,zero,67"),
  ("4df51263", "bne a0,t6,80000dbc"),
  ("04400193", "addi gp,zero,68"),
  ("00060fb7", "lui t6,0x60"),
  ("001f8f9b", "addiw t6,t6,1"),
  ("773f8f93", "addi t6,t6,1907"),
  ("4bf61663", "bne a2,t6,80000dbc"),
  ("00100293", "addi t0,zero,1"),
  ("c0102773", "csrrs a4,time,zero"),
  ("04500193", "addi gp,zero,69"),
  ("47f51263", "bne a0,t6,80000dbc"),
  ("04600193", "addi gp,zero,70"),
  ("45f59a63", "bne a1,t6,80000dbc"),
  ("04700193", "addi gp,zero,71"),
  ("45fb9463", "bne s7,t6,80000dbc"),
  ("00700293", "addi t0,zero,7"),
  ("04800193", "addi gp,zero,72"),
  ("3ff51e63", "bne a0,t6,80000dbc"),
  ("04900193", "addi gp,zero,73"),
  ("3ff59663", "bne a1,t6,80000dbc"),
  ("04a00193", "addi gp,zero,74"),
  ("3ffb9063", "bne s7,t6,80000dbc"),
  ("c0202773", "csrrs a4,instret,zero"),
  ("04b00193", "addi gp,zero,75"),
  ("3bf51863", "bne a0,t6,80000dbc"),
  ("00500293", "addi t0,zero,5"),
  ("04c00193", "addi gp,zero,76"),
  ("37f51263", "bne a0,t6,80000dbc"),
  ("04d00193", "addi gp,zero,77"),
  ("35f59a63", "bne a1,t6,80000dbc"),
  ("04e00193", "addi gp,zero,78"),
  ("35fb9463", "bne s7,t6,80000dbc"),
  ("10601073", "csrrw zero,scounteren,zero"),
  ("14229073", "csrrw zero,scause,t0"),
  ("14202573", "csrrs a0,scause,zero"),
  ("04f00193", "addi gp,zero,79"),
  ("01f00f93", "addi t6,zero,31"),
  ("33f51463", "bne a0,t6,80000dbc"),
  ("02000293", "addi t0,zero,32"),
  ("05000193", "addi gp,zero,80"),
  ("31f51863", "bne a0,t6,80000dbc"),
  ("03f29293", "slli t0,t0,0x3f"),
  ("00528293", "addi t0,t0,5"),
  ("05100193", "addi gp,zero,81"),
  ("005f8f93", "addi t6,t6,5"),
  ("2ff51463", "bne a0,t6,80000dbc"),
  ("01f28293", "addi t0,t0,31"),
  ("05200193", "addi gp,zero,82"),
  ("01ff8f93", "addi t6,t6,31"),
  ("04028293", "addi t0,t0,64"),
  ("05300193", "addi gp,zero,83"),
  ("29f51863", "bne a0,t6,80000dbc"),
  ("05400193", "addi gp,zero,84"),
  ("27f51463", "bne a0,t6,80000dbc"),
  ("01cd0d13", "addi s10,s10,28"),
  ("01300293", "addi t0,zero,19"),
  ("142027f3", "csrrs a5,scause,zero"),
  ("05500193", "addi gp,zero,85"),
  ("01300f93", "addi t6,zero,19"),
  ("23f79463", "bne a5,t6,80000dbc"),
  ("00400293", "addi t0,zero,4"),
  ("14301073", "csrrw zero,stval,zero"),
  ("30002773", "csrrs a4,mstatus,zero"),
  ("05600193", "addi gp,zero,86"),
  ("1ff51463", "bne a0,t6,80000dbc"),
  ("05700193", "addi gp,zero,87"),
  ("1df91a63", "bne s2,t6,80000dbc"),
  ("05800193", "addi gp,zero,88"),
  ("1df99263", "bne s3,t6,80000dbc"),
  ("014db023", "sd s4,0(s11)"),
  ("05900193", "addi gp,zero,89"),
  ("30002fb7", "lui t6,0x30002"),
  ("773f8f9b", "addiw t6,t6,1907"),
  ("1bfa1663", "bne s4,t6,80000dbc"),
  ("001002b7", "lui t0,0x100"),
  ("18001073", "csrrw zero,satp,zero"),
  ("18002573", "csrrs a0,satp,zero"),
  ("12000073", "sfence.vma zero,zero"),
  ("05a00193", "addi gp,zero,90"),
  ("19f51463", "bne a0,t6,80000dbc"),
  ("001012b7", "lui t0,0x101"),
  ("18002773", "csrrs a4,satp,zero"),
  ("05b00193", "addi gp,zero,91"),
  ("15f51463", "bne a0,t6,80000dbc"),
  ("05c00193", "addi gp,zero,92"),
  ("13f59c63", "bne a1,t6,80000dbc"),
  ("05d00193", "addi gp,zero,93"),
  ("18002fb7", "lui t6,0x18002"),
  ("13f61463", "bne a2,t6,80000dbc"),
  ("05e00193", "addi gp,zero,94"),
  ("0ff51a63", "bne a0,t6,80000dbc"),
  ("05f00193", "addi gp,zero,95"),
  ("0df51063", "bne a0,t6,80000dbc"),
  ("06000193", "addi gp,zero,96"),
  ("12000fb7", "lui t6,0x12000"),
  ("0bf61863", "bne a2,t6,80000dbc"),
  ("028d0d13", "addi s10,s10,40"),
  ("180027f3", "csrrs a5,satp,zero"),
  ("12528073", "sfence.vma t0,t0"),
  ("06100193", "addi gp,zero,97"),
  ("07f51063", "bne a0,t6,80000dbc"),
  ("06200193", "addi gp,zero,98"),
  ("05f79a63", "bne a5,t6,80000dbc"),
  ("06300193", "addi gp,zero,99"),
  ("05fb9463", "bne s7,t6,80000dbc"),
  ("06400193", "addi gp,zero,100"),
  ("01f51c63", "bne a0,t6,80000dbc"),
  ("254f0f13", "addi t5,t5,596"),
  ("23cf0f13", "addi t5,t5,572"),
  ("34202573", "csrrs a0,mcause,zero"),
  ("341025f3", "csrrs a1,mepc,zero"),
  ("34302673", "csrrs a2,mtval,zero"),
  ("300026f3", "csrrs a3,mstatus,zero"),
  ("000d0067", "jalr zero,0(s10)"),
  ("14202973", "csrrs s2,scause,zero"),
  ("141029f3", "csrrs s3,sepc,zero"),
  ("14302a73", "csrrs s4,stval,zero"),
  ("10002af3", "csrrs s5,sstatus,zero"),
  ("00100073", "ebreak"),
  ("00000013", "addi zero,zero,0"),
  ("0280006f", "jal zero,80000e68"),
  ("02c0006f", "jal zero,80000e70"),
  ("0300006f", "jal zero,80000e78"),
  ("0240006f", "jal zero,80000e78"),
  ("0200006f", "jal zero,80000e78"),
  ("01c0006f", "jal zero,80000e78"),
  ("0180006f", "jal zero,80000e78"),
  ("0140006f", "jal zero,80000e78"),
  ("05000b13", "addi s6,zero,80"),
  ("fa9ff06f", "jal zero,80000e14"),
  ("05100b13", "addi s6,zero,81"),
  ("fa1ff06f", "jal zero,80000e14"),
  ("00001b37", "lui s6,0x1"),
  ("badb0b1b", "addiw s6,s6,-1107"),
  ("f95ff06f", "jal zero,80000e14"),
  (* tests/sv39.S *)
  ("0000cd97", "auipc s11,0xc"),
  ("00002297", "auipc t0,0x2"),
  ("ee428293", "addi t0,t0,-284"),
  ("eec28293", "addi t0,t0,-276"),
  ("00006297", "auipc t0,0x6"),
  ("fdc28293", "addi t0,t0,-36"),
  ("0022d293", "srli t0,t0,0x2"),
  ("1ff2e293", "ori t0,t0,511"),
  ("00008297", "auipc t0,0x8"),
  ("fc828293", "addi t0,t0,-56"),
  ("3b129073", "csrrw zero,pmpaddr1,t0"),
  ("3b229073", "csrrw zero,pmpaddr2,t0"),
  ("001f22b7", "lui t0,0x1f2"),
  ("8182829b", "addiw t0,t0,-2024"),
  ("00007297", "auipc t0,0x7"),
  ("f9828293", "addi t0,t0,-104"),
  ("00449337", "lui t1,0x449"),
  ("8cd3031b", "addiw t1,t1,-1843"),
  ("00e31313", "slli t1,t1,0xe"),
  ("45530313", "addi t1,t1,1109"),
  ("00c31313", "slli t1,t1,0xc"),
  ("66730313", "addi t1,t1,1639"),
  ("78830313", "addi t1,t1,1928"),
  ("0062b023", "sd t1,0(t0)"),
  ("01f50463", "beq a0,t6,800000a8"),
  ("6350106f", "jal zero,80001ed8"),
  ("03029293", "slli t0,t0,0x30"),
  ("00c29293", "slli t0,t0,0xc"),
  ("23428293", "addi t0,t0,564"),
  ("18029073", "csrrw zero,satp,t0"),
  ("6090106f", "jal zero,80001ed8"),
  ("ffb0029b", "addiw t0,zero,-5"),
  ("5dd0106f", "jal zero,80001ed8"),
  ("5b10106f", "jal zero,80001ed8"),
  ("000102b7", "lui t0,0x10"),
  ("fff2829b", "addiw t0,t0,-1"),
  ("02029293", "slli t0,t0,0x20"),
  ("00010fb7", "lui t6,0x10"),
  ("ffff8f9b", "addiw t6,t6,-1"),
  ("020f9f93", "slli t6,t6,0x20"),
  ("234f8f93", "addi t6,t6,564"),
  ("5650106f", "jal zero,80001ed8"),
  ("ff90029b", "addiw t0,zero,-7"),
  ("03c29293", "slli t0,t0,0x3c"),
  ("ff900f9b", "addiw t6,zero,-7"),
  ("03cf9f93", "slli t6,t6,0x3c"),
  ("ffff8f93", "addi t6,t6,-1"),
  ("5310106f", "jal zero,80001ed8"),
  ("5050106f", "jal zero,80001ed8"),
  ("ffd0029b", "addiw t0,zero,-3"),
  ("03d29293", "slli t0,t0,0x3d"),
  ("00228293", "addi t0,t0,2"),
  ("ffd00f9b", "addiw t6,zero,-3"),
  ("03df9f93", "slli t6,t6,0x3d"),
  ("002f8f93", "addi t6,t6,2"),
  ("4d90106f", "jal zero,80001ed8"),
  ("03e29293", "slli t0,t0,0x3e"),
  ("00328293", "addi t0,t0,3"),
  ("4a50106f", "jal zero,80001ed8"),
  ("18005073", "csrrwi zero,satp,0"),
  ("48d0106f", "jal zero,80001ed8"),
  ("000402b7", "lui t0,0x40"),
  ("30002573", "csrrs a0,mstatus,zero"),
  ("00040fb7", "lui t6,0x40"),
  ("00040f37", "lui t5,0x40"),
  ("01ef8463", "beq t6,t5,80000274"),
  ("4690106f", "jal zero,80001ed8"),
  ("1002a073", "csrrs zero,sstatus,t0"),
  ("43d0106f", "jal zero,80001ed8"),
  ("00004297", "auipc t0,0x4"),
  ("d5c28293", "addi t0,t0,-676"),
  ("00c2d313", "srli t1,t0,0xc"),
  ("00a31313", "slli t1,t1,0xa"),
  ("00136313", "ori t1,t1,1"),
  ("00000e13", "addi t3,zero,0"),
  ("01c36333", "or t1,t1,t3"),
  ("00003397", "auipc t2,0x3"),
  ("d4038393", "addi t2,t2,-704"),
  ("01c383b3", "add t2,t2,t3"),
  ("0063b023", "sd t1,0(t2)"),
  ("01f29293", "slli t0,t0,0x1f"),
  ("0cf36313", "ori t1,t1,207"),
  ("d1038393", "addi t2,t2,-752"),
  ("01000e13", "addi t3,zero,16"),
  ("0df36313", "ori t1,t1,223"),
  ("ce038393", "addi t2,t2,-800"),
  ("01800e13", "addi t3,zero,24"),
  ("4010029b", "addiw t0,zero,1025"),
  ("01529293", "slli t0,t0,0x15"),
  ("0c736313", "ori t1,t1,199"),
  ("cb038393", "addi t2,t2,-848"),
  ("02000e13", "addi t3,zero,32"),
  ("c8038393", "addi t2,t2,-896"),
  ("00001e37", "lui t3,0x1"),
  ("ff8e0e1b", "addiw t3,t3,-8"),
  ("00005297", "auipc t0,0x5"),
  ("c6828293", "addi t0,t0,-920"),
  ("00004397", "auipc t2,0x4"),
  ("c4c38393", "addi t2,t2,-948"),
  ("c1c38393", "addi t2,t2,-996"),
  ("00800e13", "addi t3,zero,8"),
  ("000802b7", "lui t0,0x80"),
  ("0012829b", "addiw t0,t0,1"),
  ("be838393", "addi t2,t2,-1048"),
  ("bd428293", "addi t0,t0,-1068"),
  ("04136313", "ori t1,t1,65"),
  ("bb838393", "addi t2,t2,-1096"),
  ("ba428293", "addi t0,t0,-1116"),
  ("01136313", "ori t1,t1,17"),
  ("b8838393", "addi t2,t2,-1144"),
  ("b7428293", "addi t0,t0,-1164"),
  ("08136313", "ori t1,t1,129"),
  ("b5838393", "addi t2,t2,-1192"),
  ("02800e13", "addi t3,zero,40"),
  ("b4428293", "addi t0,t0,-1212"),
  ("b2838393", "addi t2,t2,-1240"),
  ("03000e13", "addi t3,zero,48"),
  ("b1428293", "addi t0,t0,-1260"),
  ("00005397", "auipc t2,0x5"),
  ("af838393", "addi t2,t2,-1288"),
  ("ae428293", "addi t0,t0,-1308"),
  ("04336313", "ori t1,t1,67"),
  ("ac838393", "addi t2,t2,-1336"),
  ("ab428293", "addi t0,t0,-1356"),
  ("04936313", "ori t1,t1,73"),
  ("a9838393", "addi t2,t2,-1384"),
  ("a8428293", "addi t0,t0,-1404"),
  ("0d736313", "ori t1,t1,215"),
  ("a6838393", "addi t2,t2,-1432"),
  ("a5428293", "addi t0,t0,-1452"),
  ("08736313", "ori t1,t1,135"),
  ("a3838393", "addi t2,t2,-1480"),
  ("a2428293", "addi t0,t0,-1500"),
  ("04736313", "ori t1,t1,71"),
  ("a0838393", "addi t2,t2,-1528"),
  ("03800e13", "addi t3,zero,56"),
  ("9f428293", "addi t0,t0,-1548"),
  ("0c536313", "ori t1,t1,197"),
  ("9d838393", "addi t2,t2,-1576"),
  ("04000e13", "addi t3,zero,64"),
  ("9c428293", "addi t0,t0,-1596"),
  ("00100e1b", "addiw t3,zero,1"),
  ("036e1e13", "slli t3,t3,0x36"),
  ("9a438393", "addi t2,t2,-1628"),
  ("04800e13", "addi t3,zero,72"),
  ("fff00e1b", "addiw t3,zero,-1"),
  ("03fe1e13", "slli t3,t3,0x3f"),
  ("97838393", "addi t2,t2,-1672"),
  ("05000e13", "addi t3,zero,80"),
  ("03de1e13", "slli t3,t3,0x3d"),
  ("94c38393", "addi t2,t2,-1716"),
  ("05800e13", "addi t3,zero,88"),
  ("00009297", "auipc t0,0x9"),
  ("93828293", "addi t0,t0,-1736"),
  ("91c38393", "addi t2,t2,-1764"),
  ("06000e13", "addi t3,zero,96"),
  ("90828293", "addi t0,t0,-1784"),
  ("8ec38393", "addi t2,t2,-1812"),
  ("07000e13", "addi t3,zero,112"),
  ("8d828293", "addi t0,t0,-1832"),
  ("8bc38393", "addi t2,t2,-1860"),
  ("07800e13", "addi t3,zero,120"),
  ("8a828293", "addi t0,t0,-1880"),
  ("88c38393", "addi t2,t2,-1908"),
  ("08000e13", "addi t3,zero,128"),
  ("87828293", "addi t0,t0,-1928"),
  ("05936313", "ori t1,t1,89"),
  ("85c38393", "addi t2,t2,-1956"),
  ("08800e13", "addi t3,zero,136"),
  ("84828293", "addi t0,t0,-1976"),
  ("00006397", "auipc t2,0x6"),
  ("82c38393", "addi t2,t2,-2004"),
  ("00003297", "auipc t0,0x3"),
  ("81828293", "addi t0,t0,-2024"),
  ("00c2d293", "srli t0,t0,0xc"),
  ("03f31313", "slli t1,t1,0x3f"),
  ("0062e2b3", "or t0,t0,t1"),
  ("00002437", "lui s0,0x2"),
  ("00000793", "addi a5,zero,0"),
  ("00043783", "ld a5,0(s0)"),
  ("6900106f", "jal zero,80001ed8"),
  ("01f78463", "beq a5,t6,80000880"),
  ("65c0106f", "jal zero,80001ed8"),
  ("00006417", "auipc s0,0x6"),
  ("78040413", "addi s0,s0,1920"),
  ("7fe002b7", "lui t0,0x7fe00"),
  ("40540433", "sub s0,s0,t0"),
  ("5f00106f", "jal zero,80001ed8"),
  ("02aab837", "lui a6,0x2aab"),
  ("b338081b", "addiw a6,a6,-1229"),
  ("00d81813", "slli a6,a6,0xd"),
  ("67780813", "addi a6,a6,1655"),
  ("00c81813", "slli a6,a6,0xc"),
  ("77980813", "addi a6,a6,1913"),
  ("88880813", "addi a6,a6,-1912"),
  ("01043823", "sd a6,16(s0)"),
  ("5940106f", "jal zero,80001ed8"),
  ("6b828293", "addi t0,t0,1720"),
  ("0102b783", "ld a5,16(t0)"),
  ("01078463", "beq a5,a6,80000960"),
  ("57c0106f", "jal zero,80001ed8"),
  ("6a040413", "addi s0,s0,1696"),
  ("01e29293", "slli t0,t0,0x1e"),
  ("00540433", "add s0,s0,t0"),
  ("50c0106f", "jal zero,80001ed8"),
  ("0010041b", "addiw s0,zero,1"),
  ("02641413", "slli s0,s0,0x26"),
  ("00d00f93", "addi t6,zero,13"),
  ("4b80106f", "jal zero,80001ed8"),
  ("026f9f93", "slli t6,t6,0x26"),
  ("01f60463", "beq a2,t6,80000a34"),
  ("4a80106f", "jal zero,80001ed8"),
  ("00043023", "sd zero,0(s0)"),
  ("00f00f93", "addi t6,zero,15"),
  ("46c0106f", "jal zero,80001ed8"),
  ("45c0106f", "jal zero,80001ed8"),
  ("02649493", "slli s1,s1,0x26"),
  ("34149073", "csrrw zero,mepc,s1"),
  ("00cd0d13", "addi s10,s10,12"),
  ("00c00f93", "addi t6,zero,12"),
  ("4280106f", "jal zero,80001ed8"),
  ("4180106f", "jal zero,80001ed8"),
  ("01f58463", "beq a1,t6,80000ad8"),
  ("4040106f", "jal zero,80001ed8"),
  ("fff0041b", "addiw s0,zero,-1"),
  ("02741413", "slli s0,s0,0x27"),
  ("3c00106f", "jal zero,80001ed8"),
  ("027f9f93", "slli t6,t6,0x27"),
  ("3b00106f", "jal zero,80001ed8"),
  ("fff0049b", "addiw s1,zero,-1"),
  ("02749493", "slli s1,s1,0x27"),
  ("3800106f", "jal zero,80001ed8"),
  ("3700106f", "jal zero,80001ed8"),
  ("00001437", "lui s0,0x1"),
  ("0084041b", "addiw s0,s0,8"),
  ("32c0106f", "jal zero,80001ed8"),
  ("00001fb7", "lui t6,0x1"),
  ("008f8f9b", "addiw t6,t6,8"),
  ("31c0106f", "jal zero,80001ed8"),
  ("00042023", "sw zero,0(s0)"),
  ("2e00106f", "jal zero,80001ed8"),
  ("2d00106f", "jal zero,80001ed8"),
  ("000014b7", "lui s1,0x1"),
  ("2a00106f", "jal zero,80001ed8"),
  ("2940106f", "jal zero,80001ed8"),
  ("00003437", "lui s0,0x3"),
  ("2340106f", "jal zero,80001ed8"),
  ("1f80106f", "jal zero,80001ed8"),
  ("00003fb7", "lui t6,0x3"),
  ("1ec0106f", "jal zero,80001ed8"),
  ("000437af", "amoadd.d a5,zero,(s0)"),
  ("1b00106f", "jal zero,80001ed8"),
  ("1a40106f", "jal zero,80001ed8"),
  ("180437af", "sc.d a5,zero,(s0)"),
  ("1680106f", "jal zero,80001ed8"),
  ("15c0106f", "jal zero,80001ed8"),
  ("100437af", "lr.d a5,(s0)"),
  ("1804372f", "sc.d a4,zero,(s0)"),
  ("1180106f", "jal zero,80001ed8"),
  ("10c0106f", "jal zero,80001ed8"),
  ("0e00106f", "jal zero,80001ed8"),
  ("00004437", "lui s0,0x4"),
  ("0a00106f", "jal zero,80001ed8"),
  ("0940106f", "jal zero,80001ed8"),
  ("000812b7", "lui t0,0x81"),
  ("0380106f", "jal zero,80001ed8"),
  ("400437af", "amoor.d a5,zero,(s0)"),
  ("7fd0006f", "jal zero,80001ed8"),
  ("7ff61ae3", "bne a2,t6,80001ed8"),
  ("7bf51ee3", "bne a0,t6,80001ed8"),
  ("7bf61ae3", "bne a2,t6,80001ed8"),
  ("00008437", "lui s0,0x8"),
  ("77f51ce3", "bne a0,t6,80001ed8"),
  ("00008fb7", "lui t6,0x8"),
  ("77f618e3", "bne a2,t6,80001ed8"),
  ("73f51ce3", "bne a0,t6,80001ed8"),
  ("73f618e3", "bne a2,t6,80001ed8"),
  ("00005437", "lui s0,0x5"),
  ("6ff51ae3", "bne a0,t6,80001ed8"),
  ("00005fb7", "lui t6,0x5"),
  ("6ff616e3", "bne a2,t6,80001ed8"),
  ("00043423", "sd zero,8(s0)"),
  ("6bf51ae3", "bne a0,t6,80001ed8"),
  ("6bf614e3", "bne a2,t6,80001ed8"),
  ("000412b7", "lui t0,0x41"),
  ("65f798e3", "bne a5,t6,80001ed8"),
  ("00092837", "lui a6,0x92"),
  ("a2b8081b", "addiw a6,a6,-1493"),
  ("3c580813", "addi a6,a6,965"),
  ("abd80813", "addi a6,a6,-1347"),
  ("def80813", "addi a6,a6,-529"),
  ("01043423", "sd a6,8(s0)"),
  ("5ff51ce3", "bne a0,t6,80001ed8"),
  ("f1c28293", "addi t0,t0,-228"),
  ("0082b783", "ld a5,8(t0)"),
  ("5f0792e3", "bne a5,a6,80001ed8"),
  ("00001497", "auipc s1,0x1"),
  ("e2048493", "addi s1,s1,-480"),
  ("400002b7", "lui t0,0x40000"),
  ("005484b3", "add s1,s1,t0"),
  ("5bf516e3", "bne a0,t6,80001ed8"),
  ("5a9612e3", "bne a2,s1,80001ed8"),
  ("00040837", "lui a6,0x40"),
  ("10082073", "csrrs zero,sstatus,a6"),
  ("55f792e3", "bne a5,t6,80001ed8"),
  ("02028293", "addi t0,t0,32"),
  ("006282b3", "add t0,t0,t1"),
  ("00f43c23", "sd a5,24(s0)"),
  ("51f510e3", "bne a0,t6,80001ed8"),
  ("4df79ce3", "bne a5,t6,80001ed8"),
  ("49f51ce3", "bne a0,t6,80001ed8"),
  ("49f618e3", "bne a2,t6,80001ed8"),
  ("45f51ae3", "bne a0,t6,80001ed8"),
  ("45f616e3", "bne a2,t6,80001ed8"),
  ("c8848493", "addi s1,s1,-888"),
  ("43f510e3", "bne a0,t6,80001ed8"),
  ("40961ce3", "bne a2,s1,80001ed8"),
  ("00011437", "lui s0,0x11"),
  ("3df51ce3", "bne a0,t6,80001ed8"),
  ("00011fb7", "lui t6,0x11"),
  ("3df618e3", "bne a2,t6,80001ed8"),
  ("37f79ae3", "bne a5,t6,80001ed8"),
  ("00006437", "lui s0,0x6"),
  ("33f51ce3", "bne a0,t6,80001ed8"),
  ("00006fb7", "lui t6,0x6"),
  ("33f618e3", "bne a2,t6,80001ed8"),
  ("2ff51ce3", "bne a0,t6,80001ed8"),
  ("2ff618e3", "bne a2,t6,80001ed8"),
  ("00007437", "lui s0,0x7"),
  ("29f79ae3", "bne a5,t6,80001ed8"),
  ("25f51ee3", "bne a0,t6,80001ed8"),
  ("00007fb7", "lui t6,0x7"),
  ("25f61ae3", "bne a2,t6,80001ed8"),
  ("080437af", "amoswap.d a5,zero,(s0)"),
  ("21f51ee3", "bne a0,t6,80001ed8"),
  ("21f61ae3", "bne a2,t6,80001ed8"),
  ("00009437", "lui s0,0x9"),
  ("1df51ce3", "bne a0,t6,80001ed8"),
  ("00009fb7", "lui t6,0x9"),
  ("1df618e3", "bne a2,t6,80001ed8"),
  ("0000a437", "lui s0,0xa"),
  ("19f51ae3", "bne a0,t6,80001ed8"),
  ("0000afb7", "lui t6,0xa"),
  ("19f616e3", "bne a2,t6,80001ed8"),
  ("0000b437", "lui s0,0xb"),
  ("15f518e3", "bne a0,t6,80001ed8"),
  ("15f614e3", "bne a2,t6,80001ed8"),
  ("00010437", "lui s0,0x10"),
  ("11f516e3", "bne a0,t6,80001ed8"),
  ("11f612e3", "bne a2,t6,80001ed8"),
  ("00400437", "lui s0,0x400"),
  ("0df514e3", "bne a0,t6,80001ed8"),
  ("00400fb7", "lui t6,0x400"),
  ("0df610e3", "bne a2,t6,80001ed8"),
  ("02041413", "slli s0,s0,0x20"),
  ("09f510e3", "bne a0,t6,80001ed8"),
  ("07f61ae3", "bne a2,t6,80001ed8"),
  ("00602437", "lui s0,0x602"),
  ("03f51ce3", "bne a0,t6,80001ed8"),
  ("00602fb7", "lui t6,0x602"),
  ("03f618e3", "bne a2,t6,80001ed8"),
  ("00802437", "lui s0,0x802"),
  ("7ff51a63", "bne a0,t6,80001ed8"),
  ("00802fb7", "lui t6,0x802"),
  ("7ff61663", "bne a2,t6,80001ed8"),
  ("00a02437", "lui s0,0xa02"),
  ("34141073", "csrrw zero,mepc,s0"),
  ("7df51063", "bne a0,t6,80001ed8"),
  ("00a02fb7", "lui t6,0xa02"),
  ("7bf61c63", "bne a2,t6,80001ed8"),
  ("00c00437", "lui s0,0xc00"),
  ("0104041b", "addiw s0,s0,16"),
  ("00500f93", "addi t6,zero,5"),
  ("77f51863", "bne a0,t6,80001ed8"),
  ("00c00fb7", "lui t6,0xc00"),
  ("010f8f9b", "addiw t6,t6,16"),
  ("77f61263", "bne a2,t6,80001ed8"),
  ("73f51663", "bne a0,t6,80001ed8"),
  ("73f61063", "bne a2,t6,80001ed8"),
  ("00c004b7", "lui s1,0xc00"),
  ("6ff51a63", "bne a0,t6,80001ed8"),
  ("6ff61663", "bne a2,t6,80001ed8"),
  ("6ff59063", "bne a1,t6,80001ed8"),
  ("0000f437", "lui s0,0xf"),
  ("0204041b", "addiw s0,s0,32"),
  ("69f51c63", "bne a0,t6,80001ed8"),
  ("0000ffb7", "lui t6,0xf"),
  ("020f8f9b", "addiw t6,t6,32"),
  ("69f61663", "bne a2,t6,80001ed8"),
  ("65f51a63", "bne a0,t6,80001ed8"),
  ("65f61463", "bne a2,t6,80001ed8"),
  ("0000f4b7", "lui s1,0xf"),
  ("61f51e63", "bne a0,t6,80001ed8"),
  ("61f61a63", "bne a2,t6,80001ed8"),
  ("0000d4b7", "lui s1,0xd"),
  ("ffe4849b", "addiw s1,s1,-2"),
  ("0000dfb7", "lui t6,0xd"),
  ("5df61a63", "bne a2,t6,80001ed8"),
  ("ffef8f9b", "addiw t6,t6,-2"),
  ("5df59263", "bne a1,t6,80001ed8"),
  ("6e828293", "addi t0,t0,1768"),
  ("6cc38393", "addi t2,t2,1740"),
  ("06800e13", "addi t3,zero,104"),
  ("55f51e63", "bne a0,t6,80001ed8"),
  ("002f8f9b", "addiw t6,t6,2"),
  ("55f59663", "bne a1,t6,80001ed8"),
  ("53f79c63", "bne a5,t6,80001ed8"),
  ("65c28293", "addi t0,t0,1628"),
  ("64038393", "addi t2,t2,1600"),
  ("4df79863", "bne a5,t6,80001ed8"),
  ("0000e4b7", "lui s1,0xe"),
  ("0204849b", "addiw s1,s1,32"),
  ("77777837", "lui a6,0x77777"),
  ("7778081b", "addiw a6,a6,1911"),
  ("02081813", "slli a6,a6,0x20"),
  ("00500713", "addi a4,zero,5"),
  ("1904b72f", "sc.d a4,a6,(s1)"),
  ("47f71663", "bne a4,t6,80001ed8"),
  ("59028293", "addi t0,t0,1424"),
  ("0202b783", "ld a5,32(t0)"),
  ("45079c63", "bne a5,a6,80001ed8"),
  ("43f51263", "bne a0,t6,80001ed8"),
  ("3ff79e63", "bne a5,t6,80001ed8"),
  ("3df51263", "bne a0,t6,80001ed8"),
  ("3bf61e63", "bne a2,t6,80001ed8"),
  ("000612b7", "lui t0,0x61"),
  ("39f51663", "bne a0,t6,80001ed8"),
  ("37f79263", "bne a5,t6,80001ed8"),
  ("000202b7", "lui t0,0x20"),
  ("31f79e63", "bne a5,t6,80001ed8"),
  ("2ff51863", "bne a0,t6,80001ed8"),
  ("2ff61463", "bne a2,t6,80001ed8"),
  ("2bf51c63", "bne a0,t6,80001ed8"),
  ("2bf61863", "bne a2,t6,80001ed8"),
  ("000a12b7", "lui t0,0xa1"),
  ("27f51e63", "bne a0,t6,80001ed8"),
  ("25f79a63", "bne a5,t6,80001ed8"),
  ("0000b2b7", "lui t0,0xb"),
  ("21f51463", "bne a0,t6,80001ed8"),
  ("1ff91a63", "bne s2,t6,80001ed8"),
  ("1ffa1263", "bne s4,t6,80001ed8"),
  ("1c599663", "bne s3,t0,80001ed8"),
  ("19f51863", "bne a0,t6,80001ed8"),
  ("19f91263", "bne s2,t6,80001ed8"),
  ("06500193", "addi gp,zero,101"),
  ("15f51e63", "bne a0,t6,80001ed8"),
  ("06600193", "addi gp,zero,102"),
  ("15f91863", "bne s2,t6,80001ed8"),
  ("06700193", "addi gp,zero,103"),
  ("15f99263", "bne s3,t6,80001ed8"),
  ("06800193", "addi gp,zero,104"),
  ("11f51c63", "bne a0,t6,80001ed8"),
  ("11f61863", "bne a2,t6,80001ed8"),
  ("00005417", "auipc s0,0x5"),
  ("22840413", "addi s0,s0,552"),
  ("06900193", "addi gp,zero,105"),
  ("0bf79263", "bne a5,t6,80001ed8"),
  ("1c848493", "addi s1,s1,456"),
  ("00c4d493", "srli s1,s1,0xc"),
  ("0054e4b3", "or s1,s1,t0"),
  ("18049073", "csrrw zero,satp,s1"),
  ("06a00193", "addi gp,zero,106"),
  ("05f51263", "bne a0,t6,80001ed8"),
  ("06b00193", "addi gp,zero,107"),
  ("01f79e63", "bne a5,t6,80001ed8"),
  ("138f0f13", "addi t5,t5,312"),
  ("120f0f13", "addi t5,t5,288"),
  (* tests/sv48.S *)
  ("00007d97", "auipc s11,0x7"),
  ("94028293", "addi t0,t0,-1728"),
  ("fc428293", "addi t0,t0,-60"),
  ("0111a337", "lui t1,0x111a"),
  ("a233031b", "addiw t1,t1,-1501"),
  ("ab330313", "addi t1,t1,-1357"),
  ("00d31313", "slli t1,t1,0xd"),
  ("77930313", "addi t1,t1,1913"),
  ("89930313", "addi t1,t1,-1895"),
  ("00002397", "auipc t2,0x2"),
  ("f7c38393", "addi t2,t2,-132"),
  ("f5038393", "addi t2,t2,-176"),
  ("f2438393", "addi t2,t2,-220"),
  ("ef838393", "addi t2,t2,-264"),
  ("800e0e1b", "addiw t3,t3,-2048"),
  ("ee028293", "addi t0,t0,-288"),
  ("ec438393", "addi t2,t2,-316"),
  ("e9438393", "addi t2,t2,-364"),
  ("e6438393", "addi t2,t2,-412"),
  ("e3438393", "addi t2,t2,-460"),
  ("e2028293", "addi t0,t0,-480"),
  ("e0438393", "addi t2,t2,-508"),
  ("dd438393", "addi t2,t2,-556"),
  ("da038393", "addi t2,t2,-608"),
  ("d8c28293", "addi t0,t0,-628"),
  ("d7038393", "addi t2,t2,-656"),
  ("d2c28293", "addi t0,t0,-724"),
  ("ff90031b", "addiw t1,zero,-7"),
  ("03c31313", "slli t1,t1,0x3c"),
  ("d0028293", "addi t0,t0,-768"),
  ("60551863", "bne a0,t0,8000092c"),
  ("5df51863", "bne a0,t6,8000092c"),
  ("0111afb7", "lui t6,0x111a"),
  ("a23f8f9b", "addiw t6,t6,-1501"),
  ("ab3f8f93", "addi t6,t6,-1357"),
  ("779f8f93", "addi t6,t6,1913"),
  ("899f8f93", "addi t6,t6,-1895"),
  ("5bf79063", "bne a5,t6,8000092c"),
  ("c7040413", "addi s0,s0,-912"),
  ("c0840413", "addi s0,s0,-1016"),
  ("4df79c63", "bne a5,t6,8000092c"),
  ("ba840413", "addi s0,s0,-1112"),
  ("02729293", "slli t0,t0,0x27"),
  ("00028837", "lui a6,0x28"),
  ("2c38081b", "addiw a6,a6,707"),
  ("00e81813", "slli a6,a6,0xe"),
  ("0d180813", "addi a6,a6,209"),
  ("e0f80813", "addi a6,a6,-497"),
  ("01081813", "slli a6,a6,0x10"),
  ("10280813", "addi a6,a6,258"),
  ("43f79e63", "bne a5,t6,8000092c"),
  ("b0c28293", "addi t0,t0,-1268"),
  ("43079463", "bne a5,a6,8000092c"),
  ("af840413", "addi s0,s0,-1288"),
  ("02f29293", "slli t0,t0,0x2f"),
  ("3bf79e63", "bne a5,t6,8000092c"),
  ("05500793", "addi a5,zero,85"),
  ("37f51e63", "bne a0,t6,8000092c"),
  ("05500f93", "addi t6,zero,85"),
  ("37f79863", "bne a5,t6,8000092c"),
  ("a4040413", "addi s0,s0,-1472"),
  ("33f51663", "bne a0,t6,8000092c"),
  ("31f79263", "bne a5,t6,8000092c"),
  ("02f41413", "slli s0,s0,0x2f"),
  ("2bf51e63", "bne a0,t6,8000092c"),
  ("02ff9f93", "slli t6,t6,0x2f"),
  ("27f51c63", "bne a0,t6,8000092c"),
  ("27f61663", "bne a2,t6,8000092c"),
  ("02f49493", "slli s1,s1,0x2f"),
  ("23f61863", "bne a2,t6,8000092c"),
  ("23f59063", "bne a1,t6,8000092c"),
  ("02341413", "slli s0,s0,0x23"),
  ("fff40413", "addi s0,s0,-1"),
  ("00c41413", "slli s0,s0,0xc"),
  ("1df51c63", "bne a0,t6,8000092c"),
  ("023f9f93", "slli t6,t6,0x23"),
  ("1df61263", "bne a2,t6,8000092c"),
  ("0ff0041b", "addiw s0,zero,255"),
  ("19f51263", "bne a0,t6,8000092c"),
  ("0ff00f9b", "addiw t6,zero,255"),
  ("17f61c63", "bne a2,t6,8000092c"),
  ("02841413", "slli s0,s0,0x28"),
  ("13f51863", "bne a0,t6,8000092c"),
  ("028f9f93", "slli t6,t6,0x28"),
  ("13f61263", "bne a2,t6,8000092c"),
  ("0ff51263", "bne a0,t6,8000092c"),
  ("0df61c63", "bne a2,t6,8000092c"),
  ("0bf61263", "bne a2,t6,8000092c"),
  ("07f61063", "bne a2,t6,8000092c"),
  ("01f61e63", "bne a2,t6,8000092c"),
  ("6e4f0f13", "addi t5,t5,1764"),
  ("6ccf0f13", "addi t5,t5,1740"),
  (* tests/sv57.S *)
  ("00008d97", "auipc s11,0x8"),
  ("92c28293", "addi t0,t0,-1748"),
  ("93428293", "addi t0,t0,-1740"),
  ("00669337", "lui t1,0x669"),
  ("8ab3031b", "addiw t1,t1,-1877"),
  ("ccf30313", "addi t1,t1,-817"),
  ("c4530313", "addi t1,t1,-955"),
  ("9aa30313", "addi t1,t1,-1622"),
  ("f2038393", "addi t2,t2,-224"),
  ("ef438393", "addi t2,t2,-268"),
  ("edc28293", "addi t0,t0,-292"),
  ("ec038393", "addi t2,t2,-320"),
  ("e6838393", "addi t2,t2,-408"),
  ("e5428293", "addi t0,t0,-428"),
  ("e3838393", "addi t2,t2,-456"),
  ("e0838393", "addi t2,t2,-504"),
  ("dd838393", "addi t2,t2,-552"),
  ("dc428293", "addi t0,t0,-572"),
  ("da838393", "addi t2,t2,-600"),
  ("d7838393", "addi t2,t2,-648"),
  ("d6428293", "addi t0,t0,-668"),
  ("d4838393", "addi t2,t2,-696"),
  ("d3428293", "addi t0,t0,-716"),
  ("ffd0031b", "addiw t1,zero,-3"),
  ("03d31313", "slli t1,t1,0x3d"),
  ("d0828293", "addi t0,t0,-760"),
  ("60551663", "bne a0,t0,80000920"),
  ("5df51663", "bne a0,t6,80000920"),
  ("00669fb7", "lui t6,0x669"),
  ("8abf8f9b", "addiw t6,t6,-1877"),
  ("ccff8f93", "addi t6,t6,-817"),
  ("c45f8f93", "addi t6,t6,-955"),
  ("9aaf8f93", "addi t6,t6,-1622"),
  ("59f79e63", "bne a5,t6,80000920"),
  ("00007417", "auipc s0,0x7"),
  ("c7840413", "addi s0,s0,-904"),
  ("53f79a63", "bne a5,t6,80000920"),
  ("c1040413", "addi s0,s0,-1008"),
  ("4df79a63", "bne a5,t6,80000920"),
  ("bb040413", "addi s0,s0,-1104"),
  ("47f79463", "bne a5,t6,80000920"),
  ("b4440413", "addi s0,s0,-1212"),
  ("00d0e837", "lui a6,0xd0e"),
  ("8e18081b", "addiw a6,a6,-1823"),
  ("e8f80813", "addi a6,a6,-369"),
  ("1f180813", "addi a6,a6,497"),
  ("01180813", "addi a6,a6,17"),
  ("3ff51a63", "bne a0,t6,80000920"),
  ("3df79663", "bne a5,t6,80000920"),
  ("aa828293", "addi t0,t0,-1368"),
  ("3b079c63", "bne a5,a6,80000920"),
  ("a9440413", "addi s0,s0,-1388"),
  ("03829293", "slli t0,t0,0x38"),
  ("35f79663", "bne a5,t6,80000920"),
  ("05700793", "addi a5,zero,87"),
  ("31f51663", "bne a0,t6,80000920"),
  ("05700f93", "addi t6,zero,87"),
  ("31f79063", "bne a5,t6,80000920"),
  ("9dc40413", "addi s0,s0,-1572"),
  ("29f79a63", "bne a5,t6,80000920"),
  ("03841413", "slli s0,s0,0x38"),
  ("038f9f93", "slli t6,t6,0x38"),
  ("25f61063", "bne a2,t6,80000920"),
  ("1ff61e63", "bne a2,t6,80000920"),
  ("03849493", "slli s1,s1,0x38"),
  ("1df51663", "bne a0,t6,80000920"),
  ("1df61063", "bne a2,t6,80000920"),
  ("02b41413", "slli s0,s0,0x2b"),
  ("00d41413", "slli s0,s0,0xd"),
  ("02bf9f93", "slli t6,t6,0x2b"),
  ("15f61a63", "bne a2,t6,80000920"),
  ("03041413", "slli s0,s0,0x30"),
  ("11f61463", "bne a2,t6,80000920"),
  ("0df51463", "bne a0,t6,80000920"),
  ("0bf61e63", "bne a2,t6,80000920"),
  ("03141413", "slli s0,s0,0x31"),
  ("07f51a63", "bne a0,t6,80000920"),
  ("07f61463", "bne a2,t6,80000920"),
  ("03f51463", "bne a0,t6,80000920"),
  ("6f0f0f13", "addi t5,t5,1776"),
  ("6d8f0f13", "addi t5,t5,1752")
]

(* ------------------------------------------------------------------------
   Running
   ------------------------------------------------------------------------ *)

val failures = ref ([] : string list)
val shapes = ref ([] : (string * string list) list)
val examples = ref ([] : (string * (string * Thm.thm)) list)
val counts = ref ([] : (string * int) list)
val no_steps = ref 0
(* theorems whose conclusion reads or writes c_SCSR, and with a hypothesis
   on it (each also a failure) *)
val scsr_concls = ref 0
val scsr_hyps = ref 0

fun incr key =
  counts :=
    (case Lib.assoc1 key (!counts) of
        SOME (_, n) => (key, n + 1) :: List.filter (not o equal key o fst)
                                                    (!counts)
      | NONE => (key, 1) :: !counts)

fun fail msg = (print ("FAIL " ^ msg ^ "\n"); failures := msg :: !failures)

fun must_not_step name h why =
  ( ignore (riscv_step_hex h)
  ; fail (name ^ " " ^ h ^ ": stepped, but " ^ why) )
  handle HOL_ERR _ =>
    ( no_steps := !no_steps + 1
    ; print ("no step (" ^ why ^ "): " ^ name ^ " " ^ h ^ "\n") )

(* A field check holds if it simplifies to T, or is then proved by
   bit-blasting (the fields of s as atoms), after a case split on the
   conditions in it.  rec'mstatus is expanded for the checks of the fields
   of a written mstatus. *)
local
  val ss = srw_ss() ++ bitstringLib.v2w_n2w_ss
  val rwts =
    [riscvTheory.Skip_def, riscv_stepTheory.reg_rec_id,
     riscvTheory.rec'mstatus_def]
  fun blast tm = TAC_PROOF (([], tm), rw [] \\ blastLib.FULL_BBLAST_TAC)
in
  fun field_holds tm =
    let
      val r = utilsLib.rhsc (Conv.QCONV (SIMP_CONV ss rwts) tm)
    in
      Teq r orelse Lib.can blast r
    end
    handle HOL_ERR _ => false
end

(* Checks the theorem of an encoding that must step, and the fields of the
   state after it (checks); returns false when riscv_step finds that the
   instruction traps (on a misaligned constant address, or a CSR access
   that is illegal), and then has no step theorem *)
fun must_step_with checks name h inst =
  let
    val th = SOME (riscv_step_hex h)
             handle e as HOL_ERR _ =>
               if String.isSubstring "instruction traps"
                    (Feedback.exn_to_string e)
                 then NONE
               else raise e
  in
    case th of
       NONE => false
     | SOME th =>
         let
           val (cats, errors) = check h inst th
           val key = if is_compressed h then "compressed" else class_of inst
           val s' =
             optionSyntax.dest_some (boolSyntax.rhs (Thm.concl th))
             handle HOL_ERR _ => s
           val field_errors =
             List.mapPartial
               (fn f =>
                  let
                    val tm = f s'
                  in
                    if field_holds tm then NONE
                    else SOME ("field check fails: " ^ Parse.term_to_string tm)
                  end) checks
         in
           List.app (fn e => fail (name ^ " " ^ h ^ " (" ^ name_of inst ^
                                   "): " ^ e)) (errors @ field_errors)
           ; if mentions_scsr (Thm.concl th)
               then scsr_concls := !scsr_concls + 1 else ()
           ; if List.exists mentions_scsr (Thm.hyp th)
               then scsr_hyps := !scsr_hyps + 1 else ()
           ; incr key
           ; shapes := (key, cats) :: !shapes
           ; if Lib.can (Lib.assoc key) (!examples) then ()
             else examples := (key, (name ^ " " ^ h, th)) :: !examples
           ; true
         end
  end
  handle e => (fail (name ^ " " ^ h ^ ": " ^ General.exnMessage e); true)

val must_step = must_step_with []

fun test name h =
  let
    val inst = decoded h
  in
    case no_step h inst of
       SOME why => (must_not_step name h why; true)
     | NONE => must_step name h inst
  end
  handle e => (fail (name ^ " " ^ h ^ ": " ^ General.exnMessage e); true)

val () = print "\nriscv_stepLib selftest\n\n"
val t0 = Time.now ()

(* every riscv_dict entry; an encoding with a misaligned constant address
   is retried with other bits *)
val () =
  List.app
    (fn (name, pat) =>
       let
         val base =
           if String.isSuffix "_NOP" name
             then String.substring (name, 0, String.size name - 4)
           else name
         val rms =
           if Lib.mem base exact_conversion then [SOME 0, SOME 4, SOME 7]
           else if Lib.mem base rounding then [SOME 0, SOME 7]
           else [NONE]
         (* a 32-bit entry is named after the instruction it decodes to *)
         fun named h =
           String.isPrefix "RVC_" name orelse
           name_of (decoded h) = base orelse
           (fail (name ^ " " ^ h ^ " decodes to " ^ name_of (decoded h))
            ; false)
         fun go rm k =
           if k = 0 then fail (name ^ ": no encoding that steps found")
           else
             let
               val h = instantiate rm pat
             in
               if not (named h) orelse test name h then () else go rm (k - 1)
             end
         (* a CSR entry: each of the required CSRs, with the other free
            bits chosen as for the other entries *)
         fun with_csr c =
           let
             val h = instantiate NONE pat
             val n = hex_int h mod 1048576 + c * 1048576
           in
             StringCvt.padLeft #"0" 8
               (String.map Char.toLower (Int.fmt StringCvt.HEX n))
           end
         (* for the CSR entries, an instruction that must step and does
            not is a failure (test returns false for it) *)
         fun csr_test c =
           let
             val h = with_csr c
           in
             if not (named h) orelse test name h then ()
             else fail (name ^ " " ^ h ^ ": no step")
           end
       in
         if Lib.mem base csr_insts then List.app csr_test required_csrs
         else List.app (fn rm => go rm 8) rms
       end)
    riscv_dict

(* every CSR of the hart, read with CSRRS (csrr a0) and written with CSRRW
   from t0 and CSRRCI with uimm 3 (each also tests that a write of a
   read-only CSR does not step), and some addresses that are not CSRs *)
local
  fun enc c f3 rd f =
    StringCvt.padLeft #"0" 8
      (String.map Char.toLower
         (Int.fmt StringCvt.HEX
            (c * 1048576 + f * 32768 + f3 * 4096 + rd * 128 + 0x73)))
  val absent =
    [0x000, 0x004, 0x008, 0x015, 0xC03, 0xC1F, 0xC80, 0x101, 0x120, 0x14D,
     0x15D, 0x181, 0x200, 0x310, 0x312, 0x321, 0x322, 0x34A, 0x3A1, 0x3A3,
     0x3A4, 0x3C0, 0x747, 0x7A0, 0x7B0, 0x7C0, 0xB01, 0xB80, 0xF00, 0xF10,
     0xFFF]
in
  val () =
    List.app
      (fn c =>
         List.app
           (fn (txt, f3, rd, f) =>
              let
                val name = "CSR 0x" ^ Int.fmt StringCvt.HEX c ^ " " ^ txt
                val h = enc c f3 rd f
              in
                if test name h then () else fail (name ^ " " ^ h ^ ": no step")
              end)
           [("csrrs a0,csr,zero", 2, 10, 0), ("csrrw zero,csr,t0", 1, 0, 5),
            ("csrrci t1,csr,3", 7, 6, 3)])
      (present_csrs @ absent)
end

(* the rm values that make an instruction with a rounding mode illegal *)
val () =
  List.app
    (fn (name, pat) =>
       if Lib.mem name rounding then
         List.app (fn rm => ignore (test (name ^ " rm=" ^ Int.toString rm)
                                       (instantiate (SOME rm) pat)))
           (if Lib.mem name exact_conversion then [5, 6] else [4, 5, 6])
       else ())
    riscv_dict

val () =
  List.app
    (fn (h, txt, steps, checks) =>
       let
         val inst = decoded h
         val name = "edge: " ^ txt
       in
         if steps then
           (if must_step_with checks name h inst then ()
            else fail (name ^ " " ^ h ^ ": no step"))
         else must_not_step name h "edge case"
       end
       handle e => fail ("edge: " ^ txt ^ " " ^ h ^ ": " ^
                         General.exnMessage e))
    edge_cases

val ndict = List.length riscv_dict

val () =
  List.app
    (fn (h, txt) =>
       if test ("sim: " ^ txt) h then ()
       else fail ("sim: " ^ txt ^ " " ^ h ^ ": traps on a constant address"))
    sim_tests

val () =
  let
    val classes =
      ["ALU", "branch", "JAL/JALR", "load", "store", "AMO", "LR/SC",
       "FP load/store", "FP arithmetic", "compressed", "FENCE", "system",
       "trap", "MRET", "CSR"]
  in
    print ("\nriscv_dict entries: " ^ Int.toString ndict ^
           ", sim/tests instructions: " ^ Int.toString (List.length sim_tests) ^
           ", edge cases: " ^ Int.toString (List.length edge_cases) ^
           "\nexpected not to step, and did not: " ^
           Int.toString (!no_steps) ^
           "\nwith c_SCSR in the conclusion (a CSR instruction on stvec, \
           \scounteren, senvcfg, sscratch, sepc, scause, stval or satp): " ^
           Int.toString (!scsr_concls) ^ ", in a hypothesis: " ^
           Int.toString (!scsr_hyps) ^
           "\n\nhypotheses by class:\n");
    List.app
      (fn c =>
         let
           val n = case Lib.assoc1 c (!counts) of SOME (_, n) => n | NONE => 0
           val sets =
             Lib.mk_set
               (List.map (String.concatWith ", " o snd)
                  (List.filter (equal c o fst) (!shapes)))
         in
           print ("  " ^ c ^ ": " ^ Int.toString n ^ " theorems\n");
           List.app (fn x => print ("    {" ^ x ^ "}\n"))
             (Listsort.sort String.compare sets)
         end) classes;
    print "\nexamples:\n";
    List.app
      (fn c =>
         case Lib.assoc1 c (!examples) of
            SOME (_, (what, th)) =>
              ( print ("\n  " ^ c ^ ": " ^ what ^ "\n")
              ; List.app
                  (fn h => print ("    " ^ Parse.term_to_string h ^ "\n"))
                  (Thm.hyp th) )
          | NONE => ()) classes;
    print ("\ntime: " ^ Time.toString (Time.- (Time.now (), t0)) ^ " s\n")
  end
in
val () =
  case !failures of
     [] => ( print "\nriscv_stepLib selftest: all checks passed\n"
           ; selftest_passed := true )
   | l => print ("\nriscv_stepLib selftest: " ^ Int.toString (List.length l) ^
                 " failures\n")
end;

val () =
  OS.Process.exit
    (if !selftest_passed then OS.Process.success else OS.Process.failure);
