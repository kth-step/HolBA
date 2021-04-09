structure bir_multicore_inst_liftingLib :> bir_multicore_inst_liftingLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open testutils;
open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open PPBackEnd;
open riscv_assemblerLib;
open selftestLib;
open selftest_styleLib;

open bir_interval_expSyntax bir_immSyntax bir_program_labelsSyntax bir_programSyntax;

open wordsSyntax pairSyntax listSyntax stringSyntax;


(* Flags for determining type of output *)
val unicode = false;
val raw_output = false;
(* Flags used here *)
val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else
                                     PPBackEnd.vt100_terminal);
val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)


val ERR = mk_HOL_ERR "bir_multicore_inst_liftingLib"
val wrap_exn = Feedback.wrap_exn "bir_multicore_inst_liftingLib"

(* TODO: Any other way to supply this to the functor? *)
structure log_name =
struct
  val log_name = "selftest_multicore_riscv.log";
end;

structure test_RISCV = test_bmr(structure MD = bmil_riscv; structure log_name_str = log_name);

(* 1. Testing phase: wrap lift_instr *)

(* 2. Finalize phase: wrap lift_da_and_store in bir_lifter_interfaceLib *)

(* TODO: Double-check these numbers are OK, should work with arbitrary ones though *)
(*
val mu_b = Arbnum.fromInt 0; (* Memory starts at address 0x0 *)
val mu_e = Arbnum.fromInt 0x1000000; (* Memory ends at address 0x1000000 *)
val pc =   Arbnum.fromInt 0x10030; (* Program counter is at address 0x10030 *)

(* TEST: opcode MISC-MEM *)
(* RW/RW fence *)
val hex = "0330000F"

*)

(**************** From RISC-V selftest ********************)

(* Ignore error here... *)
fun riscv_test_hex mu_b mu_e pc hex = test_RISCV.lift_instr mu_b mu_e pc hex NONE;

fun riscv_test_hex_print_asm asm mu_b mu_e pc hex = 
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    test_RISCV.lift_instr mu_b mu_e pc hex NONE
  end
;

fun riscv_test_asm asm mu_b mu_e pc =
  let
    val _ = test_RISCV.print_log true (asm^(": "))
  in
    riscv_test_hex mu_b mu_e pc (riscv_hex_from_asm asm)
  end
;
val riscv_test_asms = map riscv_test_asm

(**************************************************************)

local
fun pad_zero' 0   str = str
  | pad_zero' len str = pad_zero' (len-1) ("0"^str)
in
fun hex_to_bin_pad_zero len str =
  let
    val str' = (Arbnum.toBinString (Arbnum.fromHexString str))
  in
    pad_zero' (len - (size str')) str'
  end
end
;

fun parse_fence hex =
  let
    val bin = hex_to_bin_pad_zero 32 hex
    val fm = substring (bin, 0, 4)
    val pi = substring (bin, 4, 1)
    val po = substring (bin, 5, 1)
    val pr = substring (bin, 6, 1)
    val pw = substring (bin, 7, 1)
    val si = substring (bin, 8, 1)
    val so = substring (bin, 9, 1)
    val sr = substring (bin, 10, 1)
    val sw = substring (bin, 11, 1)
    val rs1 = substring (bin, 12, 5)
    val funct3 = substring (bin, 17, 3)
    val rd = substring (bin, 20, 5)
    val opcode = substring (bin, 25, 7)
  in
    (fm, pi, po, pr, pw, si, so, sr, sw, rs1, funct3, rd, opcode)
  end
;

fun is_fence hex =
  let
    val (fm, pi, po, pr, pw, si, so, sr, sw, rs1, funct3, rd, opcode) = parse_fence hex
  in
    if opcode = "0001111" (* opcode MISC-MEM *)
    then
      (* TODO: Well-formedness conditions here... *)
      (* Only recognize fences which would have any effect on TSO semantics for now *)
      (pw = "1") andalso (sr = "1")
    else false
  end
;

fun get_fence_args hex =
  let
    val (fm, pi, po, pr, pw, si, so, sr, sw, rs1, funct3, rd, opcode) = parse_fence hex
  in
    (if pr = "1"
     then if pw = "1"
	  then BM_ReadWrite_tm
	  else BM_Read_tm
     else if pw = "1"
	  then BM_Write_tm
	  else raise ERR "get_fence_args" "Fence has no predecessor R/W bits",
     if sr = "1"
     then if sw = "1"
	  then BM_ReadWrite_tm
	  else BM_Read_tm
     else if sw = "1"
	  then BM_Write_tm
	  else raise ERR "get_fence_args" "Fence has no successor R/W bits"
       )
  end
;

fun is_atomic hex =
  let
    val bin = hex_to_bin_pad_zero 32 hex
    val opcode = substring (bin, 25, 7)
  in
    if opcode = "0101111" (* opcode AMO *)
    then let
           val msb_5 = substring (bin, 0, 5)
         in
           (* Rule out LR and SC, for now... *)
           (msb_5 <> "00010") andalso (msb_5 <> "00011")
         end
    else false
  end
;

val word8_tm = mk_word_type (fcpSyntax.mk_numeric_type (Arbnum.fromInt 8));

fun get_byte_word_l hex =
  let
    val bin = hex_to_bin_pad_zero 32 hex
    val byte1 = substring (bin, 0, 8)
    val byte2 = substring (bin, 8, 8)
    val byte3 = substring (bin, 16, 8)
    val byte4 = substring (bin, 24, 8)
    val byte_to_word8 = (fn byte => (mk_wordi (Arbnum.fromBinString byte, 8)))
  in
    mk_list ((map byte_to_word8 [byte1, byte2, byte3, byte4]), word8_tm)
  end
;

fun lift_fence mu_b mu_e pc hex =
  let
    val riscv_bmr_tm = ``riscv_bmr``; (* TODO *)
    val pc_word = mk_wordi (pc, 64)
    val pc_imm = gen_mk_Imm pc_word
    val pc_next_imm = gen_mk_Imm (mk_wordii ((Arbnum.toInt pc)+4, 64))
    val wi_end = mk_WI_end (mk_wordii (Arbnum.toInt mu_b, 64), mk_wordii (Arbnum.toInt mu_e, 64))
    val byte_instruction = get_byte_word_l hex
    val prog =
      mk_BirProgram_list (“:'a”, (* TODO *)
	[mk_bir_block_list (“:'a”, (* TODO *)
			    mk_BL_Address_HC (pc_imm, fromMLstring hex),
			    [mk_BStmt_Fence (get_fence_args hex)],
			    mk_BStmt_Jmp (mk_BLE_Label (mk_BL_Address pc_next_imm))
	)]
      )
    val lifted_tm =
      mk_bir_is_lifted_inst_prog (riscv_bmr_tm,
                                  pc_imm,
                                  wi_end,
                                  mk_pair (pc_word, byte_instruction),
                                  prog
      )
  in
    prove(lifted_tm, cheat)
  end
;


(* TODO
fun lift_atomic mu_b mu_e pc hex = 


;
*)

fun riscv_multicore_test_hex mu_b mu_e pc hex =
  if is_fence hex
  then (SOME (lift_fence mu_b mu_e pc hex),
        SOME (bir_inst_liftingLibTypes.BILED_msg "cheated with lifter theorem"),
        "Time not measured")
(* TODO
  else if is_atomic hex
  then lift_atomic hex
*)
  else riscv_test_hex mu_b mu_e pc hex
;


end
